package com.github.korosuke613.bwdm.informationStore

import com.github.korosuke613.bwdm.Util
import com.fujitsu.vdmj.ast.definitions.ASTDefinition
import com.fujitsu.vdmj.lex.Dialect
import com.fujitsu.vdmj.lex.LexException
import com.fujitsu.vdmj.lex.LexTokenReader
import com.fujitsu.vdmj.mapper.ClassMapper
import com.fujitsu.vdmj.syntax.DefinitionReader
import com.fujitsu.vdmj.syntax.ParserException
import com.fujitsu.vdmj.tc.definitions.TCDefinition
import com.fujitsu.vdmj.tc.definitions.TCExplicitFunctionDefinition
import com.fujitsu.vdmj.tc.definitions.TCExplicitOperationDefinition
import com.fujitsu.vdmj.tc.patterns.TCIdentifierPattern
import com.fujitsu.vdmj.tc.definitions.TCInstanceVariableDefinition
import com.fujitsu.vdmj.tc.lex.TCNameToken
import java.io.File
import java.io.IOException


/**
 * information what got from VDM++ specification file by syntax analyse with VDMJ
 */
class InformationExtractor


@Throws(LexException::class, ParserException::class, IOException::class)
constructor(val vdmFilePath: String) {

    /**
     * a parameter to ArrayList of if-conditions.
     * ArrayList of ifConditions of each parameter.
     */
    //private val ifConditionBodies: HashMap<String, ArrayList<HashMap<String, String>>>
    private var ifExpressionBody: String? = null
    val ifConditionBodiesInCameForward: ArrayList<String>

    val conditionAndReturnValueList: ConditionAndReturnValueList
    val argumentTypes: ArrayList<String> //int, nat, nat1
    val parameters: ArrayList<String> //a, b, c
    lateinit var compositeParameters: ArrayList<String>
    val instanceVariables: LinkedHashMap<String, TCInstanceVariableDefinition> = LinkedHashMap()
    val explicitOperations: LinkedHashMap<String, TCExplicitOperationDefinition> = LinkedHashMap()

    /**
     * type of return value
     */
    var returnValue: String? = null
        private set

    var ifElseExprSyntaxTree: IfElseExprSyntaxTree? = null
        private set

    var functionName: String? = null
        private set


    /**
     * a parameter to ArrayList of HashMaps that is parsed each if-expression.
     * ArrayList of HashMap of parsed if-expr.
     */
    val ifConditions: HashMap<String, ArrayList<HashMap<String, String>>>

    init {
        val vdmFile = File(vdmFilePath)

        // variableName = init; example
        argumentTypes = ArrayList() //int, nat, nat1

        //parameter information
        //a*b*c
        parameters = ArrayList() //a, b, c

        ifExpressionBody = ""
        //ifConditionBodies = HashMap()
        ifConditionBodiesInCameForward = ArrayList()
        ifConditions = HashMap()
        /*Done initializing fields*/

        val lexer = LexTokenReader(vdmFile, Dialect.VDM_PP)
        val parser = DefinitionReader(lexer)
        val astDefinitions = parser.readDefinitions()

        astDefinitions.forEach { astDefinition: ASTDefinition ->
            if(astDefinition.kind() == "instance variable"){
                lateinit var tcInstanceVariableDefinition: TCInstanceVariableDefinition
                try {
                    tcInstanceVariableDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCInstanceVariableDefinition>(astDefinition)
                } catch (e: Exception) {
                    e.printStackTrace()
                }
                instanceVariables[tcInstanceVariableDefinition.name.toString()] = tcInstanceVariableDefinition
            }
            if (astDefinition.kind() == "explicit operation"){
                lateinit var tcExplicitOperationDefinition: TCExplicitOperationDefinition
                try {
                    tcExplicitOperationDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCExplicitOperationDefinition>(astDefinition)
                }catch (e: Exception) {
                    e.printStackTrace()
                }
                explicitOperations[tcExplicitOperationDefinition.name.toString()] = tcExplicitOperationDefinition
            }
            if (astDefinition.kind() == "explicit function") {
                var tcFunctionDefinition: TCExplicitFunctionDefinition? = null
                try {
                    tcFunctionDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCExplicitFunctionDefinition>(astDefinition)
                } catch (e: Exception) {
                    e.printStackTrace()
                }

                assert(tcFunctionDefinition != null)
                functionName = tcFunctionDefinition!!.name.name
                returnValue = tcFunctionDefinition.type.result.toString()
                val tcFunctionType = tcFunctionDefinition.type
                val tmpArgumentTypes = tcFunctionType.parameters
                val tcExpression = tcFunctionDefinition.body
                ifExpressionBody = tcExpression.toString()
                tmpArgumentTypes.forEach { e -> argumentTypes.add(e.toString()) }

                try {
                    ifElseExprSyntaxTree = IfElseExprSyntaxTree(ifExpressionBody!!)
                } catch (e: ParserException) {
                    e.printStackTrace()
                } catch (e: LexException) {
                    e.printStackTrace()
                } catch (e: IOException) {
                    e.printStackTrace()
                }

                //parsing for parameters
                val tcPatternListList = tcFunctionDefinition.paramPatternList
                val tcPatternList = tcPatternListList.firstElement()
                for (aTcPatternList in tcPatternList) {
                    val tcIdentifierPattern = aTcPatternList as TCIdentifierPattern
                    val parameter = tcIdentifierPattern.toString()
                    parameters.add(parameter)
                }
                parseIfConditions()
            }
        }

        ifElseExprSyntaxTree = IfElseExprSyntaxTree(ifExpressionBody!!)

        conditionAndReturnValueList = ConditionAndReturnValueList(ifElseExprSyntaxTree!!.root)
    }/* Initializing fields*/

    private fun parseIfConditions() {
        val ifElses = ifElseExprSyntaxTree!!.ifElses

        compositeParameters = ArrayList(parameters)

        for (i in ifElses.indices) {
            var element = ifElses[i]
            if (element == "if") {
                element = ifElses[i + 1]
                ifConditionBodiesInCameForward.add(element)
                val operator = Util.getOperator(element)
                val indexOfoperator = element.indexOf(operator)
                val left = element.substring(0, indexOfoperator)
                if (Util.getOperator(left) == "+") {
                    compositeParameters.add(left)
                }
            }
        }

        //initializing of collection instances of each parameter
        compositeParameters.forEach { s ->
            //ifConditionBodies[s] = ArrayList()
            ifConditions[s] = ArrayList()
        }

        //parsing of each if-condition, and store in ifConditions
        ifConditionBodiesInCameForward.forEach { condition ->
            val operator = Util.getOperator(condition)
            val indexOfoperator = condition.indexOf(operator)
            val left = condition.substring(0, indexOfoperator)
            compositeParameters.forEach { parameter ->
                if (left == parameter) {
                    parse(condition, parameter)
                }
            }
        }
    }

    private fun parse(condition: String, parameter: String) {
        //var al = ifConditionBodies[parameter]
        //al!!.add(condition)

        val operator = Util.getOperator(condition)
        val indexOfoperator = condition.indexOf(operator)
        val hm = HashMap<String, String>()
        hm["left"] = condition.substring(0, indexOfoperator)
        hm["operator"] = operator

        val conditionParameter = parameter


        val al = ifConditions[conditionParameter]
        al!!.add(hm)
        //right-hand and surplus need branch depending on mod or other.
        modJudge(condition, operator, indexOfoperator, hm)

    }

    companion object {
        fun modJudge(condition: String, operator: String, indexOfoperator: Int, hm: HashMap<String, String>) {
            if (operator == "mod") {
                val indexOfEqual = condition.indexOf("=")
                hm["right"] = condition.substring(indexOfoperator + 3, indexOfEqual)
                hm["surplus"] = condition.substring(indexOfEqual + 1)
            } else {
                hm["right"] = condition.substring(indexOfoperator + operator.length)
            }
        }
    }
}
