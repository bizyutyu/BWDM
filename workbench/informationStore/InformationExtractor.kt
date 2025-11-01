package com.github.korosuke613.bwdm.informationStore

import com.fujitsu.vdmj.ast.definitions.ASTDefinition
import com.fujitsu.vdmj.lex.Dialect
import com.fujitsu.vdmj.lex.LexException
import com.fujitsu.vdmj.lex.LexTokenReader
import com.fujitsu.vdmj.mapper.ClassMapper
import com.fujitsu.vdmj.syntax.DefinitionReader
import com.fujitsu.vdmj.syntax.ParserException
import com.fujitsu.vdmj.tc.definitions.*
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
    val constantValues: LinkedHashMap<String, TCValueDefinition> = LinkedHashMap()
    val instanceVariables: LinkedHashMap<String, TCInstanceVariableDefinition> = LinkedHashMap()
    val explicitOperations: LinkedHashMap<String, OperationDefinition> = LinkedHashMap()
    val explicitFunctions: LinkedHashMap<String, FunctionDefinition> = LinkedHashMap()
    val types: LinkedHashMap<String, TCTypeDefinition> = LinkedHashMap()
    var invariant: String = ""

    init {
        val vdmFile = File(vdmFilePath)
        val lexer = LexTokenReader(vdmFile, Dialect.VDM_PP)
        val parser = DefinitionReader(lexer)
        val astDefinitions = parser.readDefinitions()

        if (astDefinitions.size == 0){
            // VDM++のシンタックスエラーを例外で出す
            // number:2013はwarningレベルなので除外
            val errors = parser.errors.filter { it.number != 2013 }
            throw ParserException(errors[0].number, errors[0].message, errors[0].location, 0)
        }

        astDefinitions.forEach { astDefinition: ASTDefinition ->
            if (astDefinition.kind() == "value") {
                lateinit var tcValueDefinition: TCValueDefinition
                try {
                    tcValueDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCValueDefinition>(astDefinition)
                } catch (e: Exception) {
                    e.printStackTrace()
                }
                constantValues[tcValueDefinition.pattern.toString()] = tcValueDefinition
            }
            if (astDefinition.kind() == "instance variable") {
                lateinit var tcInstanceVariableDefinition: TCInstanceVariableDefinition
                try {
                    tcInstanceVariableDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCInstanceVariableDefinition>(astDefinition)
                } catch (e: Exception) {
                    e.printStackTrace()
                }
                instanceVariables[tcInstanceVariableDefinition.name.toString()] = tcInstanceVariableDefinition
            }
            if (astDefinition.kind() == "explicit operation") {
                lateinit var tcExplicitOperationDefinition: TCExplicitOperationDefinition
                try {
                    tcExplicitOperationDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCExplicitOperationDefinition>(astDefinition)
                } catch (e: Exception) {
                    e.printStackTrace()
                }
                val operation = OperationDefinition(tcExplicitOperationDefinition, instanceVariables, constantValues, types, invariant)
                explicitOperations[operation.name] = operation
            }
            if (astDefinition.kind() == "explicit function") {
                lateinit var tcFunctionDefinition: TCExplicitFunctionDefinition
                try {
                    tcFunctionDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCExplicitFunctionDefinition>(astDefinition)
                } catch (e: Exception) {
                    e.printStackTrace()
                }
                val function = FunctionDefinition(tcFunctionDefinition, constantValues, types)
                explicitFunctions[function.name] = function
            }
			if (astDefinition.kind() == "type") {
				lateinit var tcTypeDefinition: TCTypeDefinition
                try {
                    tcTypeDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCTypeDefinition>(astDefinition)
                } catch (e: Exception) {
                    e.printStackTrace()
                }
				types[tcTypeDefinition.type.toString()] = tcTypeDefinition
			}
			if (astDefinition.kind() == "invariant") {
				lateinit var tcInvariantDefinition: TCClassInvariantDefinition
				try {
					tcInvariantDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert<TCClassInvariantDefinition>(astDefinition)
				} catch (e: Exception) {
					e.printStackTrace()
				}
				invariant = tcInvariantDefinition.expression.toString()
			}
        }
    }/* Initializing fields*/
}
