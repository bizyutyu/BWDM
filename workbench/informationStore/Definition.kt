package com.github.korosuke613.bwdm.informationStore

import com.fujitsu.vdmj.tc.definitions.TCDefinition
import com.github.korosuke613.bwdm.Util
import com.github.korosuke613.bwdm.boundaryValueAnalysisUnit.BoundaryValueAnalyzer
import com.github.korosuke613.bwdm.ConditionSolver
import com.github.korosuke613.bwdm.informationStore.ConditionAndReturnValueList.ConditionAndReturnValue
import java.util.function.Consumer

abstract class Definition(val tcDefinition: TCDefinition) {
    private val ifConditionBodiesInCameForward: ArrayList<String> = ArrayList()

    // +でつながった変数の式
    var compositeParameters: ArrayList<String> = arrayListOf()

    protected var ifExpressionBody: String = ""

    var conditionAndReturnValueList: ConditionAndReturnValueList? = null

    /**
     * type of return value
     */
    abstract var returnValue: String

    /**
     * a parameter to ArrayList of HashMaps that is parsed each if-expression.
     * ArrayList of HashMap of parsed if-expr.
     */
    val ifConditions: HashMap<String, ArrayList<HashMap<String, String>>> = HashMap()

	// インスタンス変数の初期状態
	val initInstanceVariables: LinkedHashMap<String, String> = linkedMapOf()

    var name: String = tcDefinition.name.name

	// 境界値分析に用いる条件式のリスト
	val conditionsForBva: ArrayList<String> = ArrayList()

    // 仮引数と型のリスト
    val paramToTypeList: HashMap<String, String> = HashMap()

    // 仮引数のリスト
    val parameters: ArrayList<String> = ArrayList()

    // 引数の型リスト
    val argumentTypes: ArrayList<String> = ArrayList()

	// 入力値の条件式リスト(型の不変条件と事前条件)
	val inputConditions: ArrayList<String> = ArrayList()

	// 期待値の条件式リスト(クラス不変条件と事後条件)
	val outputConditions: ArrayList<String> = ArrayList()
	
    var ifElseExprSyntaxTree: IfElseExprSyntaxTree? = null
        protected set

    var isSetter: Boolean = false

    var isObjectSetter: Boolean = true 

    abstract fun setIfElseSyntaxTree()
    abstract fun parseIfConditions()
    abstract fun setTypeConditions()

	// outputConditionsの条件式を境界値分析できる形にしたものを生成する
	protected fun setOutputConditionsForBva() {

        conditionAndReturnValueList!!.conditionAndReturnValues.forEach(Consumer<ConditionAndReturnValue> { conditionAndReturnValue ->
			val outputConditionsForBva = ArrayList<String>(outputConditions)
			val conditions = conditionAndReturnValue.conditions
        	val bools = conditionAndReturnValue.bools
        	val execution = conditionAndReturnValue.returnStr!!

			var prerequisites = ""
			for (i in 0 until conditions.size) {
				prerequisites += " and "
				prerequisites += "(" + ConditionSolver.convertToBooleanCondition(conditions[i], bools[i]).removeEndParentheses() + ")"
			}
			inputConditions.forEach { ic ->
				prerequisites += " and "
				prerequisites += "(" + ic.removeEndParentheses() + ")"
			}
			prerequisites = prerequisites.removePrefix(" and ").removeSuffix(" and ")
			prerequisites = "[" + prerequisites + "]"
		})
	}

	// 型の制約条件を生成する
	protected fun generateTypeConditions(name: String, type: String): ArrayList<String> {
		val typeConditions: ArrayList<String> = ArrayList()
		when(type) {
			"int" -> {
				typeConditions.add("($name <= ${BoundaryValueAnalyzer.intMax})")
				typeConditions.add("($name >= ${BoundaryValueAnalyzer.intMin})")
			}
			"nat" -> {
				typeConditions.add("($name <= ${BoundaryValueAnalyzer.natMax})")
				typeConditions.add("($name >= ${BoundaryValueAnalyzer.natMin})")
			}
			"nat1" -> {
				typeConditions.add("($name <= ${BoundaryValueAnalyzer.nat1Max})")
				typeConditions.add("($name >= ${BoundaryValueAnalyzer.nat1Min})")
			}
		}

		return typeConditions
	}
}

fun String.replaceVariable(oldValue: String, newValue: String): String {
	var returnStr: String = ""
	val startRegex = Regex("""\(*${oldValue}\)*""")

	this.split(" ").forEach {
		if(startRegex.matches(it)) returnStr += it.replace(oldValue, newValue)
		else returnStr += it

		returnStr += " "
	}
	returnStr = returnStr.removeSuffix(" ")

	return returnStr
}

fun String.searchVariable(str: String): Boolean {
	val startRegex = Regex("""\(*${str}\)*""")
	this.split(" ").forEach {
		if(startRegex.matches(it)) return true
	}
	return false
}

fun String.alignParentheses(): String {
	val leftCount = this.split("(").size - 1
	val rightCount = this.split(")").size - 1

	if(leftCount > rightCount) {
		val returnLength = this.length - (leftCount - rightCount)
		return this.takeLast(returnLength)
	} else if(leftCount < rightCount) {
		val returnLength = this.length - (rightCount - leftCount)
		return this.take(returnLength)
	} else {
		return this
	}
}

// 全体を囲っている括弧を外す
fun String.removeEndParentheses(): String {
	// 先頭に括弧がない場合は何もしない
	if(this.substring(0, 1) != "(") return this

	val stringList = this.toCharArray()
	var parenthesesCount: Int = 1
	for (i in 1 until stringList.size-1){
		if(stringList[i] == '(') parenthesesCount++
		if(stringList[i] == ')') parenthesesCount--

		/*
		 * 末尾に到達する前にカウントが0になった場合，
		 * 全体を括弧で囲っていないため，何もしない
		 */
		if(parenthesesCount == 0) return this
	}

	// 先頭と末尾の括弧を外す
	return this.removePrefix("(").removeSuffix(")").removeEndParentheses()
}
