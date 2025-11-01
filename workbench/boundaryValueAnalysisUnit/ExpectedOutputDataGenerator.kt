package com.github.korosuke613.bwdm.boundaryValueAnalysisUnit

import com.github.korosuke613.bwdm.Util
import com.github.korosuke613.bwdm.informationStore.Definition
import com.github.korosuke613.bwdm.informationStore.IfNode
import com.github.korosuke613.bwdm.informationStore.Node
import com.github.korosuke613.bwdm.ConditionSolver
//import com.github.korosuke613.bwdm.replaceVariable
//import com.github.korosuke613.bwdm.removeEndParentheses
import java.util.*

class ExpectedOutputDataGenerator
constructor(private val definition: Definition,
            _root: IfNode,
            _inputDataList: ArrayList<HashMap<String, Long>>) {
    internal val expectedOutputDataList: ArrayList<String> = ArrayList()

    init {
        //inputData:seq of HashMapの各要素に入力データを挿入
		_inputDataList.forEach { inputData -> extractExpectedOutputDataRecursively(_root, inputData)}
    }

    //条件式は両辺のうち片方のみ変数が含まれているという制約付き
    private fun extractExpectedOutputDataRecursively(_node: Node, _inputData: HashMap<String, Long>) {

        if (_node.getIsIfNode()) { //IfNodeである場合 // 条件式のパース
			// 条件式をconditionにセット
			var condition = _node.conditionOrReturnStr
			// condition中の引数を入力データに置き換える
			_inputData.forEach { (argumentName, value) ->
				condition = condition.replaceVariable(argumentName, value.toString())
			}

			if(ConditionSolver.evaluateCondition(condition)) {
				extractExpectedOutputDataRecursively(Objects.requireNonNull<Node>((_node as IfNode).conditionTrueNode), _inputData)
			} else { //判定結果がFalseならばifNodeのfalseNodeに進んで再帰
				extractExpectedOutputDataRecursively( Objects.requireNonNull<Node>((_node as IfNode).conditionFalseNode), _inputData)
			}
        } else { //returnNodeである場合
            val execution = _node.conditionOrReturnStr // 実行する処理
			val returnType = definition.returnValue // 戻り値の型
			val expectedOutputData = generateExpectedOutputData(execution, returnType, _inputData)
            expectedOutputDataList.add(expectedOutputData)
        }
    }

	private fun generateExpectedOutputData(execution: String, returnType: String, inputData: HashMap<String, Long>): String {
		var outputData: String = "-"

		var inputFlag = false
		val falseInputConditions: ArrayList<String> = ArrayList()
		definition.inputConditions.forEach { ic_ ->
			var ic = ic_
			// ic のインスタンス変数を置換する
			definition.initInstanceVariables.forEach { (key, value) ->
				ic = ic.replaceVariable(key, value)
			}
			// ic の仮引数を置換する
			inputData.forEach { (key, value) ->
				ic = ic.replaceVariable(key, value.toString())
			}
			if(!ConditionSolver.evaluateCondition(ic)) { // icが偽の場合
				inputFlag = true
				falseInputConditions.add(ic_) // 置換する前の式を追加
			}
		}
		if(inputFlag) { // 事前条件を充足しない場合"Input Error"を返す
			outputData = "Input Error"
			outputData += " (FAILED: CONDITION"
			falseInputConditions.forEach {
				outputData = outputData.replace("CONDITION", it.removeEndParentheses())
				outputData += ", CONDITION"
			}
			outputData = outputData.removeSuffix(", CONDITION")
			outputData += ")"
			return outputData
		}
		
		val objectState = HashMap(definition.initInstanceVariables) // 操作後のインスタンス変数
	
		// 全体が""で囲われてるときは文字列なのでそのまま出力（関数定義を想定）
		if(execution.startsWith("\"") && execution.endsWith("\"")) return execution

		if(Regex("""return\s\(.*\)""").matches(execution)) { // return ("出力文字列")の時は出力部分だけ抽出する（操作定義を想定）
			var execution_ =  execution.removePrefix("return (").removeSuffix(")")
			outputData = 
				if(execution_.toIntOrNull() == null) { // 計算する必要がある場合
					// execution_ のインスタンス変数を置換する
					definition.initInstanceVariables.forEach { (key, value) ->
						execution_ = execution_.replaceVariable(key, value)
					}
					// execution_ の仮引数を置換する
					inputData.forEach { (key, value) ->
						execution_ = execution_.replaceVariable(key, value.toString())
					}
					ConditionSolver.calculateExpression(execution_)
				} else { // 計算する必要がない場合
					execution_
				}
		} else if (!execution.contains(":=")) { // 出力処理のみ場合（関数定義を想定）
			outputData =
				if(execution.toIntOrNull() == null) { // 計算する必要がある場合
					var execution_ =  execution
					// execution_ のインスタンス変数を置換する
					definition.initInstanceVariables.forEach { (key, value) ->
						execution_ = execution_.replaceVariable(key, value)
					}
					// execution_ の仮引数を置換する
					inputData.forEach { (key, value) ->
						execution_ = execution_.replaceVariable(key, value.toString())
					}
					ConditionSolver.calculateExpression(execution_)
				} else { // 計算する必要がない場合
					execution
				}
		} else { // 戻り値以外の処理もある場合
			execution.removeEndParentheses().split(";").forEach { e ->
				if(e.contains(":=")){
					val indexOfOperator = e.indexOf(":=")
					val instance = e.substring(0, indexOfOperator-1)
					var expression = e.substring(indexOfOperator+3)

					// expression のインスタンス変数を置換する
					definition.initInstanceVariables.forEach { (key, value) ->
						expression = expression.replaceVariable(key, value)
					}
					// expression の仮引数を置換する
					inputData.forEach { (key, value) ->
						expression = expression.replaceVariable(key, value.toString())
					}
					objectState[instance] = 
						if(expression.toIntOrNull() == null) { // 計算する必要がある場合
							ConditionSolver.calculateExpression(expression)
						} else { // 計算する必要がない場合
							expression
						}

				} else if(e.startsWith("return (")){
					var returnExpression = e.removePrefix("return (").removeSuffix(")") // 戻り値の式を抽出
					// returnExpression のインスタンス変数を置換する
					objectState.forEach { (key, value) ->
						returnExpression = returnExpression.replaceVariable(key, value)
					}
					// returnExpression の仮引数を置換する
					inputData.forEach { (key, value) ->
						returnExpression = returnExpression.replaceVariable(key, value.toString())
					}
					outputData = 
						if(returnExpression.toIntOrNull() == null) { // 計算する必要がある場合
							ConditionSolver.calculateExpression(returnExpression)
						} else { // 計算する必要がない場合
							returnExpression
						}
				}
			}
		}

		var outputFlag = false
		val falseOutputConditions: ArrayList<String> = ArrayList()
		definition.outputConditions.forEach { oc_ ->
			var oc = oc_
			// oc のRESULTを置換する
			oc = oc.replaceVariable("RESULT", outputData)
			// oc のインスタンス変数を置換する
			objectState.forEach { (key, value) ->
				oc = oc.replaceVariable(key, value)
			}
			// oc の仮引数を置換する
			inputData.forEach { (key, value) ->
				oc = oc.replaceVariable(key, value.toString())
			}
			if(!ConditionSolver.evaluateCondition(oc)) { // ocが偽の場合
				outputFlag = true
				falseOutputConditions.add(oc_) // 置換する前の式を追加
			}
		}
		if(outputFlag) { // 事後条件を充足しない場合"Failure"を返す
			outputData = "Failure"
			outputData += " (FAILED: CONDITION"
			falseOutputConditions.forEach {
				outputData = outputData.replace("CONDITION", it.removeEndParentheses())
				outputData += ", CONDITION"
			}
			outputData = outputData.removeSuffix(", CONDITION")
			outputData += ")"
			return outputData
		}
	
		return outputData
	}


}

// 変数を置き換える(完全一致した単語のみ置き換える)
// 例えば式中の変数aをAに置換する際に，(data = a) → (dAtA = A)となることを防ぐための拡張関数
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
	return this.removePrefix("(").removeSuffix(")")
}
