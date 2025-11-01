package com.github.korosuke613.bwdm.symbolicExecutionUnit

import com.github.korosuke613.bwdm.Analyzer
import com.github.korosuke613.bwdm.Util
import com.github.korosuke613.bwdm.informationStore.ConditionAndReturnValueList.ConditionAndReturnValue
import com.github.korosuke613.bwdm.informationStore.Definition
import com.github.korosuke613.bwdm.boundaryValueAnalysisUnit.BoundaryValueAnalyzer
import com.microsoft.z3.*
import java.util.*
import java.util.function.Consumer
import com.github.korosuke613.bwdm.ConditionSolver
import com.github.korosuke613.bwdm.NotTypeException
import com.github.korosuke613.bwdm.removeEndParentheses

class SymbolicExecutioner
(definition: Definition) : Analyzer<String>(definition) {

    private val expectedOutputDataList: ArrayList<String> = ArrayList()

    init {
        val conditionAndReturnValueList = definition.conditionAndReturnValueList

        conditionAndReturnValueList!!.conditionAndReturnValues.forEach(Consumer<ConditionAndReturnValue> {
			this.doSymbolicExecution(it)
			// 境界値を取らない記号実行
			// this.doSymbolicExecutionExisting(it) 
        })
    }

	private fun doSymbolicExecution(conditionAndReturnValue: ConditionAndReturnValue){
        val conditions = conditionAndReturnValue.conditions
        val bools = conditionAndReturnValue.bools
        val execution = conditionAndReturnValue.returnStr!!
		val returnType = definition.returnValue // 戻り値の型
		val paramToTypeList = definition.paramToTypeList

		var inputConditionsAll = ""
		for(i in 0 until definition.inputConditions.size) {
			if(i != 0) inputConditionsAll += " and "
			inputConditionsAll += definition.inputConditions[i]
		}

		run {
			/* 
			 * まず全ての条件式を境界を取る式に変換して，それら全てを満たす入力を求める.
			 * 入力が取れない場合はネストが一番浅い条件式は元の条件式にして再度入力を求める.
			 * それでも入力が取れない場合は次にネストが浅い条件式も元の条件式にして再度入力を求める.
			 * 以上を全ての条件式が元の条件式になるまで繰り返す
			 */
			for (i in 0 until conditions.size + 1) {
				var allConditions: String = ","

				// 境界を取る条件式をallConditionsに追加する
				for (j in 0 until conditions.size - i) {
					val allConditions_ = allConditions
					allConditions = ""
					val boundaryConditions = ConditionSolver.convertToBoundaryConditionsByBoolean(conditions[j], bools[j])
					boundaryConditions.forEach { boundaryCondition ->
						val replaceStr = " and (${boundaryCondition.removeEndParentheses()}),"
						allConditions += allConditions_.replace(",", replaceStr)
					}
				}

				// 境界を取らない条件式をallConditionsに追加する
				for (k in conditions.size - i until conditions.size) {
					val condition_ = ConditionSolver.convertToBooleanCondition(conditions[k], bools[k])
					val replaceStr: String = " and (${condition_.removeEndParentheses()}),"
					allConditions = allConditions.replace(",", replaceStr)
				}

				var returnFlag: Boolean = false // 一つでも入力データが決定したらreturn@runをする
				allConditions.split(",").forEach { ac_ ->
					// 余分な文字列を削除する
					var ac = ac_.removePrefix(" and ")

					if(ac != "") {
						// 事前条件を追加する
						definition.inputConditions.forEach { ic ->
							ac = "(${ac.removeEndParentheses()}) and $ic"
						}
						val values = ConditionSolver.solveCondition(ac, paramToTypeList)

						if(!values.containsValue("NO_SOLUTION")) {
							val inputData = HashMap<String, String>()
							paramToTypeList.forEach{ (param, type) ->
								if (values[param]!!.toLongOrNull() != null) {
									inputData[param] = values[param]!!
								} else {
									// 値が自由の場合は型ごとのデフォルト値を入れる
									inputData[param] = when(type) {
										"nat" -> ConditionSolver.natDefault.toString()
										"nat1" -> ConditionSolver.nat1Default.toString()
										"int" -> ConditionSolver.intDefault.toString()
										else -> throw NotTypeException("type \"$type\" is not supported")
									}
								}
							}
            				inputDataList.add(inputData)
							val inputData_: HashMap<String, Long> = HashMap()
							inputData.forEach { (key, value) -> inputData_[key] = value.toLong()}
							//val returnStr = generateReturnStr(execution, returnType, inputData_)
							val returnStr = execution // 仮
            				expectedOutputDataList.add(returnStr!!)
							returnFlag = true
						}
					}
				}
				if(returnFlag) return@run
			}
		}
	}

	// 境界値は取らない記号実行
	private fun doSymbolicExecutionExisting(conditionAndReturnValue: ConditionAndReturnValue){
        val conditions = conditionAndReturnValue.conditions
        val bools = conditionAndReturnValue.bools
        val execution = conditionAndReturnValue.returnStr!!
		val returnType = definition.returnValue // 戻り値の型
		val paramToTypeList = definition.paramToTypeList

		var allConditions: String = ConditionSolver.convertToBooleanCondition(conditions[0], bools[0])
		for (i in 1 until conditions.size) {
			allConditions += " and "
			allConditions += ConditionSolver.convertToBooleanCondition(conditions[i], bools[i])
		}	

		// 事前条件を追加する
		definition.inputConditions.forEach { ic ->
			allConditions += " and "
			allConditions += ic
		}

		val values = ConditionSolver.solveCondition(allConditions, paramToTypeList)

		if(!values.containsValue("NO_SOLUTION")) {
			val inputData = HashMap<String, String>()
			paramToTypeList.forEach{ (param, type) ->
				if (values[param]!!.toLongOrNull() != null) {
					inputData[param] = values[param]!!
				} else {
					// 値が自由の場合は型ごとのデフォルト値を入れる
					inputData[param] = when(type) {
						"nat" -> ConditionSolver.natDefault.toString()
						"nat1" -> ConditionSolver.nat1Default.toString()
						"int" -> ConditionSolver.intDefault.toString()
						else -> throw NotTypeException("type \"$type\" is not supported")
					}
				}
			}

			inputDataList.add(inputData)
			val inputData_: HashMap<String, Long> = HashMap()
			inputData.forEach { (key, value) -> inputData_[key] = value.toLong()}
			//val returnStr = generateReturnStr(execution, returnType, inputData_)
			val returnStr = execution
			expectedOutputDataList.add(returnStr!!)
		}
	}

	// expectedOutputDataListのゲッタ
    fun getExpectedOutputDataList(): ArrayList<String> {
        return expectedOutputDataList
    }

}
