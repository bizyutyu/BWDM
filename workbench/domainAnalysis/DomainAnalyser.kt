package com.github.korosuke613.bwdm.domainAnalysis

import com.github.korosuke613.bwdm.Util
import com.github.korosuke613.bwdm.boundaryValueAnalysisUnit.ExpectedOutputDataGenerator
import com.github.korosuke613.bwdm.informationStore.ConditionAndReturnValueList
import com.github.korosuke613.bwdm.informationStore.Definition
import com.github.korosuke613.bwdm.informationStore.IfElseExprSyntaxTree
import com.github.korosuke613.bwdm.ConditionSolver
import com.github.korosuke613.bwdm.NotTypeException
import com.github.korosuke613.bwdm.removeEndParentheses
import com.microsoft.z3.ArithExpr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Status
import java.util.*
import kotlin.collections.ArrayList

class DomainAnalyser(private val definition: Definition) {
    val domains: ArrayList<DomainPoints> = ArrayList()
    val inputDataList: ArrayList<HashMap<String, Long>> = ArrayList()
    val expectedOutputDataGenerator: ExpectedOutputDataGenerator
    var expectedCount = 0

	private var usedPoint: String = "" // 使用されたポイントと被らないような条件式を記述する

    init {
        for (condition in definition.conditionAndReturnValueList!!.conditionAndReturnValues) {
            val domainPoints = DomainPoints(condition.returnStr.toString())
            generateOnPoints(domainPoints, condition)
            generateOffPoints(domainPoints)
            generateOutPoints(domainPoints, condition)
            generateInPoints(domainPoints, condition)
            domains.add(domainPoints)
        }
        createInputDataList()
 
        expectedOutputDataGenerator = ExpectedOutputDataGenerator(
                definition,
                Objects.requireNonNull<IfElseExprSyntaxTree>(definition.ifElseExprSyntaxTree).root,
                inputDataList
        )

    }

    private fun createInputDataList(){
        for(dp in domains){
            dp.onPoints.forEach { onPoint ->
                inputDataList.add(onPoint)
            }
            dp.offPoints.forEach { offPoint ->
                inputDataList.add(offPoint)
            }
            dp.inPoints.forEach { inPoint ->
                inputDataList.add(inPoint)
            }
            dp.outPoints.forEach { outPoint ->
                inputDataList.add(outPoint)
            }
        }
    }

    /**
     * dpにOnポイントを追加する.
     *
     * @args dp ドメインに対応したポイント群
     * @args carv if-then-else構造
     */
    private fun generateOnPoints(dp: DomainPoints, carv: ConditionAndReturnValueList.ConditionAndReturnValue) {
		val ifCondition = carv.conditions
		val bools: ArrayList<Boolean> = carv.bools

		for (i in 0 until ifCondition.size) {
			var allConditions: String = ","
			// ifCondition中の条件の1つだけ境界を取る
			for (j in 0 until ifCondition.size) {
				if(i == j) {
					val allConditions_ = allConditions
					allConditions = ""
					val boundaryConditions = ConditionSolver.convertToBoundaryConditionsByBoolean(ifCondition[j], bools[j])
					boundaryConditions.forEach { bc ->
						val replaceStr = " and (${bc.removeEndParentheses()}),"
						allConditions += allConditions_.replace(",", replaceStr)
					}
				} else {
					val booleanCondition = ConditionSolver.convertToBooleanCondition(ifCondition[j], bools[j])
					val replaceStr = " and (${booleanCondition.removeEndParentheses()}),"
					allConditions = allConditions.replace(",", replaceStr)
				}
			}

			allConditions.split(",").forEach { ac_ ->
				// 余分な文字列を削除する
				var ac = ac_.removePrefix(" and ")
				// 事前条件を追加する
				if(ac != "") {
					// 事前条件を追加する
					definition.inputConditions.forEach { ic ->
						ac = "(${ac.removeEndParentheses()}) and $ic"
					}

					// allConditionsを解いた結果をonPointsに追加する
					setPoints(dp.onPoints, ac)
				}
			}
		}
    }

    /**
     * dpにOffポイントを追加する.
     *
     * @args dp ドメインに対応したポイント群
     */
    private fun generateOffPoints(dp: DomainPoints) {
		dp.onPoints.forEach { onPoint ->
			onPoint.forEach { (param, value) ->
				var inputDataPlus = HashMap(onPoint)
				var inputDataMinus = HashMap(onPoint)

				inputDataPlus[param] = value + 1
				dp.offPoints.add(inputDataPlus)
				// 追加したポイントと被らないような条件式をusedPointに追加する
				addUsedPoint(inputDataPlus)

				inputDataMinus[param] = value - 1
				dp.offPoints.add(inputDataMinus)
				// 追加したポイントと被らないような条件式をusedPointに追加する
				addUsedPoint(inputDataMinus)
			}
        }
    }

    private fun generateOutPoints(dp: DomainPoints, carv: ConditionAndReturnValueList.ConditionAndReturnValue) {
		val ifCondition = carv.conditions
		val bools: ArrayList<Boolean> = carv.bools

		for (i in 0 until ifCondition.size) {
			var allConditions: String = ""
			// ifCondition中の条件の1つだけ反転させる
			for (j in 0 until ifCondition.size) {
				if(j != 0) allConditions += " and "

				allConditions += 
					if(i == j) { // i番目の条件式を反転させる
						ConditionSolver.convertToBooleanCondition(ifCondition[j], !bools[j])
					} else {
						ConditionSolver.convertToBooleanCondition(ifCondition[j], bools[j])
					}
			}

			// 事前条件を追加する
			definition.inputConditions.forEach { ic ->
				allConditions = "(${allConditions.removeEndParentheses()}) and $ic"
			}

			// allConditionsを解いた結果をonPointsに追加する
			setPoints(dp.outPoints, allConditions)
		}
    }

    /**
     * dpにInポイントを追加する.
     *
     * @args dp ドメインに対応したポイント群
     * @args carv if-then-else構造
     */
    private fun generateInPoints(dp: DomainPoints, carv: ConditionAndReturnValueList.ConditionAndReturnValue) {
        val ifCondition = carv.conditions
		val bools: ArrayList<Boolean> = carv.bools

		var allConditions = ""
		for (i in 0 until ifCondition.size) { 
			if (i != 0) allConditions += " and "
			allConditions += ConditionSolver.convertToBooleanCondition(ifCondition[i], bools[i])
		}
		// 事前条件を追加する
		definition.inputConditions.forEach { iCondition ->
			allConditions += " and "
			allConditions += iCondition
		}

		// allConditionsを解いた結果をinPointsに追加する
		setPoints(dp.inPoints, allConditions)
	}

    /**
     * 条件式を解き，与えられたポイントのリストに追加する.
	 * 既に生成されているポイントと被らないように生成するが，
	 * 不可能な場合はその制約はない.
     *
     * @args points いずれかのポイントのリスト
     * @args allConditions 解きたい条件式
     */
	private fun setPoints(points: ArrayList<HashMap<String, Long>>, allConditions: String){
		val paramToTypeList = definition.paramToTypeList
		// 既に追加しているポイントと被らない条件を追加してポイントを生成する
		val inputData: HashMap<String, Long> = HashMap()
		val allConditionsAndUnusedPoint =
			if (usedPoint != "") {
				"$allConditions and (${usedPoint.removePrefix(" and ").removeEndParentheses()})"
			} else {
				allConditions
			}
		var values = ConditionSolver.solveCondition(allConditionsAndUnusedPoint, paramToTypeList)
		// allConditionsAndUnusedPointを満たす入力がある場合
		if(!values.containsValue("NO_SOLUTION")) {
			paramToTypeList.forEach{ (param, type) ->
				if (values[param]!!.toLongOrNull() != null) {
					inputData[param] = values[param]!!.toLong()
				} else {
					// 値が自由の場合は型ごとのデフォルト値を入れる
					inputData[param] = when(type) {
						"nat" -> ConditionSolver.natDefault
						"nat1" -> ConditionSolver.nat1Default
						"int" -> ConditionSolver.intDefault
						else -> throw NotTypeException("type \"$type\" is not supported")
					}
				}
			}
		} else { // ポイントがない場合usedPointの制約をなくして再度ポイントを生成する
			values = ConditionSolver.solveCondition(allConditions, paramToTypeList)
			// allConditionsを満たす入力がある場合
			if(!values.containsValue("NO_SOLUTION")) {
				paramToTypeList.forEach{ (param, type) ->
					if (values[param]!!.toLongOrNull() != null) {
						inputData[param] = values[param]!!.toLong()
					} else {
						// 値が自由の場合は型ごとのデフォルト値を入れる
						inputData[param] = when(type) {
							"nat" -> ConditionSolver.natDefault
							"nat1" -> ConditionSolver.nat1Default
							"int" -> ConditionSolver.intDefault
							else -> throw NotTypeException("type \"$type\" is not supported")
						}
					}
				}
			}
		}

		if(!inputData.isEmpty()) {
			points.add(inputData)
			// 追加したポイントと被らないような条件式をusedPointに追加する
			addUsedPoint(inputData)
		}
	}

    val allTestcasesByDa: String
        get() {
            val buf = StringBuilder()
            expectedCount = 0
			/*
			 * createInputDataList()でinputDataListに追加したポイント順に，
			 * addResultBuf()を実行する
			 */
            for(dp in domains) {
                buf.append("- ${dp.name}\n")
                addResultBuf(buf, dp.onPoints, "Onポイント")
                addResultBuf(buf, dp.offPoints, "Offポイント")
                addResultBuf(buf, dp.inPoints, "Inポイント")
                addResultBuf(buf, dp.outPoints, "Outポイント")
                buf.append("\n")
            }
            return buf.toString()
        }

    private fun addResultBuf(buf: StringBuilder, points: ArrayList<HashMap<String, Long>>, title: String){
        var i = 0
        buf.append("-- $title\n")
        points.forEach { point ->
            buf.append("No.").append(i + 1).append(" : ")
            for (prm in definition.parameters) {
                buf.append(point[prm]).append(" ")
            }
            buf.append("-> ").append(expectedOutputDataGenerator.expectedOutputDataList[expectedCount]).append("\n")
            expectedCount++
            i++
        }
    }

	private fun addUsedPoint(inputData: HashMap<String, Long>) {
		var str: String = ""
		inputData.forEach { (param, value) ->
			str += " or ($param <> $value)"
		}
		usedPoint += " and (${str.removePrefix(" or ")})"
	}
}
