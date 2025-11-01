package com.github.korosuke613.bwdm

import com.github.korosuke613.bwdm.Util
import com.microsoft.z3.*

class ConditionSolver {
    companion object {
		// 変数に対する制約がない場合の値
		internal const val natDefault: Long = 0 
		internal const val nat1Default: Long = 1
		internal const val intDefault: Long = 0

		private val exprList: ArrayList<BoolExpr> = ArrayList()
    	private val ctx: Context = Context()

    	/**
		 * 与えられた条件式を満たす各変数のパラメータを求める.
		 *
		 * @args condition 条件式
		 * @args paramToTypeList 変数と型のリスト
		 * @Return 各変数のパラメータ（変数に対して制約がない場合）
		 */
		fun solveCondition(condition: String, paramToTypeList: HashMap<String, String>): HashMap<String, String> {
        	var conditionUnion = ctx.mkBool(java.lang.Boolean.TRUE) // BoolExpr型に直したcondition（単位元としてTRUEの式で初期化する）
			var expr: BoolExpr? // 論理式
			exprList.clear() // div式のリストを空にする

			// conditionをBoolExpr型に変換してconditionUnionに追加する
			expr = convertBoolExpr(condition)
			conditionUnion = ctx.mkAnd(conditionUnion, expr)

			// 型ごとの制約条件をconditionUnionに追加する
			paramToTypeList.forEach { (parameter, argumentType) ->
				// conditionにparameterが含まれてる場合のみ，制約条件を追加する
				val regex = Regex("""(\s|\()$parameter(\s|\))""")
				if (regex.containsMatchIn(condition)){
					expr = when(argumentType){
						"nat" -> ctx.mkGe(ctx.mkIntConst(parameter), ctx.mkInt(0))
						"nat1" -> ctx.mkGt(ctx.mkIntConst(parameter), ctx.mkInt(0))
						else -> null
					}
					if(expr != null) conditionUnion = ctx.mkAnd(conditionUnion, expr)
				}
			}

			// exprListの条件をconditionUnionに追加する
			exprList.forEach { expr_ ->
				conditionUnion = ctx.mkAnd(conditionUnion, expr_)
			}

    		val solver = ctx.mkSolver() // ソルバーを生成
			solver.add(conditionUnion)

			val values: HashMap<String, String> = HashMap() // SMTソルバーが求めた各変数のパラメータを格納するリスト
			if(solver.check() == Status.SATISFIABLE) {
				val m = solver.model
				paramToTypeList.forEach { (parameter, argumentType) ->
					val value = m.evaluate(ctx.mkIntConst(parameter), false).toString()
					values[parameter] = value
				}
			} else {
				// 解がない場合は"NO_SOLUTION"を格納する
				paramToTypeList.forEach { (parameter, argumentType) ->
					values[parameter] = "NO_SOLUTION"
				}
			}
			return values
		}

    	/**
		 * 与えられた条件式を評価する.
		 *
		 * @args condition 条件式
		 * @Return 評価結果
		 */
		fun evaluateCondition(condition: String): Boolean {
			var result: BoolExpr = ctx.mkBoolConst(condition.replace(" ", ""))
			exprList.clear() // div式のリストを空にする

			var conditionUnion = convertBoolExpr(condition)
			// resultとconditionUnionが同値
			conditionUnion = ctx.mkIff(result, conditionUnion)

			exprList.forEach { expr_ ->
				conditionUnion = ctx.mkAnd(conditionUnion, expr_)
			}


    		val solver = ctx.mkSolver() // ソルバーを生成
			solver.add(conditionUnion)

			if(solver.check() == Status.SATISFIABLE) {
				val m = solver.model
				val bool = m.evaluate(result, false).toString()
				return if (bool == "true") true else false
			} else {
				//throw NotSolveException("\"$condition\" not evaluated")
				return false
			}
		}

    	/**
		 * 与えられた演算式を計算する.
		 *
		 * @args expression 演算式
		 * @Return 計算結果
		 */
		fun calculateExpression(expression: String): String {
			var result: IntExpr = ctx.mkIntConst("RESULT(" + expression.replace(" ", "") + ")")
			exprList.clear() // div式のリストを空にする

			var arithExpression = convertArithExpr(expression)
			// resultとconditionUnionが同値
			var conditionUnion = ctx.mkEq(result, arithExpression)

			exprList.forEach { expr_ ->
				conditionUnion = ctx.mkAnd(conditionUnion, expr_)
			}


    		val solver = ctx.mkSolver() // ソルバーを生成
			solver.add(conditionUnion)

			if(solver.check() == Status.SATISFIABLE) {
				val m = solver.model
				val resultStr = m.evaluate(result, false).toString()
				return resultStr
			} else {
				throw NotSolveException("\"$expression\" not evaluated")
			}
		}

    	/**
		 * 与えられた条件式をBoolExpr型に変換する.
		 *
		 * @args condition_ 条件式
		 * @Return BoolExpr型に変換したcondition
		 */
		private fun convertBoolExpr(condition_: String): BoolExpr? {
			val condition = condition_.removeEndParentheses()
			val indexOfLeftTail = getOperand(condition)
			val indexOfOperatorTail = getOperand(condition, indexOfLeftTail + 2)
			
			val leftOperand = condition.substring(0, indexOfLeftTail)
			val logicalOperator = condition.substring(indexOfLeftTail + 1, indexOfOperatorTail)
			val rightOperand = condition.substring(indexOfOperatorTail + 1)

			// 論理演算子に合わせてBoolExprの式を生成する
			return when(logicalOperator) {
				"=" -> ctx.mkEq(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				"<>" -> ctx.mkNot(ctx.mkEq(convertArithExpr(leftOperand), convertArithExpr(rightOperand)))
				"<" -> ctx.mkLt(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				"<=" -> ctx.mkLe(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				">" -> ctx.mkGt(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				">=" -> ctx.mkGe(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				"and" -> ctx.mkAnd(convertBoolExpr(leftOperand), convertBoolExpr(rightOperand))
				"or" -> ctx.mkOr(convertBoolExpr(leftOperand), convertBoolExpr(rightOperand))
				"xor" -> ctx.mkXor(convertBoolExpr(leftOperand), convertBoolExpr(rightOperand))
				"=>" -> ctx.mkImplies(convertBoolExpr(leftOperand), convertBoolExpr(rightOperand))
				"nand" -> ctx.mkNot(ctx.mkAnd(convertBoolExpr(leftOperand), convertBoolExpr(rightOperand)))
				"nor" -> ctx.mkNot(ctx.mkOr(convertBoolExpr(leftOperand), convertBoolExpr(rightOperand)))
				"not=>" -> ctx.mkNot(ctx.mkImplies(convertBoolExpr(leftOperand), convertBoolExpr(rightOperand)))
				else -> throw NotOperatorException("logical operator \"$logicalOperator\" is not supported")
			}
		}

    	/**
		 * 与えられた演算式をExpr型に変換する.
		 *
		 * @args expression_ 演算式
		 * @Return Expr型に変換したexpression_
		 */
		private fun convertArithExpr(expression_: String): ArithExpr? {
			if(expression_ == "") return null

			val expression = expression_.removeEndParentheses().removePrefix(" ").removeSuffix(" ")

			// 単一のオペランドの場合
			if(expression.split(" ").size == 1) {
				// expressionをロング型に変換する（変数の場合はnull）
				val valueOrNull = expression.toLongOrNull()
				
				if(valueOrNull == null) { // 変数の場合
					return ctx.mkIntConst(expression)
				} else { // 数値の場合
					return ctx.mkInt(expression.toLong())
				}
			}

			val indexOfLeftTail = getOperand(expression)
			val indexOfOperatorTail = getOperand(expression, indexOfLeftTail + 2)
			
			val leftOperand = expression.substring(0, indexOfLeftTail)
			val operator = expression.substring(indexOfLeftTail + 1, indexOfOperatorTail)
			val rightOperand = expression.substring(indexOfOperatorTail + 1)

			return when(operator) {
				"+" -> ctx.mkAdd(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				"-" -> ctx.mkSub(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				"*" -> ctx.mkMul(convertArithExpr(leftOperand), convertArithExpr(rightOperand))
				"/", "mod", "rem", "div" -> convertArithExprAndAdditionalExpr(leftOperand, rightOperand, operator)
				else -> throw NotOperatorException("operator \"$operator\" is not supported")
			}
		}

    	/**
		 * 引数型等の問題で直接Expr式を生成できない演算のために,
		 * オペランドを一時変数に置き換えてExpr式を返す.
		 * 置き換えたオペランドをexprListに記録する.
		 *
		 * @args leftOperand_ modの左のオペランド
		 * @args rightOperand_ modの右のオペランド
		 * @args operator 演算子
		 * @Return Expr式
		 */
		private fun convertArithExprAndAdditionalExpr(leftOperand_: String, rightOperand_: String, operator: String): ArithExpr?{
			// mkMod()の引数用の一時変数
			val left: IntExpr
			val right: IntExpr

			val leftOperand = leftOperand_.removeEndParentheses()
			val rightOperand = rightOperand_.removeEndParentheses()


			// 左のオペランドを整理する
			if (leftOperand.toLongOrNull() == null) { // 数値化できない場合，変数に置き換える
				left = ctx.mkIntConst(leftOperand.replace(" ", "") )
				exprList.add(ctx.mkEq(left, convertArithExpr(leftOperand)))
			} else {
				left = ctx.mkInt(leftOperand.toLong())
			}
	
			// 右のオペランドを整理する
			if (rightOperand.toLongOrNull() == null) { // 数値化できない場合，変数に置き換える
				right = ctx.mkIntConst(rightOperand.replace(" ", "") )
				exprList.add(ctx.mkEq(right, convertArithExpr(rightOperand)))
			} else {
				right = ctx.mkInt(rightOperand.toLong())
			}

			// /の場合は丸ごと置き換えてIntExpr型で返す
			if (operator == "/"){
				/*
				 * operand = left / rightを解くために
				 * left = operand * rightと
				 * right != 0 の式をexprListに追加する
				 */
				val operand = "<$leftOperand-/-$rightOperand>".replace(" ", "")
				exprList.add(ctx.mkEq(left, ctx.mkMul(ctx.mkIntConst(operand), right)))
				exprList.add(ctx.mkNot(ctx.mkEq(right, ctx.mkInt(0))))
				return ctx.mkIntConst(operand)
			}

			// divの場合は丸ごと置き換えてIntExpr型で返す
			if (operator == "div"){
				/*
				 * operand = left div rightを解くために
				 * left rem right = left - right * operandと
				 * right != 0 の式をexprListに追加する
				 */
				val operand = "<$leftOperand-div-$rightOperand>".replace(" ", "")
				exprList.add(ctx.mkEq(ctx.mkRem(left, right), ctx.mkSub(left, ctx.mkMul(right, ctx.mkIntConst(operand)))))
				exprList.add(ctx.mkNot(ctx.mkEq(right, ctx.mkInt(0))))
				return ctx.mkIntConst(operand)
			}
	
			return when(operator) {
				"mod" -> ctx.mkMod(left, right)
				"rem" -> ctx.mkRem(left, right)
				else -> throw NotOperatorException("operator \"$operator\" is not supported")
			}
		}

    	/**
		 * 与えられた条件式の境界を取る条件式をすべて返す.
		 *
		 * @args condition_ 条件式（比較演算子一つを想定）
		 * @Return condition_の境界を取る条件式
		 */
		fun convertBoundaryConditions(condition_: String): ArrayList<String> {
			val boundaryConditions: ArrayList<String> = ArrayList() // conditionの境界を取る条件式
			boundaryConditions.addAll(convertToBoundaryConditionsByBoolean(condition_, true))
			boundaryConditions.addAll(convertToBoundaryConditionsByBoolean(condition_, false))

			return boundaryConditions
		}

		/**
		 * 与えられた条件式と真偽値における境界を取る条件式を返す.
		 *
		 * @args condition_ 条件式（比較演算子一つを想定）
		 * @args bool condition_がtrueとなるかfalseとなるか
		 * @Return boolとなるcondition_の境界を取る条件式
		 */
		fun convertToBoundaryConditionsByBoolean(condition_: String, bool: Boolean): ArrayList<String> {
			val boundaryConditions: ArrayList<String> = ArrayList() // conditionの境界を取る条件式
			var condition = condition_

			// []で囲んだ前提条件を一旦外して境界を取る条件式を取る
			val regex = Regex("""\sand\s\[.*?\]""")
			val requirements = regex.findAll(condition) // 前提条件を取得する
			requirements.forEach { r ->
				condition = condition.replace(r.value, "") // 前提条件を外す
			}
			condition = condition.alignParentheses().removeEndParentheses()

	
			val indexOfLeftTail = getOperand(condition)
			val indexOfOperatorTail = getOperand(condition, indexOfLeftTail + 2)
			
			val leftOperand = condition.substring(0, indexOfLeftTail)
			val comparisonOperator = condition.substring(indexOfLeftTail + 1, indexOfOperatorTail)
			// 右オペランド全体を囲う括弧を確実につけるために，removeEndParentheses()したものに括弧を付ける
			val rightOperand = "(" + condition.substring(indexOfOperatorTail + 1).removeEndParentheses() + ")"

			// condition_の境界を取る条件式をboundaryConditionsに追加する
			if (bool) {
				when(comparisonOperator) {
					"=" -> {
						boundaryConditions.add("$leftOperand = $rightOperand") // condition_がtrueとなる条件式
					}
					"<>" -> {
						boundaryConditions.add("$leftOperand = $rightOperand + 1") // condition_がtrueとなる条件式
						boundaryConditions.add("$leftOperand = $rightOperand - 1") // condition_がtrueとなる条件式
					}
					">=" -> {
						boundaryConditions.add("$leftOperand = $rightOperand") // condition_がtrueとなる条件式
					}
					">" -> {
						boundaryConditions.add("$leftOperand = $rightOperand + 1") // condition_がtrueとなる条件式
					}
					"<=" -> {
						boundaryConditions.add("$leftOperand = $rightOperand") // condition_がtrueとなる条件式
					}
					"<" -> {
						boundaryConditions.add("$leftOperand = $rightOperand - 1") // condition_がtrueとなる条件式
					}
					"=>" -> {
						val leftTB = convertToBoundaryConditionsByBoolean(leftOperand, true)
						val leftFB = convertToBoundaryConditionsByBoolean(leftOperand, false)
						val rightTB = convertToBoundaryConditionsByBoolean(rightOperand, true)
						val rightFB = convertToBoundaryConditionsByBoolean(rightOperand, false)

						leftTB.forEach { lt ->
							rightTB.forEach { rt ->
								boundaryConditions.add("($lt) and ($rt)") // TB and TBとなる条件式
							}
						}

						leftFB.forEach { lf ->
							rightTB.forEach { rt ->
								boundaryConditions.add("($lf) and ($rt)") // FB and TBとなる条件式
							}
							rightFB.forEach { rf ->
								boundaryConditions.add("($lf) and ($rf)") // FB and FBとなる条件式
							}
						}
					}
					"and" -> {
						val leftTB = convertToBoundaryConditionsByBoolean(leftOperand, true)
						val rightTB = convertToBoundaryConditionsByBoolean(rightOperand, true)

						leftTB.forEach { lt ->
							rightTB.forEach { rt ->
								boundaryConditions.add("($lt) and ($rt)") // TB and TBとなる条件式
							}
						}
					}
					"or" -> {
						val leftTB = convertToBoundaryConditionsByBoolean(leftOperand, true)
						val rightTB = convertToBoundaryConditionsByBoolean(rightOperand, true)
						val leftFB = convertToBoundaryConditionsByBoolean(leftOperand, false)
						val rightFB = convertToBoundaryConditionsByBoolean(rightOperand, false)

						leftTB.forEach { lt ->
							rightTB.forEach { rt ->
								boundaryConditions.add("($lt) and ($rt)") // TB and TBとなる条件式
							}

							rightFB.forEach { rf ->
								boundaryConditions.add("($lt) and ($rf)") // TB and FBとなる条件式
							}
						}

						leftFB.forEach { lf ->
							rightTB.forEach { rt ->
								boundaryConditions.add("($lf) and ($rt)") // FB and TBとなる条件式
							}
						}
					}
					else -> throw NotOperatorException("comparison operator \"$comparisonOperator\" is not supported")
				}
			} else {
				when(comparisonOperator) {
					"=" -> {
						boundaryConditions.add("$leftOperand = $rightOperand + 1") // condition_がfalseとなる条件式
						boundaryConditions.add("$leftOperand = $rightOperand - 1") // condition_がfalseとなる条件式
					}
					"<>" -> {
						boundaryConditions.add("$leftOperand = $rightOperand") // condition_がfalseとなる条件式
					}
					">=" -> {
						boundaryConditions.add("$leftOperand = $rightOperand - 1") // condition_がfalseとなる条件式
					}
					">" -> {
						boundaryConditions.add("$leftOperand = $rightOperand") // condition_がfalseとなる条件式
					}
					"<=" -> {
						boundaryConditions.add("$leftOperand = $rightOperand + 1") // condition_がfalseとなる条件式
					}
					"<" -> {
						boundaryConditions.add("$leftOperand = $rightOperand") // condition_がfalseとなる条件式
					}
					"=>" -> {
						val leftTB = convertToBoundaryConditionsByBoolean(leftOperand, true)
						val rightFB = convertToBoundaryConditionsByBoolean(rightOperand, false)

						leftTB.forEach { lt ->
							rightFB.forEach { rf ->
								boundaryConditions.add("($lt) and ($rf)") // TB and FBとなる条件式
							}
						}
					}
					"and" -> {
						val leftTB = convertToBoundaryConditionsByBoolean(leftOperand, true)
						val rightTB = convertToBoundaryConditionsByBoolean(rightOperand, true)
						val leftFB = convertToBoundaryConditionsByBoolean(leftOperand, false)
						val rightFB = convertToBoundaryConditionsByBoolean(rightOperand, false)

						leftTB.forEach { lt ->
							rightFB.forEach { rf ->
								boundaryConditions.add("($lt) and ($rf)") // TB and FBとなる条件式
							}
						}

						leftFB.forEach { lf ->
							rightTB.forEach { rt ->
								boundaryConditions.add("($lf) and ($rt)") // FB and TBとなる条件式
							}

							rightFB.forEach { rf ->
								boundaryConditions.add("($lf) and ($rf)") // FB and FBとなる条件式
							}
						}
					}
					"or" -> {
						val leftFB = convertToBoundaryConditionsByBoolean(leftOperand, false)
						val rightFB = convertToBoundaryConditionsByBoolean(rightOperand, false)

						leftFB.forEach { lf ->
							rightFB.forEach { rf ->
								boundaryConditions.add("($lf) and ($rf)") // FB and FBとなる条件式
							}
						}
					}
					else -> throw NotOperatorException("comparison operator \"$comparisonOperator\" is not supported")
				}
			}
	
			var requirementsStr = ""
			requirements.forEach { r ->
				requirementsStr += r.value
			}
			requirementsStr = requirementsStr.replace("[", "(").replace("]", ")")
			boundaryConditions.replaceAll { "(" + it + ")" + requirementsStr}
			return boundaryConditions
		}
	
		/**
		 * 与えられた条件式を真偽値に合わせて変換する.
		 *
		 * @args condition 条件式（比較か論理演算子一つを想定）
		 * @args bool conditionがtrueとなるかfalseとなるか
		 * @Return boolの真偽値に合わせて変換したcondition
		 */
		fun convertToBooleanCondition(condition: String, bool: Boolean): String {
			// tureの場合はそのままconditionを返す
			if (bool) return condition
	
			val comparisonOperator = Util.getComparisonOperator(condition) // 比較演算子を取得
			return when(comparisonOperator) {
				"=" -> condition.replace(comparisonOperator, "<>")
				"<>" -> condition.replace(comparisonOperator, "=")
				">" -> condition.replace(comparisonOperator, "<=")
				">=" -> condition.replace(comparisonOperator, "<")
				"<" -> condition.replace(comparisonOperator, ">=")
				"<=" -> condition.replace(comparisonOperator, ">")
				"=>" -> condition.replace(comparisonOperator, "not=>")
				"and" -> condition.replace(comparisonOperator, "nand")
				"or" -> condition.replace(comparisonOperator, "nor")
				else -> throw NotOperatorException("comparison operator \"$comparisonOperator\" is not supported")
			}
		}

		// オペランドの末尾のインデックスを返す
		private fun getOperand(expression: String, index: Int = 0): Int {
			val expCharList = expression.removeEndParentheses().toCharArray()

			if(expCharList[index] != '('){
				for(i in expCharList.indices){
					if(expCharList[index + i] == ' ') return index + i
				}
				return -1
			} else {
				var leftCount: Int = 0
				var rightCount: Int = 0

				for(i in expCharList.indices){
					if(expCharList[index + i] == '(') leftCount++
					else if (expCharList[index + i] == ')') rightCount++

					if(leftCount == rightCount) return i + 1
				}
				return -1
			}
		}

	}
}

class NotOperatorException(msg: String) : RuntimeException(msg)

class NotTypeException(msg: String) : RuntimeException(msg)

class NotSolveException(msg: String) : RuntimeException(msg)

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
