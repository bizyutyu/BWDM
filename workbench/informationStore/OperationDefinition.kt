package com.github.korosuke613.bwdm.informationStore

import com.fujitsu.vdmj.lex.LexException
import com.fujitsu.vdmj.syntax.ParserException
import com.fujitsu.vdmj.tc.definitions.TCExplicitOperationDefinition
import com.fujitsu.vdmj.tc.definitions.TCInstanceVariableDefinition
import com.fujitsu.vdmj.tc.definitions.TCValueDefinition
import com.fujitsu.vdmj.tc.definitions.TCTypeDefinition
import java.io.IOException

class OperationDefinition
(tcDefinition: TCExplicitOperationDefinition,
 private val instanceVariables: LinkedHashMap<String, TCInstanceVariableDefinition>,
 private val constantValues: LinkedHashMap<String, TCValueDefinition>,
 private val types: LinkedHashMap<String, TCTypeDefinition>,
 private val invariant: String) : Definition(tcDefinition) {

    // 利用しているメンバ変数のリスト
    private val usedInstanceVariables: LinkedHashMap<String, String> = linkedMapOf()

    override var returnValue: String = tcDefinition.type.result.toString()

	private	val objectState = ObjectState(tcDefinition)
	
	// 操作の被代入変数(key)と代入演算式(value)
	val operationExpressions: LinkedHashMap<String, String> = linkedMapOf()

    init {
        // 引数の型を登録
        tcDefinition.type.parameters.forEach { e ->
			var argumentType = e.toString()
			argumentType = argumentType.removePrefix("(unresolved ")
			argumentType = argumentType.removeSuffix(")")
			argumentTypes.add(argumentType)
		}

		instanceVariables.forEach { (key, value) ->
			initInstanceVariables[key] = value.expression.toString() // インスタンス変数の値を格納
		}

        // IfElseを構文解析
        ifExpressionBody = tcDefinition.body.toString()

        try {
            // 定数を実数に置き換え
            constantValues.forEach {
                if (ifExpressionBody.contains(it.key)) {
                    ifExpressionBody = ifExpressionBody.replaceVariable(it.key, it.value.exp.toString())
                }
            }
            ifElseExprSyntaxTree = IfElseExprSyntaxTree(ifExpressionBody)
        } catch (e: ParserException) {
            e.printStackTrace()
        } catch (e: LexException) {
            e.printStackTrace()
        } catch (e: IOException) {
            e.printStackTrace()
        }

		setObjectState()
		setIfElseSyntaxTree()
    }

    override fun setIfElseSyntaxTree() {
        //parsing for parameters
        setUsedInstanceVariables()

    	val tcPatternList = (tcDefinition as TCExplicitOperationDefinition).paramPatternList[0] // 仮引数
    	for (parameter in tcPatternList) {
    	    parameters.add(parameter.toString())
    	}
    	//for (variable in usedInstanceVariables) {
    	//    parameters.add(variable.key)
    	//    argumentTypes.add(variable.value)
		//	paramToTypeList[variable.key] = variable.value
    	//}
	
        conditionAndReturnValueList = ConditionAndReturnValueList(ifElseExprSyntaxTree!!.root)
		setTypeConditions()
        parseIfConditions()
		setOutputConditionsForBva()

    }

    private fun setUsedInstanceVariables() {
        instanceVariables.forEach {
            if (ifExpressionBody.contains(it.key)) {
				var instanceVariableType = it.value.type.toString()

				// 型定義を使用してる場合実際の型に変換する
				if(instanceVariableType.startsWith("(unresolved ")) {
					instanceVariableType = instanceVariableType.removePrefix("(unresolved ")
					instanceVariableType = instanceVariableType.removeSuffix(")")
					run {
					    types.forEach { t ->
							if(t.key == instanceVariableType) {
								if(t.value.invPattern != null){
									var expression = t.value.invExpression.toString()
									expression = expression.replaceVariable(t.value.invPattern.toString(), it.key)
									outputConditions.add(expression) // インスタンス変数型の不変条件をセット
								}

							    instanceVariableType = t.value.type.toDetailedString()
								return@run
							}
						}
					}
				} 

                usedInstanceVariables[it.key] = instanceVariableType 
			}
        }
    }

    override fun parseIfConditions() {
        compositeParameters = ArrayList(parameters)

       	val ifElses = ifElseExprSyntaxTree!!.ifElses

       	for (i in ifElses.indices) {
       	    var element = ifElses[i]
       	    if (element == "if") {
       	        element = ifElses[i + 1]

       	        // 定数を実数に置き換え
       	        constantValues.forEach {
       	            if (element.contains(it.key)) {
       	                element = element.replaceVariable(it.key, it.value.exp.toString())
       	                ifElses[i + 1] = element
       	            }
       	        }
				element.split(" and ", " or ", " => ").forEach {
					conditionsForBva.add(it.alignParentheses().removeEndParentheses())
				}
       	    }
       	}
    }

	fun setObjectState() {

		// 事前条件式をセット
		if(objectState.precondition != ""){	
			inputConditions.add(objectState.precondition)
			objectState.precondition.split(" and ", " or ", " => ").forEach { pre ->
				conditionsForBva.add(pre.alignParentheses())
			}
		}

		// 事後条件をセット
		if(objectState.postcondition != ""){
			outputConditions.add(replaceConstantValues(objectState.postcondition))
		}

		// 出力の制約をセット
		if(returnValue.startsWith("(unresolved ")) { // 戻り値の方が型定義の場合
			val typeName = returnValue.removePrefix("(unresolved ").removeSuffix(")") // 型定義の名前
			val type_ = types[typeName]// 型定義の抽象構文木
			returnValue = type_!!.type?.toDetailedString().toString() // returnValueを実際の方に変換する
			// 戻り値の型の不変条件をoutputConditionsに追加
			if(type_!!.invPattern != null){
				var invExpr = type_!!.invExpression.toString()
				invExpr = invExpr.replaceVariable(type_!!.invPattern.toString(), "RESULT")
				outputConditions.add(invExpr)
			}
			// 戻り値の型の制約をoutputConditionsに追加
			outputConditions.addAll(generateTypeConditions("RESULT", returnValue))
		}

		// 操作するインスタンス変数名をkeyにして操作の演算式を格納する
		//objectState.expressions.forEach {
		//	val operator = it.indexOf(" := ")
		//	val name = it.substring(0, operator)
		//	val expression = it.substring(operator + 4)

		//	operationExpressions[name] = expression
		//}

		// クラス不変条件をセット
		if(invariant != "") {
			val invariantCondition = replaceConstantValues(invariant) // 定数を実数に置換
			outputConditions.add(invariantCondition)
			// 論理演算子で分割する
		}

		// 操作しているインスタンス変数の制約条件をoutputConditionsに追加する
		ifElseExprSyntaxTree!!.ifElses.forEach { body ->
			body.split(";").forEach { expression_ ->
				val expression = expression_.alignParentheses().removeEndParentheses()
				if (expression.contains(":=")) {
					val indexOfOperator = expression.indexOf(" := ")
					val instanceName = expression.substring(0, indexOfOperator) // 操作しているインスタンス変数の名前
					var instanceType = instanceVariables[instanceName]!!.type.toString() // インスタンス変数の型

					// 型定義を使用している場合
					if (instanceType.startsWith("(unresolved ")) {
						val typeName = instanceType.removePrefix("(unresolved ").removeSuffix(")") // 型定義の名前
						instanceType = types[typeName]?.type?.toDetailedString().toString()

						val typeInvariant = types[typeName]!!.invPattern
						// 型の不変条件式をセット
						//if(typeInvariant != null){
						//	var typeInvariantStr = typeInvariant.invExpression.toString()
						//	typeInvariantStr = typeInvariantStr.replaceVariable(type.invPattern.toString(), parameter)
						//	inputConditions.add(expression)
						//	}
						//}
					}

					val instanceConstraints = generateTypeConditions(instanceName, instanceType).subtract(outputConditions) // outputConditionに既にある条件式は追加しない
					outputConditions.addAll(instanceConstraints)
				}
			}
		}

	}

	override fun setTypeConditions() {
		for(i in parameters.indices) {
			val parameter = parameters[i]
			val argumentType = argumentTypes[i]

			types.forEach { 
				if(it.key == argumentType) {
					argumentTypes[i] = it.value.type.toDetailedString()

					var type = it.value
					// 型の不変条件式をセット
					if(type.invPattern != null){
						var expression = type.invExpression.toString()
						expression = expression.replaceVariable(type.invPattern.toString(), parameter)
						inputConditions.add(expression)


						expression.split(" and ", " or ", " => ").forEach {
							// 括弧を揃えて一番外側の括弧を外す
							val exp = it.alignParentheses().removeEndParentheses()
							conditionsForBva.add(it.alignParentheses())
						}
					}
				}
			}

			inputConditions.addAll(generateTypeConditions(parameters[i], argumentTypes[i]))
			paramToTypeList[parameters[i]] = argumentTypes[i]
		}
	}

	/*
	 * 定数を実際の値に置換する
	 */ 
	private fun replaceConstantValues(_condition: String): String {
		var condition = _condition
		
		constantValues.forEach {
			condition = condition.replaceVariable(it.key, it.value.exp.toString())
		}

		return condition
	}
}
