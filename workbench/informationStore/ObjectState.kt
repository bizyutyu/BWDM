package com.github.korosuke613.bwdm.informationStore

import com.fujitsu.vdmj.tc.definitions.TCExplicitOperationDefinition
import java.util.*

class ObjectState(operationDefinition: TCExplicitOperationDefinition) {

	internal lateinit var expressions: MutableList<String>
	internal var precondition = operationDefinition.precondition?.toString() ?: ""
	internal var postcondition = operationDefinition.postcondition?.toString() ?: ""
	internal var isConstant: Boolean = false

    init {
		if (operationDefinition.parameterPatterns.toString() == "") {
			isConstant = true
		}
		
		divideOperationBody(operationDefinition.body.toString())
    } //end constructor

    private fun divideOperationBody(operationBody_: String) {
		
		expressions = ArrayList()
   		if(!operationBody_.contains(":=")) {
			isConstant = true
			return
		}

		var body = operationBody_
		if(body.contains(";")){
			body = body.removePrefix("(")
			body = body.removeSuffix(")")
		}
		val expressions_ = body.split(";")
		expressions_.forEach { exp_ ->
			var exp = exp_.split(" ", "\n").toMutableList()
			exp.removeAll { it == "" }
			val str = StringBuilder()
			exp.forEach {
				str.append(it)
				str.append(" ")
			}
			if(str.contains(":=")){ 
				expressions.add(String(str).removeSuffix(" "))
			}
		}
    }
}
