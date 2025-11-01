package com.github.korosuke613.bwdm.informationStore


import java.util.ArrayList

class ConditionAndReturnValueList(_root: IfNode) {

    var size = 0
    val conditionAndReturnValues: ArrayList<ConditionAndReturnValue> = ArrayList()

    inner class ConditionAndReturnValue internal constructor() {
        var returnStr: String? = null
            internal set
        //conditions[0]の真偽値がbools[0]
        //conditions[1]の真偽値がbools[1]...
        var conditions: ArrayList<String>
            internal set
        var bools: ArrayList<Boolean>
            internal set

        init {
            size++
            conditions = ArrayList()
            bools = ArrayList()
        }

    }

    init {
        recursiveReturnNodeFind(_root)

        /*20180124 制約に引数型の制限が必要だと気づいてささっと実装*/
        //各制約に、引数型の制限を加える
        /*

		ArrayList<String> arguments = ie.getArgumentTypes();
		ArrayList<String> parameters = ie.getParameters();

		for(int i=0; i<conditionAndReturnValues.size(); i++) {
			ConditionAndReturnValue currentCarv = conditionAndReturnValues.get(i);
			for(int j=0; j< arguments.size(); j++) {
				String currentType = arguments.get(j);
				String currentParm = parameters.get(j);

				switch (currentType) {
					case "int":
						currentCarv.getConditions().add(currentParm+"<="+Integer.MAX_VALUE);
						currentCarv.bools.add(true);
						currentCarv.getConditions().add(Integer.MIN_VALUE + "<="+currentParm);
						currentCarv.bools.add(true);
						break;
					case "nat":
						currentCarv.getConditions().add(currentParm+"<="+Integer.MAX_VALUE * 2);
						currentCarv.bools.add(true);
						currentCarv.getConditions().add("0" + "<=" + currentParm);
						currentCarv.bools.add(true);
						break;

					case "nat1":
						currentCarv.getConditions().add(currentParm+"<="+Integer.MAX_VALUE * 2 + 1);
						currentCarv.bools.add(true);
						currentCarv.getConditions().add("1" + "<=" + currentParm);
						currentCarv.bools.add(true);
						break;

				}
			}


		}
		*/
        /*ささっと実装ここまで*/


    }


    //ReturnNodeの発見とそこに至る為に必要な条件式とその真偽値
    private fun recursiveReturnNodeFind(node: Node) {
        if (node.isIfNode) { //IfNodeならば
            val ifNode = node as IfNode
            recursiveReturnNodeFind(ifNode.conditionTrueNode!!)
            recursiveReturnNodeFind(ifNode.conditionFalseNode!!)
        } else { //ReturnNodeならば
            val conditionAndReturnValue = ConditionAndReturnValue()
            conditionAndReturnValue.returnStr = node.conditionOrReturnStr

            var tmpNode = node

            while (tmpNode.parentNode != null) { //下のbreak文が
                conditionAndReturnValue.conditions.add(tmpNode.parentNode!!.conditionOrReturnStr)
                conditionAndReturnValue.bools.add(tmpNode.isTrueNode!!) //親ノードからみてTrue側かどうか

                tmpNode = tmpNode.parentNode!!
            } 
            conditionAndReturnValues.add(conditionAndReturnValue)
        }
    }
}
