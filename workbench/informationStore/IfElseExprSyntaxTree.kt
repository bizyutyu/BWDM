package com.github.korosuke613.bwdm.informationStore

import com.github.korosuke613.bwdm.alignParentheses
import java.util.*

class IfElseExprSyntaxTree(_ifExpressionBody: String) {

    lateinit var root: IfNode
        internal set
    internal lateinit var ifElses: MutableList<String>
    private var count = 0


    init {
        shapeIfElseBody(_ifExpressionBody)
        generateIfElseSyntaxTree()

    } //end constructor

    /*
     * shaping of passed ifElseBody
     */
    private fun shapeIfElseBody(_ifElseBody: String) {
        ifElses = ArrayList()
        var ifElseBody = _ifElseBody
        ifElseBody = ifElseBody
                .replace("if", "if\n").replace("else", "\nelse\n")
                .replace("then", "").replace("\n\n", "\n")
				.replace("(\n", "(").replace("\n)", ")")
				.replace(";\n", ";")

		ifElses = mutableListOf(*ifElseBody.split("\n").dropLastWhile{ it == ""}.toTypedArray())
		for (i in 0 until ifElses.size) {
			ifElses[i] = ifElses[i].removePrefix(" ").removeSuffix(" ").alignParentheses()
		}
    }


    // if式構文木を作る
    private fun generateIfElseSyntaxTree() {
        if (ifElses[0] != "if") {
        	val currentLine = ifElses[count++]
			root = IfNode(currentLine, 0)
        	root.isIfNode = false
        	root.isTrueNode = null
        } else {
        	count++ // 最初はifなので無視
        	val currentLine = ifElses[count++] // 最初のifの条件式
        	root = generateIfNode(currentLine, null, 0)
        	root.isIfNode = true
        	root.isTrueNode = null
		}
    }

    private fun generateIfNode(_condition: String, _parentNode: IfNode?, _nodeLevel: Int): IfNode {
        val ifNode = IfNode(_condition, _nodeLevel)
        ifNode.parentNode = _parentNode
        var nextToken: String = ifElses[count++]

        //trueNode
        if (nextToken == "if") {//ifの場合、次のtokenは条件式なので読み込む
            val conditionStr = ifElses[count++]
            ifNode.conditionTrueNode = generateIfNode(conditionStr, ifNode, _nodeLevel + 1)
        } else {//ifじゃない場合、nextTokenにはreturnが入っている
            ifNode.conditionTrueNode = generateReturnNode(nextToken, ifNode, _nodeLevel + 1)
        }
        ifNode.conditionTrueNode!!.isTrueNode = true

        //else 特にすることは無いので無視
        //ということはif_elseファイルからelseを消しても問題無し？
        count++

        //elseの次、falseNode
        //falseNode
        nextToken = ifElses[count++]
        if (nextToken == "if") {//ifの場合、次のtokenは条件式なので読み込む
            val conditionStr = ifElses[count++]
            ifNode.conditionFalseNode = generateIfNode(conditionStr, ifNode, _nodeLevel + 1)
        } else {//ifじゃない場合、nextTokenにはreturnが入っている
            ifNode.conditionFalseNode = generateReturnNode(nextToken, ifNode, _nodeLevel + 1)
        }
        ifNode.conditionFalseNode!!.isTrueNode = false

        return ifNode
    }

    private fun generateReturnNode(returnStr: String,
                                   parentNode: Node,
                                   _nodeLevel: Int): ReturnNode {
        val returnNode = ReturnNode(returnStr, _nodeLevel)
        returnNode.parentNode = parentNode
        return returnNode
    }

	private fun extractParentheses(string: String): String {
		// 先頭に括弧がない場合はそのまま返す
		if(string.substring(0, 1) != "(") return string
		val stringList = string.toCharArray()
		var parenthesesCount: Int = 1
		for (i in 1 until stringList.size-1){
			if(stringList[i] == '(') parenthesesCount++
			if(stringList[i] == ')') parenthesesCount--

			/*
			 * 末尾に到達する前にカウントが0になった場合，
			 * 全体を括弧で囲っていないため，何もしない
			 */
			if(parenthesesCount == 0) return string.substring(1, i-1)
		}

		// 先頭と末尾の括弧を外す
		throw IllegalArgumentException("No corresponding parentheses")
	}
}
