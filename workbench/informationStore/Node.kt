package com.github.korosuke613.bwdm.informationStore

abstract class Node {
    /*
	 *parentNodeは絶対IfNodeだからIfNodeにしてもいいかも
	 */
    var parentNode: Node? = null

    var nodeLevel: Int = 0 //このノードのいる階層 rootが0
    var id: Int = 0 //このノードのID
    abstract var isIfNode: Boolean //自身がIfNodeなのか
    var isTrueNode: Boolean? = null //自身がconditionTrueNodeなのか

    //抽象メソッド
    //IfNode or ReturnNodeかで conditionStr or returnStrを返す
    abstract val conditionOrReturnStr: String

    companion object {
        var staticID = 0 //ノードを作ったら1つずつ数字が増える ノードの総数
    }

    open fun getIsIfNode(): Boolean {
        return isIfNode
    }
}
