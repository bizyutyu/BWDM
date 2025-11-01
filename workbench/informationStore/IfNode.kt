package com.github.korosuke613.bwdm.informationStore

class IfNode(conditionStr: String, _nodeLevel: Int) : Node() {
    var conditionTrueNode: Node? = null

    var conditionFalseNode: Node? = null //Ifノードには子ノードが2つ
    override val conditionOrReturnStr = conditionStr
    override var isIfNode = true

    init {
        nodeLevel = _nodeLevel
        id = staticID++
    }
}
