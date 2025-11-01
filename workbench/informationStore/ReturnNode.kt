package com.github.korosuke613.bwdm.informationStore

class ReturnNode internal constructor(returnStr: String, _nodeLevel: Int) : Node() {
    override val conditionOrReturnStr = returnStr
    override var isIfNode = false

    init {
        nodeLevel = _nodeLevel
        id = staticID++
    }
}
