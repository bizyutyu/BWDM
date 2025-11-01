package com.github.korosuke613.bwdm.symbolicExecutionUnit

import com.github.korosuke613.bwdm.UnitMain
import com.github.korosuke613.bwdm.informationStore.Definition


class SeUnitMain
(definition: Definition) : UnitMain<String>(definition) {
    override val analyzer: SymbolicExecutioner = SymbolicExecutioner(definition)

    override val allTestCases: String
        get() {
            return getTestCases(analyzer.getExpectedOutputDataList())
        }
}
