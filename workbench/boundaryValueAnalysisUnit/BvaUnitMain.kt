package com.github.korosuke613.bwdm.boundaryValueAnalysisUnit

import com.github.korosuke613.bwdm.UnitMain
import com.github.korosuke613.bwdm.informationStore.Definition
import com.github.korosuke613.bwdm.informationStore.IfElseExprSyntaxTree
import java.util.*

class BvaUnitMain
(definition: Definition, isPairwise: Boolean) : UnitMain<Long>(definition) {
    private val expectedOutputDataGenerator: ExpectedOutputDataGenerator
    override val analyzer: BoundaryValueAnalyzer = BoundaryValueAnalyzer(definition, isPairwise)

    override val allTestCases: String
        get() {
            return getTestCases(expectedOutputDataGenerator.expectedOutputDataList)
        }

    init {
        expectedOutputDataGenerator = ExpectedOutputDataGenerator(
                definition,
                Objects.requireNonNull<IfElseExprSyntaxTree>(definition.ifElseExprSyntaxTree).root,
                analyzer.inputDataList
        )
    }

}
