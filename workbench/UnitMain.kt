package com.github.korosuke613.bwdm

import com.github.korosuke613.bwdm.informationStore.Definition
import java.util.*

abstract class UnitMain<K>(private val definition: Definition) {
    abstract val allTestCases: String
    abstract val analyzer: Analyzer<K>
    fun getTestCases(outputDataList: ArrayList<String>): String {
        val buf = StringBuilder()
        val inputDataList = analyzer.inputDataList
        val parameters = definition.parameters

        for (i in outputDataList.indices) {
            buf.append("No.").append(i + 1).append(" : ")
            val inputData = inputDataList[i]
            for (prm in parameters) {
                buf.append(inputData[prm]).append(" ")
            }
            buf.append("-> ").append(outputDataList[i]).append("\n")
        }
        return buf.toString()
    }
}
