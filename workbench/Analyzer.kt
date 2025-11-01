package com.github.korosuke613.bwdm

import com.github.korosuke613.bwdm.informationStore.Definition

abstract class Analyzer<K>(val definition: Definition) {
    val inputDataList: ArrayList<HashMap<String, K>> = ArrayList()
    val parameters = definition.parameters
}