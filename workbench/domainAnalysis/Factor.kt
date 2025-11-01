package com.github.korosuke613.bwdm.domainAnalysis

data class DomainPoints(val name: String){
    val onPoints:ArrayList<HashMap<String, Long>> = ArrayList()
    val offPoints:ArrayList<HashMap<String, Long>> = ArrayList()
    val inPoints:ArrayList<HashMap<String, Long>> = ArrayList()
    val outPoints:ArrayList<HashMap<String, Long>> = ArrayList()
}
