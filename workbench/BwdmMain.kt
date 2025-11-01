package com.github.korosuke613.bwdm

import com.fujitsu.vdmj.lex.LexException
import com.fujitsu.vdmj.syntax.ParserException
import com.github.korosuke613.bwdm.boundaryValueAnalysisUnit.BvaUnitMain
import com.github.korosuke613.bwdm.domainAnalysis.DomainAnalyser
import com.github.korosuke613.bwdm.informationStore.Definition
import com.github.korosuke613.bwdm.informationStore.FunctionDefinition
import com.github.korosuke613.bwdm.informationStore.InformationExtractor
import com.github.korosuke613.bwdm.informationStore.OperationDefinition
import com.github.korosuke613.bwdm.symbolicExecutionUnit.SeUnitMain

import external.TimeMeasure
import org.kohsuke.args4j.CmdLineException
import org.kohsuke.args4j.CmdLineParser
import java.io.File
import java.io.FileWriter
import java.io.IOException
import java.util.*
import kotlin.system.exitProcess


/**
 * main class of BWDM
 */
object BwdmMain {
    // build日
    private const val buildDate = "2018-1-24 PM19:03(JST)"
    private lateinit var extractInformation: InformationExtractor
    private lateinit var bvaUnitMain: BvaUnitMain
    private lateinit var seUnitMain: SeUnitMain
    private lateinit var domainAnalyser: DomainAnalyser
    private val shell = Shell()
    private lateinit var buf: String

    /**
     * main method.
     *
     * @args args Command line arguments.
     */
    @Throws(LexException::class, ParserException::class, IOException::class)
    @JvmStatic
    fun main(vararg args: String) {
        execBWDM(*args)
    }

    /**
     * processing of BWDM
     *
     * @args args Command line arguments.
     */
    @Throws(IOException::class, LexException::class, ParserException::class)
    private fun execBWDM(vararg args: String) {

        val parser = CmdLineParser(shell)
        try {
            parser.parseArgument(*args)
        } catch (e: CmdLineException) {
            // 引数の型がおかしかったり、必須項目が足りないと例外
            System.err.println("Got Exception: " + e.message)
            parser.printUsage(System.err)
            exitProcess(1)
        }

        //コマンド引数のパース
        when (args.size) {
            0->{
                printUsage(parser)
                return
            }
            1 //ヘルプ表示 or バージョン表示 or オプション指定ミス or ファイル指定による通常実行の4パターン
            -> {
                when {
                    shell.versionFlag -> printVersionInfo()
                    shell.usageFlag -> printUsage(parser)
                    else -> printUsage(parser)
                }
                return
            }
        }

        /**オプションに従って出力文字列を生成 */
        buf = ""
        extractInformation = InformationExtractor(shell.vdmFileName!!)
        extractInformation.explicitFunctions.values.forEach{ functionDefinition: FunctionDefinition ->
            generateTest(functionDefinition)
        }
        extractInformation.explicitOperations.values.forEach { operationDefinition: OperationDefinition ->
            generateTest(operationDefinition)
        }
    }

    private fun generateTest(definition: Definition) {
        if (definition.isSetter && definition.isObjectSetter) {
            // operationはセッターであるためテストしない
            return
        }

		buf = ""
		var testcases: String = ""
        val tm = TimeMeasure()
        tm.start()

		//if(!definition.isSetter) {
			
       	if (shell.showStandardInfo) {
       	    showStandardInfo(definition)
       	}

       	if (shell.showBvTestcases) {
       		bvaUnitMain = BvaUnitMain(definition, isPairwise = shell.showBvTestcasesWithPairwise)
	   		if (shell.showBvsInfo) {
       		    showBvsInfo(definition)
       		}

	   		if(!shell.showBvTestcasesWithPairwise) {
       	    	testcases += ">> 境界値分析によるテストケース\n"
       		} else {
       	    	testcases += ">> 境界値分析によるテストケース（ペアワイズ法適用）\n"
	   		}
       	   	testcases += bvaUnitMain.allTestCases
       	   	testcases += "\n"
       	}

       	if (shell.showSeTestcases) {
       		seUnitMain = SeUnitMain(definition)
       		if (shell.showSeConditionsInfo) {
       		    showSeConditionInfo(definition)
       		}
       	    testcases += ">> 記号実行によるテストケース\n"
       	    testcases += seUnitMain.allTestCases
       	    testcases += "\n"
       	}

       	if (shell.showDaTestcases) {
       	    testcases += ">> ドメインテストによるテストケース\n"
       	    domainAnalyser = DomainAnalyser(definition)
       	    testcases += domainAnalyser.allTestcasesByDa
       	    testcases += "\n"
       	}
		//}
        //if (!definition.isObjectSetter && definition is OperationDefinition) {
        //	val osaUnitMain = ObjectStateAnalyzer(definition, isPairwise = shell.showBvTestcasesWithPairwise)
        //    buf += "オブジェクトの状態に対するテストケース\n"
        //	buf += osaUnitMain.allTestCases
        //    buf += "\n"
        //}

		buf = buf + testcases

        if (shell.displayOnConsole) {
            print(buf)
        }
        if (shell.writeFile) {
            outputFile(extractInformation.vdmFilePath.replace("vdmpp", "tc"))
        } else if (shell.writeFileName != null) {
            outputFile(shell.writeFileName!!)
        }

        tm.finish()
        if (shell.printTimeMeasure) {
            tm.printResult()
        }
    }

    private fun printUsage(parser: CmdLineParser) {
        println("Usage:")
        println(" bwdm [options] vdmFileName")
        println()
        println("Options:")
        parser.printUsage(System.out)
        return
    }

    private fun printVersionInfo() {
        println("BWDM (Boundary Values/VDM)")
        println("Automatic Testcase Generation Tool based on VDM++ Specification")
        println("Version : 2.0")
        println("Built date : $buildDate")
        println("Copyright (C) 2018, Hiroki TACHIYAMA, Futa HIRAKOBA, and Takafumi MUTO(University of Miyazaki).")
        return
    }

    private fun outputFile(file_name: String) {
        val outputFile = File(file_name)
        val fw = FileWriter(outputFile)
        fw.write(buf)
        fw.close()
    }

    private fun showStandardInfo(definition: Definition) {
        buf += "ファイルパス : " + File(shell.vdmFileName!!).canonicalPath + "\n"
        buf += "関数名 : " + definition.name + "\n"
        buf += "引数の型 : "
        for (i in 0 until definition.argumentTypes.size) {
            buf += (definition.parameters[i] + ":"
                    + definition.argumentTypes[i] + " ")
        }
        buf += "\n"
        buf += "戻り値の型 : " + definition.returnValue + "\n"
		buf += "\n"
        //val bvTestcaseNum = bvaUnitMain.analyzer.inputDataList.size
        //val seTestcaseNum = seUnitMain.analyzer.inputDataList.size
		//val obTestcaseNum = 0
        //buf += "生成テストケース数 : " + (bvTestcaseNum + seTestcaseNum +obTestcaseNum) + "件"
        //buf += "(境界値分析:$bvTestcaseNum/記号実行:$seTestcaseNum)"
        //buf += "\n\n"
    }

    private fun showBvsInfo(definition: Definition) {
        buf += "各引数の境界値\n"
        val bvsList: HashMap<*, *> = bvaUnitMain.analyzer.boundaryValueList
        val parameters = definition.parameters
        for (i in parameters.indices) {
            val currentPrm = parameters[i]
            val bvs: ArrayList<*> = bvsList[currentPrm] as ArrayList<*>
            buf += "$currentPrm : "
            for (bv in bvs) {
                buf += "$bv "
            }
            buf += "\n"
        }
        buf += "\n"
    }

    private fun showSeConditionInfo(definition: Definition) {
        buf += "記号実行情報\n"
        val carvList = definition.conditionAndReturnValueList
        buf += "戻り値の数 : " + carvList!!.size + "\n"

        for (i in 0 until carvList.size) {
            buf += "制約 : "
            val carv = carvList.conditionAndReturnValues[i]
            val conditions = carv.conditions
            val bools = carv.bools

            //はじめの一つ以外は、前に and をつけてくっつける
            buf += if (bools[0]) {
                conditions[0] + " "
            } else {
                "!(" + conditions[0] + ") "
            }

            for (j in 1 until conditions.size) { //はじめの一個以外
                buf += if (bools[j]) {
                    "and " + conditions[j]
                } else {
                    "and !( " + conditions[j] + " ) "
                }
            }
            buf += ", 戻り値 : " + carv.returnStr + "\n"
        }
        buf += "\n"
    }
}
