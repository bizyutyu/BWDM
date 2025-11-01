package com.github.korosuke613.bwdm

import org.kohsuke.args4j.Argument
import org.kohsuke.args4j.Option
import org.kohsuke.args4j.spi.StringArrayOptionHandler



class Shell{
    @Option(name = "-v", aliases = ["--version"], usage = "print version")
    var versionFlag: Boolean = false

    @Option(name = "-h", aliases = ["--help"], usage = "print usage message and exit")
    var usageFlag: Boolean = false

    @Option(name = "-n", usage = "VDM仕様の基本情報を表示")
    var showStandardInfo: Boolean = false

    @Option(name = "-a", depends = ["-b"], usage = "生成した境界値に関する情報を表示")
    var showBvsInfo: Boolean = false

    @Option(name = "-i", depends = ["-s"], usage = "記号実行時に生成した条件式と戻り値に関する情報を表示")
    var showSeConditionsInfo: Boolean = false

    @Option(name = "-b", usage = "境界値分析によるテストケースを出力")
    var showBvTestcases: Boolean = false

    @Option(name = "-m", usage = "ドメインテストによるテストケースを出力")
    var showDaTestcases: Boolean = false

    //6 境界値テストケース（ペアワイズ適用） default:ON  -p
    @Option(name = "-p", depends = ["-b"], usage = "境界値分析にペアワイズ法を適用したテストケースを出力")
    var showBvTestcasesWithPairwise: Boolean = false

    @Option(name = "-s", usage = "記号実行によるテストケースを出力")
    var showSeTestcases: Boolean = false

    @Option(name = "-d", aliases = ["--print_display"], usage = "ディスプレイ表示")
    var displayOnConsole: Boolean = false

    @Option(name = "-f", aliases = ["--output_file"], usage = "テキストファイル<file_name>.tcに書出")
    var writeFile: Boolean = false

    @Option(name = "-fo", aliases = ["--output_specified_file"], metaVar = "<output file name>", usage = "テキストファイル<output file name>に書出")
    var writeFileName : String? = null

    @Option(name = "-t", aliases = ["--time_measurement"], usage = "計算時間の表示")
    var printTimeMeasure: Boolean = false

    @Argument(index = 0, metaVar = "<vdm file name>")
    var vdmFileName: String? = null

    @Argument(index = 1, metaVar = "arguments...", handler = StringArrayOptionHandler::class)
    var arguments: Array<String>? = null
}
