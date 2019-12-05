package com.github.korosuke613.bwdm.boundaryValueAnalysisUnit;

import com.fujitsu.vdmj.lex.LexException;
import com.fujitsu.vdmj.syntax.ParserException;
import com.github.korosuke613.bwdm.informationStore.InformationExtractor;
import java.io.IOException;
import org.junit.jupiter.api.Test;

class BoundaryValueAnalyzerTest {

  @Test
  void test() throws LexException, ParserException, IOException {

    InformationExtractor information =
        new InformationExtractor("./vdm_files/Arg2_Japanese.vdmpp");
    BoundaryValueAnalyzer bvAnalyzer =
        new BoundaryValueAnalyzer(information, false);
  }
}
