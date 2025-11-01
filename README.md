# BWDM: Verification tool for Vienna Development Method
Test Cases Auto-Generation from a VDM Specification.

[![](https://img.shields.io/badge/GitHub%20Actions-enable-brightgreen.svg?logo=github)](https://github.com/korosuke613/BWDM/actions) [![codecov](https://codecov.io/gh/korosuke613/BWDM/branch/master/graph/badge.svg)](https://codecov.io/gh/korosuke613/BWDM)

## Execution Environment, using Libraries,
* OS : macOS or Linux
* [![VDMJ Ver.4](https://img.shields.io/badge/VDMJ-4-orange.svg)](https://github.com/nickbattle/vdmj.git) : Lexer and Parser
* [![Z3](https://img.shields.io/badge/Z3-4.6-blue.svg)](https://github.com/Z3Prover/z3) : Theorem Prover
* [![PICT](https://img.shields.io/badge/PICT-e7b0ef-yellow.svg)](https://github.com/Microsoft/pict) : Pairwise Independent Combinatorial Testing
* [![pict4java](https://img.shields.io/badge/pict4java-1.0-yellowgreen.svg)](https://github.com/korosuke613/pict4java) : PICT wrappers for java-class

## install
1. Install Microsoft Z3 library.
2. Download [BWDM.jar](https://github.com/korosuke613/BWDM/releases).


## example

```bash
$ DYLD_LIBRARY_PATH=./libs java -Djna.library.path=./libs -Djava.library.path=./libs -jar BWDM.jar ./vdm_files/probrem.vdmpp -n -a -i -s -b -p -d
```

or

```bash
$ gradlew run -Pargs="./vdm_files/problem.vdmpp" 
```

## options

| Option | Content |
| --- |:---|
| -n | Basically Info. |
| -a | Info. of BVA. |
| -i | Info. of Symbolic Exe.  |
| -b | Output ONLY testcases of BVA. |
| -p | Output ONLY testcases of BVA with pairwise. |
| -s | Output ONLY testcases of Symbolic Exe. |
| -f | Output testcase into a file(default:display on console).|
| -v | Version. |
| -h | Help. |


## build

```bash
$ DYLD_LIBRARY_PATH=./libs;LD_LIBRARY_PATH=./libs; export LD_LIBRARY_PATH; gradle jar
```
