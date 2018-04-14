package bwdm.informationStore;

import bwdm.Util;
import com.fujitsu.vdmj.ast.definitions.ASTDefinition;
import com.fujitsu.vdmj.ast.definitions.ASTDefinitionList;
import com.fujitsu.vdmj.lex.Dialect;
import com.fujitsu.vdmj.lex.LexException;
import com.fujitsu.vdmj.lex.LexTokenReader;
import com.fujitsu.vdmj.mapper.ClassMapper;
import com.fujitsu.vdmj.syntax.DefinitionReader;
import com.fujitsu.vdmj.syntax.ParserException;
import com.fujitsu.vdmj.tc.definitions.TCDefinition;
import com.fujitsu.vdmj.tc.definitions.TCExplicitFunctionDefinition;
import com.fujitsu.vdmj.tc.expressions.TCExpression;
import com.fujitsu.vdmj.tc.patterns.TCIdentifierPattern;
import com.fujitsu.vdmj.tc.patterns.TCPattern;
import com.fujitsu.vdmj.tc.patterns.TCPatternList;
import com.fujitsu.vdmj.tc.patterns.TCPatternListList;
import com.fujitsu.vdmj.tc.types.TCFunctionType;
import com.fujitsu.vdmj.tc.types.TCTypeList;

import java.io.File;
import java.io.IOException;
import java.util.*;


/* information what got from VDM++ specification file by syntax analyse with VDMJ */

public class InformationExtractor {

	private ConditionAndReturnValueList conditionAndReturnValueList;
	private IfElseExprSyntaxTree ifElseExprSyntaxTree;

    //argument  実引数
    //parameter 仮引数
    //今回扱うのは仮引数

    //file name and path
	private String vdmFileName;
	private String vdmFilePath;

	//function name
	private String functionName;

    private ArrayList<String> argumentTypes; //int, nat, nat1

	private ArrayList<String> parameters; //a, b, c

	//type of return value
	private String returnValue;


	private String ifExpressionBody;

    private HashMap<String, ArrayList<Object>> ifConditionBodies;
    //a parameter to ArrayList of if-conditions
	//ArrayList of ifConditions of each parameter
	//ifConditionBodies.get("a") : "4<a", "a<7"
	//ifConditionBodies.get("b") : "-3<b","b>100","0<b"
	//ifConditionBodies.get("c") : "c<10","3<c","c>-29"

	private ArrayList<String> ifConditionBodiesInCameForward;


	private HashMap<String, ArrayList<Object>> ifConditions;
	//a parameter to ArrayList of HashMaps that is parsed each if-expression
	//ArrayList of HashMap of parsed if-expr.
	//ifConditions.get("a") : 'HashMap of 4<a', 'HashMap of a<7'
	//ifConditions.get("b") : 'HashMap of -3<b', 'HashMap of b>100', 'HashMap of 0<b'
	//ifConditions.get("c") : 'HashMap of c<10', 'HashMap of 3<c', 'HashMap of c>-29'


	public InformationExtractor(String _vdmFilePath)
			throws LexException, ParserException, IOException {

        /* Initializing fields*/
		vdmFilePath = _vdmFilePath;
		File vdmFile = new File(vdmFilePath);
		vdmFileName = vdmFile.getName();

		/* variableName = init; example */
        argumentTypes = new ArrayList<>(); //int, nat, nat1

		//parameter information
		//a*b*c
        parameters = new ArrayList<>(); //a, b, c

		ifExpressionBody = "";
		ifConditionBodies = new HashMap<>();
		ifConditionBodiesInCameForward = new ArrayList<>();
		ifConditions = new HashMap<>();
        /*Done initializing fields*/

		LexTokenReader lexer = new LexTokenReader(vdmFile, Dialect.VDM_PP);
		DefinitionReader parser = new DefinitionReader(lexer);
		ASTDefinitionList astDefinitions = parser.readDefinitions();

		astDefinitions.forEach((ASTDefinition astDefinition ) -> {
			if(astDefinition.kind().equals("explicit function")) {
				TCExplicitFunctionDefinition tcFunctionDefinition = null;
				try{
					tcFunctionDefinition = ClassMapper.getInstance(TCDefinition.MAPPINGS).init().convert(astDefinition);
				} catch (Exception e) {
					e.printStackTrace();
				}
                assert tcFunctionDefinition != null;
                functionName = tcFunctionDefinition.name.getName();
				returnValue = tcFunctionDefinition.type.result.toString();
				//returnValue.replaceAll((,"").replaceAll(")","");
				TCFunctionType tcFunctionType = tcFunctionDefinition.type;
				TCTypeList tmp_argumentTypes = tcFunctionType.parameters;
				TCExpression tcExpression = tcFunctionDefinition.body;
				ifExpressionBody = tcExpression.toString();
				tmp_argumentTypes.forEach(e -> argumentTypes.add(e.toString()));

                countArgumentTypeNumByKind();

				try {
					ifElseExprSyntaxTree = new IfElseExprSyntaxTree(ifExpressionBody);
				} catch (ParserException | LexException | IOException e) {
					e.printStackTrace();
				}

				//parsing for parameters
				TCPatternListList tcPatternListList = tcFunctionDefinition.paramPatternList;
				TCPatternList tcPatternList = tcPatternListList.firstElement();
				for (TCPattern aTcPatternList : tcPatternList) {
					TCIdentifierPattern tcIdentifierPattern =
							(TCIdentifierPattern) aTcPatternList;
					String parameter = tcIdentifierPattern.toString();
					parameters.add(parameter);
				}

				parseIfConditions();

			}
        });

		ifElseExprSyntaxTree =
				new IfElseExprSyntaxTree(ifExpressionBody);

		conditionAndReturnValueList =
				new ConditionAndReturnValueList(ifElseExprSyntaxTree.root, this);

	}

	private void countArgumentTypeNumByKind() {
		argumentTypes.forEach(at -> {
			switch (at) {
				case "int":
					break;
				case "nat":
					break;
				case "nat1":
					break;
			}
		});
	}


	private void parseIfConditions() {
		List<String> ifElses = ifElseExprSyntaxTree.ifElses;

		for(int i=0; i<ifElses.size(); i++) {
			String element = ifElses.get(i);
			if(element.equals("if")) {
				element = ifElses.get(i + 1);
				ifConditionBodiesInCameForward.add(element);
			}
		}

		//initializing of collection instances of each parameter
		parameters.forEach(s -> {
			ifConditionBodies.put(s, new ArrayList<>());
			ifConditions.put(s, new ArrayList<>());
		});

		//parsing of each if-condition, and store in ifConditions
		ifConditionBodiesInCameForward.forEach(condition ->
				parameters.forEach(parameter -> {
					if (condition.contains(parameter)) {
						parse(condition, parameter);
					}
				}));
	}

	private void parse(String condition, String parameter) {
		ArrayList<Object> al = ifConditionBodies.get(parameter);
		al.add(condition);

		String operator = Util.getOperator(condition);
		int indexOfoperator = condition.indexOf(operator);
		HashMap<String, String> hm = new HashMap<>();
		hm.put("left", condition.substring(0, indexOfoperator));
		hm.put("operator", operator);

		//right-hand and surplus need branch depending on mod or other.
		if(operator.equals("mod")) {
			int indexOfEqual = condition.indexOf("=");
			hm.put("right", condition.substring(indexOfoperator+3, indexOfEqual));
			hm.put("surplus", condition.substring(indexOfEqual+1));
		} else {
			hm.put("right", condition.substring(indexOfoperator + operator.length()));
		}

		al = ifConditions.get(parameter);
		al.add(hm);
    }

	public IfElseExprSyntaxTree getIfElseExprSyntaxTree() {
    	return ifElseExprSyntaxTree;
	}
	public ArrayList<String> getParameters() {
		return parameters;
	}
	public ArrayList<String> getArgumentTypes() {
		return argumentTypes;
	}
	public HashMap<String, ArrayList<Object>> getIfConditions() {
		return ifConditions;
	}
	public ConditionAndReturnValueList getConditionAndReturnValueList() {
		return conditionAndReturnValueList;
	}
	public String getFunctionName() { return functionName; }
	public String getVdmFileName() { return vdmFileName; }
	public String getVdmFilePath() { return vdmFilePath; }
	public String getReturnValue() { return returnValue; }
}
