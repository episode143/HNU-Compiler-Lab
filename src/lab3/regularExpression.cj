package comprehensiveLab.lab3
import comprehensiveLab.lab1.*
import comprehensiveLab.lab2.*
import std.collection.*
public class regularExpressionCompiler{
    // 针对正则表达式的对象栈
    var regularObjectStack:ArrayList<graphObject>;
    // 映射id与其对应的graph
    var unmap:HashMap<String, Graph>;
    // 最终得到的DFA
    var resultDFA:Graph;
    // 正则表达式的终结符的词法DFA
    var regularLexicalDFA:Graph;
    init(){
        this.regularObjectStack = ArrayList<graphObject>();
        this.unmap = HashMap<String, Graph>();
        this.resultDFA = Graph(0,0,ArrayList<Edge>(),ArrayList<State>());
        this.regularLexicalDFA = Graph(0,0,ArrayList<Edge>(),ArrayList<State>());
    }
    // 创建小写字符集合
    private func createLowerLetter():Int32{
        var a:Rune = 'a';
        var z:Rune = 'z';
        var charSetLetterLower:Int32 = range(a,z);
        return charSetLetterLower;
    }
    // 创建大写字符集合
    private func createUpperLetter():Int32{
        var A:Rune = 'A';
        var Z:Rune = 'Z';
        var charSetLetterUpper:Int32 = range(A,Z);
        return charSetLetterUpper;
    }
    // 创建数字集合
    private func createDigit():Int32{
        var num0:Rune = '0';
        var num9:Rune = '9';
        var charSetDigit:Int32 = range(num0,num9);
        return charSetDigit;
    }
    // 创建关于正则表达式的词法分析DFA
    public func create_Lexical_Of_Regular_Expression(){
        // ================== 基础字符集定义 ==================
        // 创建小写字母集 a-z
        var charSetLower = this.createLowerLetter() 
        // 创建大写字母集 A-Z
        var charSetUpper = this.createUpperLetter()
        // 创建数字集 0-9
        var charSetDigit = this.createDigit()
        // 合并字母集
        var charSetLetter = union(charSetLower, charSetUpper)
        // 字母数字集
        var charSetLetterDigit = union(charSetLetter, charSetDigit)

        // ================== 特殊终结符NFA构建 ==================
        // 1. cc（单个字母）
        var graph_cc = generateBasicNFA("CHARSET", charSetLetter, "CC")

        // 2. crlf（四个字符顺序连接）
        var c:Rune = 'c';
        var graph_c = generateBasicNFA("CHAR", range(c,c), "")
        var r:Rune = 'r';
        var graph_r = generateBasicNFA("CHAR", range(r,r), "")
        var l:Rune = 'l';
        var graph_l = generateBasicNFA("CHAR", range(l,l), "")
        var f:Rune = 'f';
        var graph_f = generateBasicNFA("CHAR", range(f,f), "CRLF")
        var graph_crlf = product(graph_c, product(graph_r, product(graph_l, graph_f)))

        // 3. id（字母数字正闭包）
        var graph_letter = generateBasicNFA("CHARSET", charSetLetter, "") 
        var graph_digit = generateBasicNFA("CHARSET", charSetDigit, "")
        var graph_id = generateBasicNFA("CHARSET",charSetLetterDigit,"ID")
        graph_id = plusClosure(graph_id.copyGraph());

        // 4. ->（两个字符连接）
        var arrow0:Rune = '-'
        var arrow1:Rune = '>'
        var graph_minus = generateBasicNFA("CHAR", range(arrow0,arrow0), "")
        var graph_gt = generateBasicNFA("CHAR", range(arrow1,arrow1), "ARROW")
        var graph_arrow = product(graph_minus, graph_gt)

        // 5. 单个字符终结符
        var at:Rune = '@';
        var graph_at = generateBasicNFA("CHAR", range(at,at), "AT")      // @
        var or:Rune = '|';
        var graph_pipe = generateBasicNFA("CHAR", range(or,or), "PIPE")  // |
        var plus:Rune = '+'
        var graph_plus = generateBasicNFA("CHAR", range(plus,plus), "PLUS")  // +
        var star:Rune = '*'
        var graph_star = generateBasicNFA("CHAR", range(star,star), "STAR")  // *
        var quest:Rune = '?'
        var graph_quest = generateBasicNFA("CHAR", range(quest,quest), "QUEST")// ?
        var left_bracket:Rune ='('
        var graph_lparen = generateBasicNFA("CHAR", range(left_bracket,left_bracket), "LPAREN") // (
        var right_backet:Rune = ')'
        var graph_rparen = generateBasicNFA("CHAR", range(right_backet,right_backet), "RPAREN") // )

        // ================== 合并所有NFA ==================
        var finalNFA = union(
            union(graph_cc, graph_crlf),
            union(
                union(graph_id, graph_arrow),
                union(
                    union(graph_at, graph_pipe),
                    union(
                        union(graph_plus, graph_star),
                        union(
                            union(graph_quest, graph_lparen),
                            graph_rparen
                        )
                    )
                )
            )
        )

        this.regularLexicalDFA = finalNFA.NFA_to_DFA();
    }

    // 创建关于正则表达式的文法符以及产生式和LR(0)语法分析表
    public func create_GrammarSymbol_Of_Regular_expression(){
        // 定义非终结符和终结符
        // 创建非终结符 P
        var name_P: String = "P"
        var pProductionTable_P = ArrayList<Production>()
        var numOfProduction_P = 1
        var pFirstSet_P = HashSet<TerminalSymbol>()
        var pFollowSet_P = HashSet<TerminalSymbol>()
        var pDependentSetInFollow_P = HashSet<NonTerminalSymbol>()
        var nts_P: NonTerminalSymbol = NonTerminalSymbol(
            name_P, non_s, pProductionTable_P, numOfProduction_P, 
            pFirstSet_P, pFollowSet_P, pDependentSetInFollow_P
        )
        all_NonTerminalSymbol_Set.append(nts_P)
        getNTS.put(name_P, nts_P)

        // 创建非终结符 S
        var name_S: String = "S"
        var pProductionTable_S = ArrayList<Production>()
        var numOfProduction_S = 1
        var pFirstSet_S = HashSet<TerminalSymbol>()
        var pFollowSet_S = HashSet<TerminalSymbol>()
        var pDependentSetInFollow_S = HashSet<NonTerminalSymbol>()
        var nts_S: NonTerminalSymbol = NonTerminalSymbol(
            name_S, non_s, pProductionTable_S, numOfProduction_S, 
            pFirstSet_S, pFollowSet_S, pDependentSetInFollow_S
        )
        all_NonTerminalSymbol_Set.append(nts_S)
        getNTS.put(name_S, nts_S)

        // 创建非终结符 E
        var name_E: String = "E"
        var pProductionTable_E = ArrayList<Production>()
        var numOfProduction_E = 1
        var pFirstSet_E = HashSet<TerminalSymbol>()
        var pFollowSet_E = HashSet<TerminalSymbol>()
        var pDependentSetInFollow_E = HashSet<NonTerminalSymbol>()
        var nts_E: NonTerminalSymbol = NonTerminalSymbol(
            name_E, non_s, pProductionTable_E, numOfProduction_E, 
            pFirstSet_E, pFollowSet_E, pDependentSetInFollow_E
        )
        all_NonTerminalSymbol_Set.append(nts_E)
        getNTS.put(name_E, nts_E)

        // 创建终结符 id
        var name_id: String = "id"
        var lexeme_id: String = "IDENTIFIER"
        var ts_id = TerminalSymbol(name_id, ter_s, lexeme_id)
        getTS.put(name_id, ts_id)

        // 创建终结符 ->
        var name_arrow: String = "->"
        var lexeme_arrow: String = "RIGHT_ARROW"
        var ts_arrow = TerminalSymbol(name_arrow, ter_s, lexeme_arrow)
        getTS.put(name_arrow, ts_arrow)

        // 创建终结符 crlf
        var name_crlf: String = "crlf"
        var lexeme_crlf: String = "NEWLINE"
        var ts_crlf = TerminalSymbol(name_crlf, ter_s, lexeme_crlf)
        getTS.put(name_crlf, ts_crlf)

        // 创建终结符 @
        var name_at: String = "@"
        var lexeme_at: String = "AT_SYMBOL"
        var ts_at = TerminalSymbol(name_at, ter_s, lexeme_at)
        getTS.put(name_at, ts_at)

        // 创建终结符 ~
        var name_tilde: String = "~"
        var lexeme_tilde: String = "TILDE"
        var ts_tilde = TerminalSymbol(name_tilde, ter_s, lexeme_tilde)
        getTS.put(name_tilde, ts_tilde)

        // 创建终结符 -
        var name_minus: String = "-"
        var lexeme_minus: String = "MINUS"
        var ts_minus = TerminalSymbol(name_minus, ter_s, lexeme_minus)
        getTS.put(name_minus, ts_minus)

        // 创建终结符 |
        var name_pipe: String = "|"
        var lexeme_pipe: String = "PIPE"
        var ts_pipe = TerminalSymbol(name_pipe, ter_s, lexeme_pipe)
        getTS.put(name_pipe, ts_pipe)

        // 创建终结符 **
        var name_double_star: String = "**"
        var lexeme_double_star: String = "DOUBLE_STAR"
        var ts_double_star = TerminalSymbol(name_double_star, ter_s, lexeme_double_star)
        getTS.put(name_double_star, ts_double_star)

        // 创建终结符 *
        var name_star: String = "*"
        var lexeme_star: String = "STAR"
        var ts_star = TerminalSymbol(name_star, ter_s, lexeme_star)
        getTS.put(name_star, ts_star)

        // 创建终结符 +
        var name_plus: String = "+"
        var lexeme_plus: String = "PLUS"
        var ts_plus = TerminalSymbol(name_plus, ter_s, lexeme_plus)
        getTS.put(name_plus, ts_plus)

        // 创建终结符 ?
        var name_question: String = "?"
        var lexeme_question: String = "QUESTION"
        var ts_question = TerminalSymbol(name_question, ter_s, lexeme_question)
        getTS.put(name_question, ts_question)

        // 创建终结符 (
        var name_left_paren: String = "("
        var lexeme_left_paren: String = "LEFT_PAREN"
        var ts_left_paren = TerminalSymbol(name_left_paren, ter_s, lexeme_left_paren)
        getTS.put(name_left_paren, ts_left_paren)

        // 创建终结符 )
        var name_right_paren: String = ")"
        var lexeme_right_paren: String = "RIGHT_PAREN"
        var ts_right_paren = TerminalSymbol(name_right_paren, ter_s, lexeme_right_paren)
        getTS.put(name_right_paren, ts_right_paren)

        // 创建终结符 ·
        var name_dot: String = "·"
        var lexeme_dot: String = "DOT"
        var ts_dot = TerminalSymbol(name_dot, ter_s, lexeme_dot)
        getTS.put(name_dot, ts_dot)

        // 创建终结符 cc
        var name_cc: String = "cc"
        var lexeme_cc: String = "CC_SYMBOL"
        var ts_cc = TerminalSymbol(name_cc, ter_s, lexeme_cc)
        getTS.put(name_cc, ts_cc)

        // 创建终结符 #
        var name_hash: String = "#"
        var lexeme_hash: String = "HASH"
        var ts_hash = TerminalSymbol(name_hash, ter_s, lexeme_hash)
        getTS.put(name_hash, ts_hash)

        // 辅助的文法符创建
        // 创建非终结符 S1
        var name_S1: String = "S1"
        var pProductionTable_S1 = ArrayList<Production>()
        var numOfProduction_S1 = 1
        var pFirstSet_S1 = HashSet<TerminalSymbol>()
        var pFollowSet_S1 = HashSet<TerminalSymbol>()
        var pDependentSetInFollow_S1 = HashSet<NonTerminalSymbol>()
        var nts_S1: NonTerminalSymbol = NonTerminalSymbol(
            name_S1, non_s, pProductionTable_S1, numOfProduction_S1, 
            pFirstSet_S1, pFollowSet_S1, pDependentSetInFollow_S1
        )
        all_NonTerminalSymbol_Set.append(nts_S1)
        getNTS.put(name_S1, nts_S1)

        // 创建非终结符 S2
        var name_S2: String = "S2"
        var pProductionTable_S2 = ArrayList<Production>()
        var numOfProduction_S2 = 1
        var pFirstSet_S2 = HashSet<TerminalSymbol>()
        var pFollowSet_S2 = HashSet<TerminalSymbol>()
        var pDependentSetInFollow_S2 = HashSet<NonTerminalSymbol>()
        var nts_S2: NonTerminalSymbol = NonTerminalSymbol(
            name_S2, non_s, pProductionTable_S2, numOfProduction_S2, 
            pFirstSet_S2, pFollowSet_S2, pDependentSetInFollow_S2
        )
        all_NonTerminalSymbol_Set.append(nts_S2)
        getNTS.put(name_S2, nts_S2)

        // 创建非终结符 E1
        var name_E1: String = "E1"
        var pProductionTable_E1 = ArrayList<Production>()
        var numOfProduction_E1 = 1
        var pFirstSet_E1 = HashSet<TerminalSymbol>()
        var pFollowSet_E1 = HashSet<TerminalSymbol>()
        var pDependentSetInFollow_E1 = HashSet<NonTerminalSymbol>()
        var nts_E1: NonTerminalSymbol = NonTerminalSymbol(
            name_E1, non_s, pProductionTable_E1, numOfProduction_E1, 
            pFirstSet_E1, pFollowSet_E1, pDependentSetInFollow_E1
        )
        all_NonTerminalSymbol_Set.append(nts_E1)
        getNTS.put(name_E1, nts_E1)

        // 创建非终结符 E2
        var name_E2: String = "E2"
        var pProductionTable_E2 = ArrayList<Production>()
        var numOfProduction_E2 = 1
        var pFirstSet_E2 = HashSet<TerminalSymbol>()
        var pFollowSet_E2 = HashSet<TerminalSymbol>()
        var pDependentSetInFollow_E2 = HashSet<NonTerminalSymbol>()
        var nts_E2: NonTerminalSymbol = NonTerminalSymbol(
            name_E2, non_s, pProductionTable_E2, numOfProduction_E2, 
            pFirstSet_E2, pFollowSet_E2, pDependentSetInFollow_E2
        )
        all_NonTerminalSymbol_Set.append(nts_E2)
        getNTS.put(name_E2, nts_E2)

        // 创建终结符 $
        var name_dollar: String = "$"
        var lexeme_dollar: String = "END_MARKER"
        var ts_dollar = TerminalSymbol(name_dollar, ter_s, lexeme_dollar)
        getTS.put(name_dollar, ts_dollar)

        // 创建产生式
        // 产生式 P → S $
        var production_P_id: Int64 = 1
        var production_P_size: Int64 = 2
        var production_P_sTable: ArrayList<GrammarSymbol> = ArrayList<GrammarSymbol>()
        var production_P_fSet: HashSet<TerminalSymbol> = HashSet<TerminalSymbol>()
        var production_P: Production = Production(production_P_id, production_P_size, production_P_sTable, production_P_fSet)

        production_P.pBodySymbolTable.append(nts_S)   // 非终结符 S
        production_P.pBodySymbolTable.append(ts_dollar) // 终结符 $

        // 将产生式添加到 P 的产生式表中
        nts_P.pProductionTable.append(production_P)
        nts_P.numOfProduction = 1
        all_Production_Set.append(production_P)
        relativeId.append(0)

        // 产生式 S → S1 S2
        var production_S1_id: Int64 = 2
        var production_S1_size: Int64 = 2
        var production_S1_sTable: ArrayList<GrammarSymbol> = ArrayList<GrammarSymbol>()
        var production_S1_fSet: HashSet<TerminalSymbol> = HashSet<TerminalSymbol>()
        var production_S1: Production = Production(production_S1_id, production_S1_size, production_S1_sTable, production_S1_fSet)

        production_S1.pBodySymbolTable.append(nts_S1) // 非终结符 S1
        production_S1.pBodySymbolTable.append(nts_S2) // 非终结符 S2

        nts_S.pProductionTable.append(production_S1)
        all_Production_Set.append(production_S1)
        relativeId.append(0)

        // 产生式 S → id → E crlf
        var production_S2_id: Int64 = 3
        var production_S2_size: Int64 = 4
        var production_S2_sTable: ArrayList<GrammarSymbol> = ArrayList<GrammarSymbol>()
        var production_S2_fSet: HashSet<TerminalSymbol> = HashSet<TerminalSymbol>()
        var production_S2: Production = Production(production_S2_id, production_S2_size, production_S2_sTable, production_S2_fSet)

        production_S2.pBodySymbolTable.append(ts_id)      // id
        production_S2.pBodySymbolTable.append(ts_arrow)   // ->
        production_S2.pBodySymbolTable.append(nts_E)      // E
        production_S2.pBodySymbolTable.append(ts_crlf)    // crlf

        nts_S.pProductionTable.append(production_S2)
        all_Production_Set.append(production_S2)
        relativeId.append(0)

        // 产生式 S → @S1
        var production_S3_id: Int64 = 4
        var production_S3_size: Int64 = 2
        var production_S3_sTable: ArrayList<GrammarSymbol> = ArrayList<GrammarSymbol>()
        var production_S3_fSet: HashSet<TerminalSymbol> = HashSet<TerminalSymbol>()
        var production_S3: Production = Production(production_S3_id, production_S3_size, production_S3_sTable, production_S3_fSet)

        production_S3.pBodySymbolTable.append(ts_at)   // @
        production_S3.pBodySymbolTable.append(nts_S1)  // S1

        nts_S.pProductionTable.append(production_S3)
        all_Production_Set.append(production_S3)
        relativeId.append(0)

        // 产生式 E → E1 | E2
        var production_E_id: Int64 = 5
        var production_E_size: Int64 = 3  // 符号数：E1, |, E2
        var production_E_sTable: ArrayList<GrammarSymbol> = ArrayList<GrammarSymbol>()
        var production_E_fSet: HashSet<TerminalSymbol> = HashSet<TerminalSymbol>()
        var production_E: Production = Production(production_E_id, production_E_size, production_E_sTable, production_E_fSet)

        production_E.pBodySymbolTable.append(nts_E1)   // 非终结符 E1
        production_E.pBodySymbolTable.append(ts_pipe)  // 终结符 |（逻辑或符号）
        production_E.pBodySymbolTable.append(nts_E2)   // 非终结符 E2

        nts_E.pProductionTable.append(production_E)
        nts_E.numOfProduction = 1  // 假设这是 E 的第一个产生式，根据实际调整
        all_Production_Set.append(production_E)
        relativeId.append(0)

        // 产生式 E → E1 · E2
        var production_E6_id: Int64 = 6
        var production_E6_size: Int64 = 3
        var production_E6_sTable = ArrayList<GrammarSymbol>()
        var production_E6 = Production(production_E6_id, production_E6_size, production_E6_sTable, HashSet())
        production_E6.pBodySymbolTable.append(nts_E1)
        production_E6.pBodySymbolTable.append(ts_dot)
        production_E6.pBodySymbolTable.append(nts_E2)
        nts_E.pProductionTable.append(production_E6)
        all_Production_Set.append(production_E6)

        // 产生式 E → E1 E2
        var production_E7_id: Int64 = 7
        var production_E7 = Production(production_E7_id, 2, ArrayList(), HashSet())
        production_E7.pBodySymbolTable.append(nts_E1)
        production_E7.pBodySymbolTable.append(nts_E2)
        nts_E.pProductionTable.append(production_E7)
        all_Production_Set.append(production_E7)

        // 产生式 E → E1 +
        var production_E8_id: Int64 = 8
        var production_E8 = Production(production_E8_id, 2, ArrayList(), HashSet())
        production_E8.pBodySymbolTable.append(nts_E1)
        production_E8.pBodySymbolTable.append(ts_plus)
        nts_E.pProductionTable.append(production_E8)
        all_Production_Set.append(production_E8)

        // 产生式 E → E1 *
        var production_E9_id: Int64 = 9
        var production_E9 = Production(production_E9_id, 2, ArrayList(), HashSet())
        production_E9.pBodySymbolTable.append(nts_E1)
        production_E9.pBodySymbolTable.append(ts_star) 
        nts_E.pProductionTable.append(production_E9)
        all_Production_Set.append(production_E9)

        // 产生式 E → E1 ?
        var production_E10_id: Int64 = 10
        var production_E10 = Production(production_E10_id, 2, ArrayList(), HashSet())
        production_E10.pBodySymbolTable.append(nts_E1)
        production_E10.pBodySymbolTable.append(ts_question)  // 使用已有终结符

        nts_E.pProductionTable.append(production_E10)
        all_Production_Set.append(production_E10)

        // 产生式 E → (E1)
        var production_E11_id: Int64 = 11
        var production_E11 = Production(production_E11_id, 3, ArrayList(), HashSet())
        production_E11.pBodySymbolTable.append(ts_left_paren)
        production_E11.pBodySymbolTable.append(nts_E1)
        production_E11.pBodySymbolTable.append(ts_right_paren)
        nts_E.pProductionTable.append(production_E11)
        all_Production_Set.append(production_E11)

        // 产生式 E → id
        var production_E12_id: Int64 = 12
        var production_E12 = Production(production_E12_id, 1, ArrayList(), HashSet())
        production_E12.pBodySymbolTable.append(ts_id)
        nts_E.pProductionTable.append(production_E12)
        all_Production_Set.append(production_E12)

        // 产生式 E → CC（关联用户已创建的cc终结符）
        var production_E13_id: Int64 = 13
        var production_E13 = Production(production_E13_id, 1, ArrayList(), HashSet())
        production_E13.pBodySymbolTable.append(ts_cc)  // 使用用户定义的cc符号
        nts_E.pProductionTable.append(production_E13)
        all_Production_Set.append(production_E13)

        get_All_NTS_FIRST();

        get_All_Production_FIRST();

        get_All_NTS_FOLLOW();
    }

    // 创建正则表达式的LR(0)的DFA以及其LR(0)语法分析表
    public func create_Reuglar_Expression_LR0_DFA(){
        // 创建核心项 P -> S $
        var I0_0_item:LR0Item = LR0Item(all_NonTerminalSymbol_Set[0],all_Production_Set[0],0,"CORE");
        // 创建I0（只含核心项）
        var I0:ItemSet = ItemSet(0,ArrayList<LR0Item>());
        I0.pItemTable.append(I0_0_item);
        pItemSetTable.append(I0);
        // 生成整个LR(0)项集集合
        getClosure(I0);
        // 得到LR语法分析表
        exhaustTransition(I0);
        create_LR1_Analysis_Table();
    }

    // 执行翻译将正则表达式序列翻译成对应的DFA图
    public func translateToGraph(ts_sequence:ArrayList<graphObject>){
        var pStateStack:ArrayList<Int64> = ArrayList<Int64>();
            pStateStack.append(0);
            var currentLexeme_pos:Int64 = 0;
            while(!pStateStack.isEmpty()) {
                var currSize:Int64 = pStateStack.size;
                // 求出当前状态
                var currentState = pStateStack[currSize-1];
                if(pActionCellTable[pItemSetTable[currentState]].contains(getTS[ts_sequence[currentLexeme_pos].grammarSymbol.name])) {
                    var indicator:ActionCell = pActionCellTable[pItemSetTable[currentState]][getTS[ts_sequence[currentLexeme_pos].grammarSymbol.name]];
                    if(indicator.actionType == "s") {
                        pStateStack.append(indicator.actionId);
                        // 由于正则表达式的翻译过程中只有规约时才有动作，所以shiftAction没有相对应的动作
                        //*shiftAction
                        // 添加进对象栈
                        regularObjectStack.append(ts_sequence[currentLexeme_pos]);
                    }
                    else if(indicator.actionType == "r") {
                        var production:Production = all_Production_Set[indicator.actionId];
                        // 根据规约编号来执行翻译动作
                        this.regularTranslateAction(indicator.actionId);
                        var times:Int64 = production.pBodySymbolTable.size;
                        while(times!=0) {
                            times--;
                            var currTail = pStateStack.size;
                            if(currTail == 0) {
                                println("输入字符串有语法错误");
                                return;
                            }
                            pStateStack.remove(currTail-1);
                        }
                        var currTail:Int64 = pStateStack.size;
                        currentState = pStateStack[currTail-1];
                        var nextState:Int64 = pGOTOCellTable[pItemSetTable[currentState]][all_NonTerminalSymbol_Set[relativeId[indicator.actionId]]].nextStateId;
                        pStateStack.append(nextState);
                    }
                    else if(indicator.actionType == "acc") {
                        println("语法分析完成,语法正确！");
                        // 将最后的NFA转化为DFA
                        this.getResultDFA();
                        return;
                    }
                }
                else {
                    println("输入字符串有语法错误");
                    return;
                }
            }
    }

    // 翻译动作
    public func regularTranslateAction(actionId:Int64) {
        match(actionId) {
            case 0 => this.getResultDFA();
            case 1 => this.regularTranslate1();
            case 2 => this.regularTranslate2();
            case 3 => this.regularTranslate3();
            case 4 => this.regularTranslate4();
            case 5 => this.regularTranslate5();
            case 6 => this.regularTranslate6();
            case 7 => this.regularTranslate7();
            case 8 => this.regularTranslate8();
            case 9 => this.regularTranslate9();
            case 10 => this.regularTranslate10();
            case 11 => this.regularTranslate11();
            case 12 => this.regularTranslate12();
            case _ => this.getResultDFA();
        }
    }
    
    // 弹出对象栈的最后一个对象
    public func regularRemoveEnd():graphObject {
        var endIndex:Int64 = this.regularObjectStack.size-1;
        var target:graphObject = this.regularObjectStack[endIndex];
        this.regularObjectStack.remove(endIndex);
        return target;
    }

    // 结果——得到最终的DFA

    // P -> S $
    public func getResultDFA(){
        var shut = regularRemoveEnd();
        var S = regularRemoveEnd();
        // 将S的nfa转化为DFA赋予最终正则表达式的结果——词法DFA图(用于词法分析得到token),后续可以使用这个DFA执行词法分析
        this.resultDFA = S.graph.NFA_to_DFA();
    }
    
    // S -> S1 S2
    public func regularTranslate1(){
        var S2 = regularRemoveEnd();
        var S1 = regularRemoveEnd();
        // S.pNFA = S2.pNFA
        var S = graphObject(S2.id,S2.grammarSymbol,S2.graph);
        this.regularObjectStack.append(S);
    }

    // S -> id -> E crlf
    public func regularTranslate2(){
        var crlf = regularRemoveEnd();
        var E = regularRemoveEnd();
        var arrow = regularRemoveEnd();
        var ID = regularRemoveEnd();
        // S.pNFA = S2.pNFA S.var = id.var
        var S = graphObject(ID.id,E.grammarSymbol,E.graph);
        // map(id.var,E.pNFA)
        unmap.put(S.id,S.graph);
        this.regularObjectStack.append(S);
    }

    // S -> @ S1
    public func regularTranslate3(){
        var S1 = regularRemoveEnd()
        var at = regularRemoveEnd();
        // setCategory( S1.pNFA, S1.var)
        var endState = S1.graph.pStateTable.size-1;
        S1.graph.pStateTable[endState].LexemeCategory = S1.id;
        // S.pNFA = S1.pNFA;
        var S = graphObject(S1.id,S1.grammarSymbol,S1.graph);
        this.regularObjectStack.append(S);
    }

    // E -> E1|E2 
    public func regularTranslate4(){
        var E2 = regularRemoveEnd();
        var or = regularRemoveEnd();
        var E1 = regularRemoveEnd();
        // E.pNFA =union(E1.pNFA, E2.pNFA)
        var tempGraph:Graph = union(E1.graph,E2.graph);
        var E = graphObject("${E1.id} | ${E2.id}",E1.grammarSymbol,tempGraph);
        this.regularObjectStack.append(E);
    }

    // E -> E1 · E2
    public func regularTranslate5(){
        var E2 = regularRemoveEnd();
        var dot = regularRemoveEnd();
        var E1 = regularRemoveEnd();
        // E.pNFA =product(E1.pNFA, E2.pNFA)
        var tempGraph:Graph = product(E1.graph,E2.graph);
        var E = graphObject("${E1.id} · ${E2.id}",E1.grammarSymbol,tempGraph);
        this.regularObjectStack.append(E);
    }

    // E -> E1 E2
    public func regularTranslate6(){
        var E2 = regularRemoveEnd();
        var E1 = regularRemoveEnd();
        // E.pNFA =product(E1.pNFA, E2.pNFA)
        var tempGraph:Graph = product(E1.graph,E2.graph);
        var E = graphObject("${E1.id} · ${E2.id}",E1.grammarSymbol,tempGraph);
        this.regularObjectStack.append(E);
    }

    // E -> E1+
    public func regularTranslate7(){
        var plus = regularRemoveEnd();
        var E1 = regularRemoveEnd();
        // E.pNFA =plusClosure(E1.pNFA)
        var tempGraph:Graph = plusClosure(E1.graph);
        var E = graphObject(E1.id,E1.grammarSymbol,tempGraph);
        this.regularObjectStack.append(E);
    }

    // E -> E1*
    public func regularTranslate8(){
        var star = regularRemoveEnd();
        var E1 = regularRemoveEnd();
        // E.pNFA =closure(E1.pNFA)
        var tempGraph:Graph = closure(E1.graph);
        var E = graphObject(E1.id,E1.grammarSymbol,tempGraph);
        this.regularObjectStack.append(E);
    }

    // E -> E1? 
    public func regularTranslate9(){
        var question = regularRemoveEnd();
        var E1 = regularRemoveEnd();
        // E.pNFA =closure(E1.pNFA)
        var tempGraph:Graph = zeroOrOne(E1.graph);
        var E = graphObject(E1.id,E1.grammarSymbol,tempGraph);
        this.regularObjectStack.append(E);
    }

    // E -> (E1)
    public func regularTranslate10(){
        var right = regularRemoveEnd();
        var E1 = regularRemoveEnd();
        var left = regularRemoveEnd();
        // E.pNFA =E1.pNFA
        var E = graphObject(E1.id,E1.grammarSymbol,E1.graph);
        this.regularObjectStack.append(E);
    }

    // E -> id
    public func regularTranslate11(){
        var ID = regularRemoveEnd();
        var tempGS:GrammarSymbol = GrammarSymbol("${ID.id}","NONTERMINAL");
        var E = graphObject(ID.id,tempGS,unmap[ID.id]);
        this.regularObjectStack.append(E);
    }

    // E -> cc
    public func regularTranslate12(){
        var cc =  regularRemoveEnd();
        // E.pNFA =generateBasicNFA( cc.var )
        var driveId:Int32 = range(Rune(cc.id[0]),Rune(cc.id[0]));
        var tempEdge:Edge = Edge(0,1,driveId,"CHAR");
        var tempGraph:Graph = Graph(0,2,ArrayList<Edge>(),ArrayList<State>());
        tempGraph.pEdgeTable.append(tempEdge);
        tempGraph.pStateTable.append(State(0,"UNMATCH",""));
        tempGraph.pStateTable.append(State(0,"MATCH","cc"));
        var E = graphObject(cc.id,cc.grammarSymbol,tempGraph)
        this.regularObjectStack.append(E);
    }
}
