package comprehensiveLab
import std.console.*
import comprehensiveLab.lab1.*
import comprehensiveLab.lab2.*
import comprehensiveLab.lab3.*
import comprehensiveLab.lab4.*
import comprehensiveLab.testfiles.*
import std.collection.*
import std.io.SeekPosition
import std.fs.*
main(): Int64 {
    println("请输入要翻译的文件名");
    var fileName = Console.stdIn.readln() ?? 'defualt string';
    getCode(fileName);
    return 0
}
public func getCode(fileName:String){
    // 检查文件是否存在
    var filePath:Path = Path("./src/testfiles/"+fileName+".tny");
    if(!File.exists(filePath)) {
        println("输入文件不存在");
        return;
    }
    // 读取文件内容
    var fileContent:String = readFromFile("./src/testfiles/"+fileName+".tny");
    // 测试词法分析器
    var ts_sequence:ArrayList<object> =lexicalAnalysis(fileContent);
    // 创建TINY的文法
    create_TINY_Grammar();
    // 构架DFA以及LR(0)语法分析表
    create_TINY_LR0_DFA();
    // 测试生成中间代码(执行翻译)
    println("测试生成中间代码");
    translate_to_TMCODE(ts_sequence,"./src/testfiles/"+fileName+".tm");
}