package comprehensiveLab.lab3
import comprehensiveLab.lab1.*
import comprehensiveLab.lab2.*
public class graphObject{
    // 此对象的属性值只有名称 若是cc则是对应其字符 若是id则是代称符号
    var id:String;
    var grammarSymbol:GrammarSymbol;
    var graph:Graph;
    init(id:String,grammarSymbol:GrammarSymbol,graph:Graph){
        this.id = id;
        this.grammarSymbol = grammarSymbol;
        this.graph = graph;
    }
}