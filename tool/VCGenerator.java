package tool;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;

import java.util.List;

public class VCGenerator {

	private ProcedureDeclContext proc;
	private List<SimpleCParser.VarDeclContext> globals;
	
	public VCGenerator(ProcedureDeclContext proc, List<SimpleCParser.VarDeclContext> globals) {
		this.proc = proc;
		this.globals = globals;
	}
	
	public StringBuilder generateVC() {
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");

		SimpleCSMTVistor visitor = new SimpleCSMTVistor(globals);

		for( SimpleCParser.VarDeclContext ctx : globals ) {
			result.append(ctx.accept(visitor));
		}

		result.append(proc.accept(visitor));

		result.append("\n(check-sat)\n");
		result.append("(get-model)\n");

		return result;
	}


}
