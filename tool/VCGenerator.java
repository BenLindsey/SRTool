package tool;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;

import java.util.List;
import java.util.Map;

public class VCGenerator {

	private ProcedureDeclContext proc;
	private List<SimpleCParser.VarDeclContext> globals;
	private Map<String, ProcedureSummarisation> summarisationMap;
	
	public VCGenerator(ProcedureDeclContext proc,
					   List<SimpleCParser.VarDeclContext> globals,
					   Map<String, ProcedureSummarisation> summarisationMap) {
		this.proc = proc;
		this.globals = globals;
		this.summarisationMap = summarisationMap;

		// The static variables in the Variables class mean that we use the
		// wrong ids/declarations for global variables, so we need to reset these
		// across procedures.
		Variables.refresh();
	}
	
	public StringBuilder generateVC() {
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");

		SimpleCSMTVisitor visitor = new SimpleCSMTVisitor(summarisationMap);

		for( SimpleCParser.VarDeclContext ctx : globals ) {
			result.append(ctx.accept(visitor));
		}

		result.append(proc.accept(visitor));

		result.append("\n(check-sat)\n");
		result.append("(get-model)\n");

		return result;
	}


}
