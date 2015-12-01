package tool;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;
import tool.SMTs.SMT;

import java.util.List;
import java.util.Map;

public class VCGenerator {

	private SimpleCSMTVisitor visitor;
	private ProcedureDeclContext proc;
	private List<SimpleCParser.VarDeclContext> globals;
	private Map<String, ProcedureSummarisation> summarisationMap;

	private List<Integer> unwindingAssertionIds;

	
	public VCGenerator(SimpleCSMTVisitor visitor,
					   ProcedureDeclContext proc,
					   List<SimpleCParser.VarDeclContext> globals,
					   Map<String, ProcedureSummarisation> summarisationMap) {
		this.visitor = visitor;
		this.proc = proc;
		this.globals = globals;
		this.summarisationMap = summarisationMap;
	}

	public StringBuilder generateVC() {
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");

		for( SimpleCParser.VarDeclContext ctx : globals ) {
			result.append(ctx.accept(visitor));
		}

		SMT funcSMT = proc.accept(visitor);

		HoudiniLoopRunner loopRunner = new HoudiniLoopRunner(visitor, proc, summarisationMap, result.toString());

		if (!visitor.getAssertionToCandidateInvariantMap().isEmpty()) {
			result.append(loopRunner.eliminateCandidates(funcSMT));
		} else {
			result.append(funcSMT);
		}

		result.append("\n(check-sat)\n");
		result.append("(get-model)\n");
		result.append("(get-value (");

		for(int i = 0; i < loopRunner.getVisitor().assertionsSize(); i++) {
			result.append(" ").append(AssertionCollection.getAssertionName(i));
		}

		result.append("))\n");

		unwindingAssertionIds = loopRunner.getVisitor().getUnwindingAssertionIds();

		return result;
	}

	public List<Integer> getUnwindingAssertionIds() {
		return unwindingAssertionIds;
	}
}
