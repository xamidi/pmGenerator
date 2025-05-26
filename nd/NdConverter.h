#ifndef XAMIDI_ND_NDCONVERTER_H
#define XAMIDI_ND_NDCONVERTER_H

#include <string>

namespace xamidi {
namespace nd {

struct NdConverter {
	// Convert a propositional natural deduction proof without premises in FitchFX format (https://github.com/mrieppel/FitchFX ; e.g. exported from https://mrieppel.github.io/FitchFX/)
	// to a condensed detachment proof in a specified Hilbert system, i.e. read a natural deduction proof from a file, decontextualize, then and print its proof summary.
	// Translations can be based on proof data provided by the user in another proof summary of the target system. Only basic (i.e. non-derived) FitchFX rules are supported.
	// NOTE: When not using the default axioms, minimal input requirements are proofs for (A1) ψ→(φ→ψ) (i.e. CpCqp) and (A2) (ψ→(φ→χ))→((ψ→φ)→(ψ→χ)) (i.e. CCpCqrCCpqCpr).
	//       These enable support for rules →I ("conditional introduction") and →E ("conditional elimination"), but cannot prove any derivation containing negation.
	//       When a proof for (A3) (¬ψ→¬φ)→(φ→ψ) (i.e. CCNpNqCqp) is also provided, all rules are automatically supported, as long as 'purity mode' is enabled by the user:
	//       In this case, rules containing any operators other than "→" (i.e. C) and "¬" (i.e. N) are expressed in term of pure C-N-formulas, using the following aliases.
	//         (∧) (ψ∧φ):=¬(ψ→¬φ)          (i.e. Kpq:=NCpNq)
	//         (∨) (ψ∨φ):=(¬ψ→φ)           (i.e. Apq:=CNpq)
	//         (↔) (ψ↔φ):=¬((ψ→φ)→¬(φ→ψ))  (i.e. Epq:=NCCpqNCqp)
	//         (⊥) ⊥:=¬(ψ→ψ)               (i.e. O:=NCpp)
	//       Inserted natural deduction proofs are transformed by the parsing algorithm in a corresponding manner.
	//       Note that when 'purity mode' is disabled, a used Hilbert system requires its axioms to define all used operators, and the user must enable used rules
	//       by providing proofs for rule-enabling theorems that use such operators. There is the option to enable different proofs (e.g. shorter; or more proofs
	//       when (A3) was not given or 'purity mode' is disabled) by providing proofs for the following theorems (including proper schemas thereof):
	//       ‖ ID ‖ Theorem       | Enables ‖ Pure Variant      | Enables    | Default Length                  | Default Proof & Theorem                                                                                                                      ‖
	//       ‖ -- ‖ ------------- | ------- ‖ ----------------- | ---------- | ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- ‖
	//       ‖  0 ‖ CpCqKpq       | ∧I      ‖ CpCqNCpNq         | ∧I, ↔I     |  31 ; 15(D)+ 7(A1)+ 6(A2)+3(A3) | DD2D13DD2D1D2DD2DD2D13DD2D13111:CpCqNCpNq                                                                                                    ‖
	//       ‖  1 ‖ CpCqKqp       | ∧I      ‖ CpCqNCqNp         | ∧I, ↔I     |  39 ; 19(D)+ 9(A1)+ 8(A2)+3(A3) | DD2D1D2DD2D13DD2D1D2DD2DD2D13DD2D131111:CpCqNCqNp                                                                                            ‖
	//       ‖  2 ‖ CKpqp         | ∧E-l    ‖ CNCpNqp           | ∧E-l, ↔E-l |  33 ; 16(D)+ 7(A1)+ 5(A2)+5(A3) | D3DD2D1D3DD2DD2D13DD2D1311DD2D131:CNCpqp                                                                                                     ‖
	//       ‖  3 ‖ CKpqq         | ∧E-r    ‖ CNCpNqq           | ∧E-r, ↔E-r |  27 ; 13(D)+ 6(A1)+ 4(A2)+4(A3) | D3DD2D1D3DD2DD2D13DD2D13111:CNCpNqq                                                                                                          ‖
	//       ‖  4 ‖ CpApq         | ∨I-l    ‖ CpCNpq            | ∨I-l, ¬E   |  15 ;  7(D)+ 4(A1)+ 3(A2)+1(A3) | DD2D1D2DD2D1311:CpCNpq                                                                                                                       ‖
	//       ‖  5 ‖ CpAqp         | ∨I-r    ‖ CpCNqp            | ∨I-r       |   1 ;        1(A1)              | 1:CpCqp                                                                                                                                      ‖
	//       ‖  6 ‖ CApqCCprCCqrr | ∨E      ‖ CCNpqCCprCCqrr    | ∨E         | 125 ; 62(D)+29(A1)+28(A2)+6(A3) | DD2D1DD2D1DD2D1DD22D11DD2D112D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D1D2DD2D1211:CCNpqCCprCCqrr ‖
	//       ‖  7 ‖ CApqCCqrCCprr | ∨E      ‖ CCNpqCCqrCCprr    | ∨E         | 101 ; 50(D)+23(A1)+22(A2)+6(A3) | DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D1D2DD2D1211:CCNpqCCqrCCprr                         ‖
	//       ‖  8 ‖ CCpqCAprCCrqq | ∨E      ‖ CCpqCCNprCCrqq    | ∨E         | 121 ; 60(D)+28(A1)+27(A2)+6(A3) | DD2D1D2DD2D12DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D1D2DD2D1211DD2D111:CCpqCCNprCCrqq     ‖
	//       ‖  9 ‖ CCpqCCrqCAprq | ∨E      ‖ CCpqCCrqCCNprq    | ∨E         | 113 ; 56(D)+26(A1)+25(A2)+6(A3) | DD2D1D2DD2D12DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D121DD2D111:CCpqCCrqCCNprq             ‖
	//       ‖ 10 ‖ CCpqCArpCCrqq | ∨E      ‖ CCpqCCNrpCCrqq    | ∨E         |  93 ; 46(D)+21(A1)+20(A2)+6(A3) | DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D121:CCpqCCNrpCCrqq                                 ‖
	//       ‖ 11 ‖ CCpqCCrqCArpq | ∨E      ‖ CCpqCCrqCCNrpq    | ∨E         | 117 ; 58(D)+27(A1)+26(A2)+6(A3) | DD2D1DD2D1DD2D1DD22D11DD2D112D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D121:CCpqCCrqCCNrpq         ‖
	//       ‖ 12 ‖ CCpqCCqpEpq   | ↔I      ‖ CCpqCCqpNCCpqNCqp | ↔I         |                                 | via CpCqNCpNq (∧I)                                                                                                                           ‖
	//       ‖ 13 ‖ CCpqCCqpEqp   | ↔I      ‖ CCpqCCqpNCCqpNCpq | ↔I         |                                 | via CpCqNCqNp (∧I)                                                                                                                           ‖
	//       ‖ 14 ‖ CEpqCpq       | ↔E-l    ‖ CNCCpqNCqpCpq     | ↔E-l       |                                 | via CNCpqp  (∧E-l)                                                                                                                           ‖
	//       ‖ 15 ‖ CEpqCqp       | ↔E-r    ‖ CNCCpqNCqpCqp     | ↔E-r       |                                 | via CNCpNqq (∧E-r)                                                                                                                           ‖
	//       ‖ 16 ‖ CCpONp        | ¬I      ‖ CCpNCqqNp         | ¬I         |  41 ; 20(D)+ 9(A1)+ 9(A2)+3(A3) | DD2DD2D13DD2D1DD22D2DD2D13DD2D1311D1DD211:CCpNCqqNp                                                                                          ‖
	//       ‖ 17 ‖ CNpCpO        | ¬E      ‖ CNpCpNCqq         | ¬E         |   7 ;  3(D)+ 2(A1)+ 1(A2)+1(A3) | DD2D131:CNpCpq                                                                                                                               ‖
	//       ‖ 18 ‖ CpCNpO        | ¬E      ‖ CpCNpNCqq         | ¬E         |                                 | via CpCNpq  (∨I-l)                                                                                                                           ‖
	//       ‖ 19 ‖ CCNpOp        | IP      ‖ CCNpNCqqp         | IP         |  11 ;  5(D)+ 3(A1)+ 2(A2)+1(A3) | DD23D1DD211:CCNpNCqqp                                                                                                                        ‖
	//       When a user provides multiple proofs for a single rule, a shortest of those proofs is used.
	//       Further shortenings may be possible by providing proofs for (id) ψ→ψ (i.e. Cpp) [ID 20, default:DD211] and (ins) (ψ→φ)→(ψ→(χ→φ)) (i.e. CCpqCpCrq) [ID 21, default: D2D11].
	//       All user-provided proofs must be given by a single proof summary file, which also defines the axioms of the target system.
	//       When no such proof summary is given, the default system (A1),(A2),(A3) (i.e. CpCqp,CCpCqrCCpqCpr,CCNpNqCqp) is targeted.
	static void convertFitchFxFileToDProofSummary(const std::string& ffxFile, const std::string* optIn_outputFile = nullptr, const std::string* optIn_baseProofSummaryFile = nullptr, bool normalPolishNotation = false, bool printInfixUnicode = false, bool pure = true, bool targetEverything = false, bool debug = false);
};

}
}

#endif // XAMIDI_ND_NDCONVERTER_H
