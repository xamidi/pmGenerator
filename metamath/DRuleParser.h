#ifndef XAMIDI_METAMATH_DRULEPARSER_H
#define XAMIDI_METAMATH_DRULEPARSER_H

#include <cstddef>
#include <map>
#include <memory>
#include <set>
#include <string_view>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace xamidi {
namespace helper { struct String; }
namespace tree { template<typename T> class TreeNode; }
namespace logic { typedef tree::TreeNode<helper::String> DlFormula; enum class DlOperator; struct DlCore; }

namespace metamath {

// (first: D-proof, second: (<0>: formulas as tree structures, <1>: reasons, <2>: reference numbers of reasons))
typedef std::pair<std::string, std::tuple<std::vector<std::shared_ptr<logic::DlFormula>>, std::vector<std::string>, std::map<std::size_t, std::vector<unsigned>>>> DProofInfo;

class DRuleParser {
	friend struct logic::DlCore;

	// Unique pointer for each operator terminal. Accessible via DlCore::obtainDefiniteOpSymbol().
	static const std::shared_ptr<helper::String>& _and();
	static const std::shared_ptr<helper::String>& _or();
	static const std::shared_ptr<helper::String>& _nand();
	static const std::shared_ptr<helper::String>& _nor();
	static const std::shared_ptr<helper::String>& _imply();
	static const std::shared_ptr<helper::String>& _implied();
	static const std::shared_ptr<helper::String>& _nimply();
	static const std::shared_ptr<helper::String>& _nimplied();
	static const std::shared_ptr<helper::String>& _equiv();
	static const std::shared_ptr<helper::String>& _xor();
	static const std::shared_ptr<helper::String>& _com();
	static const std::shared_ptr<helper::String>& _app();
	static const std::shared_ptr<helper::String>& _not();
	static const std::shared_ptr<helper::String>& _nece();
	static const std::shared_ptr<helper::String>& _poss();
	static const std::shared_ptr<helper::String>& _obli();
	static const std::shared_ptr<helper::String>& _perm();
	static const std::shared_ptr<helper::String>& _top();
	static const std::shared_ptr<helper::String>& _bot();

public:
	struct AxiomInfo {
		std::shared_ptr<logic::DlFormula> refinedAxiom;
		unsigned primitivesCount;
		std::string name;
		AxiomInfo(const std::string& name, const std::shared_ptr<logic::DlFormula>& axiom);
		AxiomInfo& operator=(const AxiomInfo& other);
	private:
		AxiomInfo(const std::tuple<std::shared_ptr<logic::DlFormula>, unsigned, std::string>& refinedData);
		static std::tuple<std::shared_ptr<logic::DlFormula>, unsigned, std::string> _refineAxiom(const std::string& name, const std::shared_ptr<logic::DlFormula>& axiom);
	};

private:
	static std::shared_ptr<logic::DlFormula> _ax(unsigned axiomIndex, const std::vector<std::shared_ptr<logic::DlFormula>>& primitives, const std::vector<AxiomInfo>& axioms);
	static std::shared_ptr<logic::DlFormula> _ax1(const std::shared_ptr<logic::DlFormula>& psi, const std::shared_ptr<logic::DlFormula>& phi);
	static std::shared_ptr<logic::DlFormula> _ax2(const std::shared_ptr<logic::DlFormula>& psi, const std::shared_ptr<logic::DlFormula>& phi, const std::shared_ptr<logic::DlFormula>& chi);
	static std::shared_ptr<logic::DlFormula> _ax3(const std::shared_ptr<logic::DlFormula>& psi, const std::shared_ptr<logic::DlFormula>& phi);

public:
	static std::vector<std::string> readFromMmsolitaireFile(const std::string& file, std::vector<std::string>* optOut_dProofNamesInFile, bool debug = false);
	static std::map<std::size_t, std::set<std::string>> prepareDProofsByLength(const std::string& file, const std::vector<AxiomInfo>* customAxioms = nullptr, unsigned minUseAmountToCreateHelperProof = 2, std::vector<std::string>* optOut_dProofsInFile = nullptr, std::vector<std::string>* optOut_dProofNamesInFile = nullptr, bool debug = false);

	// Fast substitution, which only works reliably when it is ensured that 'formula' contains no non-leaf references that also occur in 'substitutions'.
	// Otherwise, cycles / infinite trees (which are no formulas) may be constructed!
	static void modifyingSubstitute(std::shared_ptr<logic::DlFormula>& formula, const std::map<std::string, std::shared_ptr<logic::DlFormula>>& substitutions, std::unordered_set<std::shared_ptr<logic::DlFormula>>* alreadyModified = nullptr);
private:
	static void _modifyingSubstitute(std::shared_ptr<logic::DlFormula>& formula, const std::map<std::string, std::shared_ptr<logic::DlFormula>>& substitutions, std::unordered_set<std::shared_ptr<logic::DlFormula>>& alreadyModified);

public:
	static std::vector<DProofInfo> parseDProof_raw(const std::string& dProof, const std::vector<AxiomInfo>* customAxioms = nullptr, unsigned minUseAmountToCreateHelperProof = 2, bool debug = false, bool calculateMeanings = false, bool exceptionOnUnificationFailure = true, bool reversedAbstractProofStrings = true);
	static std::vector<DProofInfo> parseDProof_raw_permissive(const std::string& dProof, const std::vector<AxiomInfo>* customAxioms = nullptr, unsigned minUseAmountToCreateHelperProof = 2, bool debug = false, bool calculateMeanings = false, bool reversedAbstractProofStrings = true);
	static std::vector<DProofInfo> parseDProofs_raw(const std::vector<std::string>& dProofs, const std::vector<AxiomInfo>* customAxioms = nullptr, unsigned minUseAmountToCreateHelperProof = 2, std::map<std::size_t, std::set<std::string>>* optOut_knownDProofsByLength = nullptr, bool debug = false, bool calculateMeanings = true, bool exceptionOnUnificationFailure = true, bool prepareOnly = false, bool reversedAbstractProofStrings = true, std::vector<std::size_t>* optOut_indexTranslation = nullptr, std::unordered_map<std::size_t, std::size_t>* optOut_indexOrigins = nullptr, std::map<std::size_t, std::size_t>* optOut_duplicates = nullptr, std::vector<std::string>* optOut_otherProofStrings = nullptr);

	static void reverseAbstractProofString(std::string& abstractDProof);

	// Parsing of propositional formulas in pmproofs' style that declare desired consequents or results of proofs.
	static std::shared_ptr<logic::DlFormula> parseMmConsequent(const std::string& strConsequent, bool calculateMeanings = true);

	static std::string toDBProof(const std::string& dProof, const std::vector<AxiomInfo>* customAxioms = nullptr, const std::string& name = "", const std::string& theorem = "", bool normalPolishNotation = false);
	static void parseAbstractDProof(std::vector<std::string>& inOut_abstractDProof, std::vector<std::shared_ptr<logic::DlFormula>>& out_abstractDProofConclusions, const std::vector<AxiomInfo>* customAxioms = nullptr, std::vector<std::string>* optOut_helperRules = nullptr, std::vector<std::shared_ptr<logic::DlFormula>>* optOut_helperRulesConclusions = nullptr, std::vector<std::size_t>* optOut_indexEvalSequence = nullptr, bool debug = false);
	static std::vector<std::size_t> parseValidateAndFilterAbstractDProof(std::vector<std::string>& inOut_abstractDProof, std::vector<std::shared_ptr<logic::DlFormula>>& out_abstractDProofConclusions, std::vector<std::string>& out_helperRules, std::vector<std::shared_ptr<logic::DlFormula>>& out_helperRulesConclusions, const std::vector<AxiomInfo>* customAxioms = nullptr, std::vector<AxiomInfo>* filterForTheorems = nullptr, std::vector<AxiomInfo>* requiredIntermediateResults = nullptr, std::vector<std::size_t>* optOut_indexEvalSequence = nullptr, bool debug = false);
	static std::vector<std::size_t> measureFundamentalLengthsInAbstractDProof(const std::vector<std::size_t>& targetIndices, const std::vector<std::string>& abstractDProof, const std::vector<std::shared_ptr<logic::DlFormula>>& abstractDProofConclusions, const std::vector<std::string>& helperRules = { }, const std::vector<std::shared_ptr<logic::DlFormula>>& helperRulesConclusions = { }, bool debug = false, std::size_t limit = SIZE_MAX);
	static std::vector<std::string> unfoldRulesInAbstractDProof(const std::vector<std::size_t>& targetIndices, const std::vector<std::string>& abstractDProof, const std::vector<std::string>& helperRules = { }, bool debug = false, std::vector<std::size_t>* storedFundamentalLengths = nullptr, std::size_t storeIntermediateUnfoldingLimit = SIZE_MAX);
	static std::vector<std::string> unfoldAbstractDProof(const std::vector<std::string>& abstractDProof, const std::vector<AxiomInfo>* customAxioms = nullptr, std::vector<AxiomInfo>* filterForTheorems = nullptr, std::vector<AxiomInfo>* requiredIntermediateResults = nullptr, bool debug = false, std::size_t storeIntermediateUnfoldingLimit = SIZE_MAX, std::size_t limit = SIZE_MAX);
	static void compressAbstractDProof(std::vector<std::string>& retractedDProof, std::vector<std::shared_ptr<logic::DlFormula>>& abstractDProofConclusions, std::vector<std::string>& helperRules, std::vector<std::shared_ptr<logic::DlFormula>>& helperRulesConclusions, std::vector<std::size_t>& indexEvalSequence, const std::vector<AxiomInfo>* customAxioms = nullptr, bool concurrentDRuleSearch = true);
	static std::vector<std::string> recombineAbstractDProof(const std::vector<std::string>& abstractDProof, std::vector<std::shared_ptr<logic::DlFormula>>& out_conclusions, const std::vector<AxiomInfo>* customAxioms = nullptr, std::vector<AxiomInfo>* filterForTheorems = nullptr, const std::vector<AxiomInfo>* conclusionsWithHelperProofs = nullptr, unsigned minUseAmountToCreateHelperProof = 2, std::vector<AxiomInfo>* requiredIntermediateResults = nullptr, bool debug = false, std::size_t maxLengthToKeepProof = SIZE_MAX, bool abstractProofStrings = true, std::size_t storeIntermediateUnfoldingLimit = SIZE_MAX, std::size_t limit = SIZE_MAX, bool removeDuplicateConclusions = false, bool compress = false, bool compress_concurrentDRuleSearch = true);
private:
#define PARSEMMPL_STORED // NOTE: For Metamath's pmproofs.txt, using storage slightly slows parsing but speeds up meaning calculation, so that stored mode is faster overall. However, those overall durations are close to two milliseconds, so it barely matters.
#ifdef PARSEMMPL_STORED
	static std::shared_ptr<logic::DlFormula> _parseEnclosedMmFormula(std::unordered_map<std::string, std::shared_ptr<logic::DlFormula>>& formulaBackups, const std::string& strConsequent, std::string::size_type myFirst, std::string::size_type myLast, const std::map<std::string::size_type, std::pair<std::string::size_type, std::shared_ptr<logic::DlFormula>>>& potentialSubformulas, const std::string::const_iterator& consBegin);
#else
	static std::shared_ptr<logic::DlFormula> _parseEnclosedMmFormula(const std::string& strConsequent, std::string::size_type myFirst, std::string::size_type myLast, const std::map<std::string::size_type, std::pair<std::string::size_type, std::shared_ptr<logic::DlFormula>>>& potentialSubformulas, const std::string::const_iterator& consBegin);
#endif
	static std::string_view::iterator _obtainUnaryOperatorSequence(const std::string_view& unaryOperatorSequence, std::vector<logic::DlOperator>& unaryOperators);
};

}
}

#endif // XAMIDI_METAMATH_DRULEPARSER_H
