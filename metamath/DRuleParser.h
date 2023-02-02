#ifndef XAMID_METAMATH_DRULEPARSER_H
#define XAMID_METAMATH_DRULEPARSER_H

#include <map>
#include <memory>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xamid {
namespace helper { struct String; }
namespace tree { template<typename T> class TreeNode; }
namespace nortmann { typedef tree::TreeNode<helper::String> DlFormula; enum class DlOperator; struct DlCore; }

namespace metamath {

class DRuleParser {
	friend struct nortmann::DlCore;

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

	static std::shared_ptr<nortmann::DlFormula> _ax1(const std::shared_ptr<nortmann::DlFormula>& psi, const std::shared_ptr<nortmann::DlFormula>& phi);
	static std::shared_ptr<nortmann::DlFormula> _ax2(const std::shared_ptr<nortmann::DlFormula>& psi, const std::shared_ptr<nortmann::DlFormula>& phi, const std::shared_ptr<nortmann::DlFormula>& chi);
	static std::shared_ptr<nortmann::DlFormula> _ax3(const std::shared_ptr<nortmann::DlFormula>& psi, const std::shared_ptr<nortmann::DlFormula>& phi);

public:
	static std::vector<std::pair<std::string, std::string>> readFromMmsolitaireFile(const std::string& file, bool debug = false);
	static std::map<int, std::set<std::string>> prepareDProofsByLength(const std::string& file, unsigned minUseAmountToCreateHelperProof = 2, std::vector<std::pair<std::string, std::string>>* optOut_dProofsInFile = nullptr, bool debug = false);

	// Fast substitution, which only works reliably when it is ensured that 'formula' contains no non-leaf references that also occur in 'substitutions'.
	// Otherwise, cycles / infinite trees (which are no formulas) may be constructed!
	static void modifyingSubstitute(std::shared_ptr<nortmann::DlFormula>& formula, const std::map<std::string, std::shared_ptr<nortmann::DlFormula>>& substitutions, std::unordered_set<std::shared_ptr<nortmann::DlFormula>>* alreadyModified = nullptr);
private:
	static void _modifyingSubstitute(std::shared_ptr<nortmann::DlFormula>& formula, const std::map<std::string, std::shared_ptr<nortmann::DlFormula>>& substitutions, std::unordered_set<std::shared_ptr<nortmann::DlFormula>>& alreadyModified);

public:
	static std::vector<std::pair<std::string, std::tuple<std::vector<std::shared_ptr<nortmann::DlFormula>>, std::vector<std::string>, std::map<unsigned, std::vector<unsigned>>>>> parseDProof_raw(const std::string& dProof, unsigned minUseAmountToCreateHelperProof = 2, bool verifyingConstruct = false, bool debug = false, bool calculateMeanings = false, bool exceptionOnUnificationFailure = false);
	static std::vector<std::pair<std::string, std::tuple<std::vector<std::shared_ptr<nortmann::DlFormula>>, std::vector<std::string>, std::map<unsigned, std::vector<unsigned>>>>> parseDProofs_raw(const std::vector<std::pair<std::string, std::string>>& dProofs, unsigned minUseAmountToCreateHelperProof = 2, std::map<std::string, std::string>* optOut_duplicates = nullptr, std::map<int, std::set<std::string>>* optOut_knownDProofsByLength = nullptr, bool verifyingConstruct = false, bool debug = false, bool calculateMeanings = true, bool exceptionOnUnificationFailure = true, const std::vector<std::string>* altIn_dProofsWithoutContexts = nullptr, bool prepareOnly = false);

	// Parsing of pmproofs' propositional formulas that declare desired consequents or results of proofs. Used by originalCollection().
	static std::shared_ptr<nortmann::DlFormula> parseMmPlConsequent(const std::string& strConsequent, bool calculateMeanings = true);
private:
#define PARSEMMPL_STORED // NOTE: For Metamath's pmproofs.txt, using storage slightly slows parsing but speeds up meaning calculation, so that stored mode is faster overall. However, those overall durations are close to two milliseconds, so it barely matters.
#ifdef PARSEMMPL_STORED
	static std::shared_ptr<nortmann::DlFormula> _parseEnclosedMmPlFormula(std::unordered_map<std::string, std::shared_ptr<nortmann::DlFormula>>& formulaBackups, const std::string& strConsequent, std::string::size_type myFirst, std::string::size_type myLast, const std::map<std::string::size_type, std::pair<std::string::size_type, std::shared_ptr<nortmann::DlFormula>>>& potentialSubformulas, const std::string::const_iterator& consBegin);
#else
	static std::shared_ptr<nortmann::DlFormula> _parseEnclosedMmPlFormula(const std::string& strConsequent, std::string::size_type myFirst, std::string::size_type myLast, const std::map<std::string::size_type, std::pair<std::string::size_type, std::shared_ptr<nortmann::DlFormula>>>& potentialSubformulas, const std::string::const_iterator& consBegin);
#endif
	static std::string::const_iterator _obtainUnaryOperatorSequence(const std::string& unaryOperatorSequence, std::vector<nortmann::DlOperator>& unaryOperators);
};

}
}

#endif // XAMID_METAMATH_DRULEPARSER_H
