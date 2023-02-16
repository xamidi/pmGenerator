#ifndef XAMID_NORTMANN_DLCORE_H
#define XAMID_NORTMANN_DLCORE_H

#include <tbb/version.h>

#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace tbb {
namespace detail { namespace d1 { template<typename T> class tbb_allocator; template<typename T> class cache_aligned_allocator; template<typename T, typename Allocator> class concurrent_vector; template<typename Key, typename T, typename Hash, typename KeyEqual, typename Allocator> class concurrent_unordered_map; } }
using detail::d1::tbb_allocator;
using detail::d1::cache_aligned_allocator;
using detail::d1::concurrent_vector;
using detail::d1::concurrent_unordered_map;
#if TBB_VERSION_MAJOR >= 2021 && TBB_VERSION_MINOR >= 4
namespace detail { namespace d2 { template<typename Key, typename Value, typename Compare, typename Allocator> class concurrent_map; } }
using detail::d2::concurrent_map;
#else
namespace detail { namespace d1 { template<typename Key, typename Value, typename Compare, typename Allocator> class concurrent_map; } }
using detail::d1::concurrent_map;
#endif
}

namespace xamid {
template<typename T> using tbb_concurrent_vector = tbb::concurrent_vector<T, tbb::cache_aligned_allocator<T>>;
template<typename Key, typename T> using tbb_concurrent_unordered_map = tbb::concurrent_unordered_map<Key, T, std::hash<Key>, std::equal_to<Key>, tbb::tbb_allocator<std::pair<const Key, T>>>;
template<typename Key, typename Value> using tbb_concurrent_map = tbb::concurrent_map<Key, Value, std::less<Key>, tbb::tbb_allocator<std::pair<const Key, Value>>>;
namespace helper { struct String; }
namespace tree { template<typename T> class TreeNode; }
namespace grammar { struct CfgGrammar; }

namespace nortmann {

typedef tree::TreeNode<helper::String> DlFormula;
struct dlFormulaHash;
struct dlFormulaEqual;
enum class DlOperator;

#define FOURCC(a, b, c, d) ((uint32_t) (((d) << 24) | ((c) << 16) | ((b) << 8) | (a)))
enum {
	MMID_LEFT = FOURCC('(', 0, 0, 0), //      (
	MMID_RIGHT = FOURCC(')', 0, 0, 0), //     )
	MMID_IMPLY = FOURCC('-', '>', 0, 0), //   \imply
	MMID_NOT = FOURCC('-', '.', 0, 0), //     \not
	MMID_EQUIV = FOURCC('<', '-', '>', 0), // \equiv
	MMID_OR = FOURCC('\\', '/', 0, 0), //     \or
	MMID_AND = FOURCC('/', '\\', 0, 0), //    \and
	MMID_NAND = FOURCC('-', '/', '\\', 0), // \nand
	MMID_XOR = FOURCC('\\', '/', '_', 0), //  \xor
	MMID_TOP = FOURCC('T', '.', 0, 0), //     \top
	MMID_BOT = FOURCC('F', '.', 0, 0), //     \bot
	MMID_PHI = FOURCC('p', 'h', 0, 0), //     \phi
	MMID_PSI = FOURCC('p', 's', 0, 0), //     \psi
	MMID_CHI = FOURCC('c', 'h', 0, 0), //     \chi
	MMID_THETA = FOURCC('t', 'h', 0, 0), //   \theta
	MMID_TAU = FOURCC('t', 'a', 0, 0), //     \tau
	MMID_ETA = FOURCC('e', 't', 0, 0), //     \eta
	MMID_ZETA = FOURCC('z', 'e', 0, 0), //    \zeta
	MMID_SIGMA = FOURCC('s', 'i', 0, 0), //   \sigma
	MMID_RHO = FOURCC('r', 'h', 0, 0), //     \rho
	MMID_MU = FOURCC('m', 'u', 0, 0), //      \mu
	MMID_LAMBDA = FOURCC('l', 'a', 0, 0), //  \lambda
	MMID_KAPPA = FOURCC('k', 'a', 0, 0), //   \kappa
	MMID_JPH = FOURCC('j', 'p', 'h', 0), //
	MMID_JPS = FOURCC('j', 'p', 's', 0), //
	MMID_JCH = FOURCC('j', 'c', 'h', 0), //
	MMID_JTH = FOURCC('j', 't', 'h', 0), //
	MMID_JTA = FOURCC('j', 't', 'a', 0), //
	MMID_JET = FOURCC('j', 'e', 't', 0), //
	MMID_JZE = FOURCC('j', 'z', 'e', 0), //
	MMID_JSI = FOURCC('j', 's', 'i', 0), //
	MMID_JRH = FOURCC('j', 'r', 'h', 0), //
	MMID_JMU = FOURCC('j', 'm', 'u', 0), //
	MMID_JLA = FOURCC('j', 'l', 'a', 0), //
	MMID_PHI_PRIME = FOURCC('p', 'h', '\'', 0), //       \phi'
	MMID_PSI_PRIME = FOURCC('p', 's', '\'', 0), //       \psi'
	MMID_CHI_PRIME = FOURCC('c', 'h', '\'', 0), //       \chi'
	MMID_THETA_PRIME = FOURCC('t', 'h', '\'', 0), //     \theta'
	MMID_TAU_PRIME = FOURCC('t', 'a', '\'', 0), //       \tau'
	MMID_ETA_PRIME = FOURCC('e', 't', '\'', 0), //       \eta'
	MMID_ZETA_PRIME = FOURCC('z', 'e', '\'', 0), //      \zeta'
	MMID_SIGMA_PRIME = FOURCC('s', 'i', '\'', 0), //     \sigma'
	MMID_RHO_PRIME = FOURCC('r', 'h', '\'', 0), //       \rho'
	MMID_PHI_DPRIME = FOURCC('p', 'h', '\'', '\''), //   \phi''
	MMID_PSI_DPRIME = FOURCC('p', 's', '\'', '\''), //   \psi''
	MMID_CHI_DPRIME = FOURCC('c', 'h', '\'', '\''), //   \chi''
	MMID_THETA_DPRIME = FOURCC('t', 'h', '\'', '\''), // \theta''
	MMID_TAU_DPRIME = FOURCC('t', 'a', '\'', '\''), //   \tau''
	MMID_ETA_DPRIME = FOURCC('e', 't', '\'', '\''), //   \eta''
	MMID_ZETA_DPRIME = FOURCC('z', 'e', '\'', '\''), //  \zeta''
	MMID_SIGMA_DPRIME = FOURCC('s', 'i', '\'', '\''), // \sigma''
	MMID_RHO_DPRIME = FOURCC('r', 'h', '\'', '\''), //   \rho''
};

struct DlCore {
	// Grammar attributes (using lazy initialization via singleton pattern to prevent initialization order issues)
	static grammar::CfgGrammar& grammar();
	static const std::string& terminalStr_and();
	static const std::string& terminalStr_or();
	static const std::string& terminalStr_nand();
	static const std::string& terminalStr_nor();
	static const std::string& terminalStr_imply();
	static const std::string& terminalStr_implied();
	static const std::string& terminalStr_nimply();
	static const std::string& terminalStr_nimplied();
	static const std::string& terminalStr_equiv();
	static const std::string& terminalStr_xor();
	static const std::string& terminalStr_com();
	static const std::string& terminalStr_app();
	static const std::string& terminalStr_not();
	static const std::string& terminalStr_nece();
	static const std::string& terminalStr_poss();
	static const std::string& terminalStr_obli();
	static const std::string& terminalStr_perm();
	static const std::string& terminalStr_top();
	static const std::string& terminalStr_bot();
	static const std::unordered_map<std::string, DlOperator>& dlOperators();
	static unsigned dlOperatorArity(DlOperator op);
	static const std::string& dlOperatorToString(DlOperator op);
	static const std::shared_ptr<helper::String>& obtainDefiniteOpSymbol(DlOperator op);

	// Shared grammar and variable information (this is handy e.g. for proofs, so that translations of formulas between proofs are easy)
	static const std::vector<uint32_t>& digits();
	static tbb_concurrent_map<std::string, std::vector<uint32_t>>& labelToTerminalSymbols_variables();
	static tbb_concurrent_vector<std::string>& variableToLabel();
	static tbb_concurrent_unordered_map<std::string, std::string>& variableMeaningToLabel();

	// Formula properties
	static std::unordered_set<std::string> primitivesOfFormula(const std::shared_ptr<DlFormula>& formula); // a set (unordered, no duplicates)

	// Create a copy of the given formula where all non-basic operators are replaced by their fundamental meaning in { \not, \imply, \nece, \com }.
	// NOTE: When requested, 'optOut_hasUniqueOriginals' returns false iff the originals are not unique, e.g. for \notX\implyY\imply(Z\imply(X\orY)),
	//       there is BasicDL(\notX\implyY) = BasicDL(X\orY) = \notX\implyY, thus Original(\notX\implyY) in {\notX\implyY, X\orY} would not be
	//       uniquely determined. In case of such "collisions", 'optOut_representativeOriginals' utilizes originals with minimal meaning lengths.
	static std::shared_ptr<DlFormula> toBasicDlFormula(const std::shared_ptr<DlFormula>& formula, std::unordered_map<std::shared_ptr<DlFormula>, std::shared_ptr<DlFormula>>* optOut_originals = nullptr, bool* optOut_hasUniqueOriginals = nullptr, std::unordered_map<std::shared_ptr<DlFormula>, std::shared_ptr<DlFormula>, dlFormulaHash, dlFormulaEqual>* optOut_representativeOriginals = nullptr, bool calculateMeanings = true);

	static bool tryRegisterVariable(const std::string& variableName, std::vector<uint32_t>* optOut_variableNameSequence = nullptr);

	// Determine whether 'potentialSchema' can be substituted to 'formula', and for which substitution. Note that substitution entries contain references to nodes of 'formula'.
	static bool isSchemaOf(const std::shared_ptr<DlFormula>& potentialSchema, const std::shared_ptr<DlFormula>& formula, std::map<std::string, std::shared_ptr<DlFormula>>* optOut_substitutions = nullptr);
	// Variant where inputs are given in Łukasiewicz-format provided by toPolishNotation_noRename(), and all variable names consist of only numerical characters.
	static bool isSchemaOf_polishNotation_noRename_numVars(const std::string& potentialSchema, const std::string& formula, std::map<size_t, std::string>* optOut_substitutions = nullptr);

	// Determines whether there exists a unifier for the given formulas, i.e. a substitution that results in the same substituted formula for both of the given formulas.
	// Essentially applies Robinson's unification algorithm, but modified such that the substituted formulas are not constructed but implicitly compared.
	// Note that the unifier for trees can be exponential in size w.r.t. the input, e.g. formulas { a\orz\ory\orx\orw, w\or(x\or(y\or(z\ora))) } [n := 5 variables each] result in
	// unifier 〈w, a\ora\or(a\ora)\or(a\ora\or(a\ora))〉, 〈x, a\ora\or(a\ora)〉, 〈y, a\ora〉, 〈z, a〉 [15 variables, generally 2^(n-2) + ... + 2^1 + 2^0 = sum_(k=0)^(n-2)2^k = 2^(n-1)-1].
	// Their unified formula is thereby a\ora\or(a\ora)\or(a\ora\or(a\ora))\or(a\ora\or(a\ora)\or(a\ora\or(a\ora))) [16 variables, generally 2^(n-1)].
	static bool tryUnifyTrees(const std::shared_ptr<nortmann::DlFormula>& formulaA, const std::shared_ptr<nortmann::DlFormula>& formulaB, std::map<std::string, std::shared_ptr<nortmann::DlFormula>>* optOut_substitutions = nullptr, bool debug = false);

	// A standard formula representation, except that topmost binary operators are not surrounded by parentheses.
	static std::string formulaRepresentation_traverse(const std::shared_ptr<DlFormula>& formula);

	// Calculate the formula's representation via left-to-right inorder traversal of its tree structure. Parentheses are generated for each and only binary operators, thus each formula has a unique such representation.
	static std::string standardFormulaRepresentation(const std::shared_ptr<DlFormula>& formula);

	static unsigned standardFormulaLength(const std::shared_ptr<DlFormula>& formula);

	// Calculate the formula's representation in Polish notation (according to 1. Łukasiewicz, 2. Bocheński).
	// - standard:  { \and -> K, \or -> A, \nand -> D, \nor -> X, \imply -> C, \implied -> B, \equiv -> E, \xor -> J, \not -> N, \nece -> L, \poss -> M, \top -> V, \bot -> O }
	// - custom:    { \nimply -> F, \nimplied -> G, \com -> S, \app -> U, \obli -> Z, \perm -> P }
	// - Bocheński: { \nimply -> L, \nimplied -> M } instead of { \nimply -> F, \nimplied -> G }, and (custom) { \nece -> H, \poss -> I } instead of { \nece -> L, \poss -> M }
	// Performance-oriented variant that does not rename variables and does not support user-defined translations. Generates invalid expressions when variable names
	// interfere with operator symbols, i.e. in order to generate parsable expressions, variable names should not contain a character of an operator symbol.
	// In order to support variable names of lengths greater 1, all consecutive variable names are separated by '.', e.g. x1\implyx2 -> "Cx1.x2".
	static std::string toPolishNotation_noRename(const std::shared_ptr<DlFormula>& f, bool prioritizeBochenski = false);

	// (Performance-oriented) inverse of toPolishNotation_noRename(). Assigns DRuleParser's globally definite symbols to operators, and its own globally definite symbols to variables.
	static bool fromPolishNotation_noRename(std::shared_ptr<DlFormula>& output, const std::string& input, bool prioritizeBochenski = false, bool debug = true);

	// Calculate the formula's symbolic length (i.e. the amount of nodes of its syntax tree), where 'formula' is given in Łukasiewicz-format provided by toPolishNotation_noRename(),
	// and all variable names consist of only numerical characters.
	static size_t symbolicLen_polishNotation_noRename_numVars(const std::string& formula);

	// Calculate the formula's standard length, where 'formula' is given in Łukasiewicz-format provided by toPolishNotation_noRename(), and all variable names consist of only numerical characters.
	static size_t standardLen_polishNotation_noRename_numVars(const std::string& formula);

	// Traverse the given amount of (sub-)formulas of the given formula in Łukasiewicz-format provided by toPolishNotation_noRename(), and return the index of the final character.
	static std::string::size_type traverseFormulas_polishNotation_noRename_numVars(const std::string& formula, std::string::size_type startIndex = 0, std::string::size_type formulasToTraverse = 1);

	// Calculate the substitution's representation based on formulaRepresentation_traverse().
	static std::string substitutionRepresentation_traverse(const std::map<std::string, std::shared_ptr<DlFormula>>& substitutions);

	// Do a left-to-right inorder traversal, call fVisit(node) when visiting a node, fDown(node, child) when traversing down from node to child, and fUp(child, node) when traversing up from child to node.
	static void traverseLeftToRightInOrder(const std::shared_ptr<DlFormula>& formula, const std::function<void(const std::shared_ptr<DlFormula>&)>& fVisit, const std::function<void(const std::shared_ptr<DlFormula>&, const std::shared_ptr<DlFormula>&)>& fDown, const std::function<void(const std::shared_ptr<DlFormula>&, const std::shared_ptr<DlFormula>&)>& fUp);

	// Create a copy of the given formula where all the variables of formula have been replaced by references to the corresponding substitution entries.
	static std::shared_ptr<DlFormula> substitute(const std::shared_ptr<DlFormula>& formula, const std::map<std::string, std::shared_ptr<DlFormula>>& substitutions);

	// Calculates all the meanings in a formula such that no meaning of a node represents an expression (ψ) for a DL-formula ψ.
	// The meaning of a parent node surrounds a child's meaning by parentheses only if necessary to describe the same tree / formula, using our order of operations with left first bracketing.
	static void calculateEmptyMeanings(const std::shared_ptr<DlFormula>& formula);

	// Recalculates only the meaning of the root node, based on its value and the meaning of its children.
	static void recalculateMeaningUsingMeaningOfChildren(const std::shared_ptr<DlFormula>& destinationNode); // CAUTION: Same as for reduceFormulaMeaning_modifying().

private:
	// Helper functions
	static bool _isSchemaOf(const std::shared_ptr<DlFormula>& potentialSchema, const std::shared_ptr<DlFormula>& formula, std::map<std::string, std::shared_ptr<DlFormula>>& substitutions);
	static bool _tryUnifyTrees(const std::shared_ptr<nortmann::DlFormula>& formulaA, const std::shared_ptr<nortmann::DlFormula>& formulaB, std::map<std::string, std::shared_ptr<nortmann::DlFormula>>& substitutions, bool debug);
	static void _toBasicDlFormula(const std::shared_ptr<DlFormula>& destinationNode, const std::shared_ptr<DlFormula>& formula, std::unordered_map<std::shared_ptr<DlFormula>, std::shared_ptr<DlFormula>>* optOut_originals, bool calculateMeanings);
	static void _substitute(const std::shared_ptr<DlFormula>& destinationNode, const std::shared_ptr<DlFormula>& formula, const std::map<std::string, std::shared_ptr<DlFormula>>& substitutions);
};

}
}

#endif // XAMID_NORTMANN_DLCORE_H
