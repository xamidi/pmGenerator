#ifndef XAMID_NORTMANN_DLFORMULA_H
#define XAMID_NORTMANN_DLFORMULA_H

#include <cstddef>
#include <memory>
#include <string>

namespace xamid {
namespace helper { struct String; }
namespace tree { template<typename T> class TreeNode; }

namespace nortmann {

typedef tree::TreeNode<helper::String> DlFormula; // NOTE: Even though possible, it should be common practice to never modify a formula that is not freshly generated. Otherwise, editing can have side-effects on different formulas that have nodes in common. Or even worse, cycles can occur when inserting existing formulas.

// Avoids collisions using unordered_set<shared_ptr<DlFormula>, dlFormulaHash, dlFormulaEqual> and unordered_map<shared_ptr<DlFormula>, _Tp, dlFormulaHash, dlFormulaEqual>,
// given that formulas cannot contain symbols "[", "]" or ",", and all primitives being represented by non-empty strings.
struct dlFormulaHash {
	static std::string representativeString(const std::shared_ptr<DlFormula>& f);
	std::size_t operator()(const std::shared_ptr<DlFormula>& f) const;
};
struct dlFormulaEqual {
	bool operator()(const std::shared_ptr<DlFormula>& f, const std::shared_ptr<DlFormula>& g) const;
};

enum class DlOperator {
	And, Or, Nand, Nor, Imply, Implied, Nimply, Nimplied, Equiv, Xor, Com, App, Not, Nece, Poss, Obli, Perm, Top, Bot
};

}
}

#endif // XAMID_NORTMANN_DLFORMULA_H
