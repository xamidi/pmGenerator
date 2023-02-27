#include "DlFormula.h"

#include "../tree/TreeNode.h"
#include "DlCore.h"

using namespace std;
using namespace xamid::helper;

namespace xamid {
namespace nortmann {

string dlFormulaHash::representativeString(const shared_ptr<DlFormula>& f) {
	stringstream ss;
	const vector<shared_ptr<DlFormula>>& children = f->getChildren();
	const string& value = f->getValue()->value;
	string str_children;
	for (size_t i = 0; i < children.size(); i++) {
		if (i)
			str_children += ",";
		str_children += representativeString(children[i]);
	}
	if (!str_children.empty())
		ss << value << "[" << str_children << "]";
	else
		ss << value;
	return ss.str();
}

size_t dlFormulaHash::operator()(const shared_ptr<DlFormula>& f) const {
	hash<string> stringHash;
	return stringHash.operator()(representativeString(f));
}

bool dlFormulaEqual::operator()(const shared_ptr<DlFormula>& f, const shared_ptr<DlFormula>& g) const {
	return *f == *g;
}

}
}
