#include "DlCore.h"

#include "../helper/FctHelper.h"
#include "../tree/TreeNode.h"
#include "../grammar/CfgGrammar.h"
#include "../metamath/DRuleParser.h"
#include "DlFormula.h"
#include "DlStructure.h"

#include <tbb/concurrent_map.h>
#include <tbb/concurrent_unordered_map.h>
#include <tbb/concurrent_vector.h>

#include <iostream>
#include <mutex>

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::tree;
using namespace xamidi::grammar;
using namespace xamidi::metamath;

namespace xamidi {
namespace logic {

// ------------------------------------------------------------------------------------------------ //
// Fields, using lazy initialization via singleton pattern (to prevent initialization order issues) //
// ------------------------------------------------------------------------------------------------ //

CfgGrammar& DlCore::grammar() {
	static CfgGrammar& g = DlStructure::dlEvaluationGrammar();
	return g;
}
const string& DlCore::terminalStr_and() { // [NOTE: Using "const string __attribute__ ((init_priority(111))) DlCore::terminalStr_and() = grammar().stringOf([...])" here, for example, crashes at unordered_map::find() since the internal hash table is not initialized yet.]
	static const string s = grammar().stringOf(DlStructure::terminal_and());
	return s;
}
const string& DlCore::terminalStr_or() {
	static const string s = grammar().stringOf(DlStructure::terminal_or());
	return s;
}
const string& DlCore::terminalStr_nand() {
	static const string s = grammar().stringOf(DlStructure::terminal_nand());
	return s;
}
const string& DlCore::terminalStr_nor() {
	static const string s = grammar().stringOf(DlStructure::terminal_nor());
	return s;
}
const string& DlCore::terminalStr_imply() {
	static const string s = grammar().stringOf(DlStructure::terminal_imply());
	return s;
}
const string& DlCore::terminalStr_implied() {
	static const string s = grammar().stringOf(DlStructure::terminal_implied());
	return s;
}
const string& DlCore::terminalStr_nimply() {
	static const string s = grammar().stringOf(DlStructure::terminal_nimply());
	return s;
}
const string& DlCore::terminalStr_nimplied() {
	static const string s = grammar().stringOf(DlStructure::terminal_nimplied());
	return s;
}
const string& DlCore::terminalStr_equiv() {
	static const string s = grammar().stringOf(DlStructure::terminal_equiv());
	return s;
}
const string& DlCore::terminalStr_xor() {
	static const string s = grammar().stringOf(DlStructure::terminal_xor());
	return s;
}
const string& DlCore::terminalStr_com() {
	static const string s = grammar().stringOf(DlStructure::terminal_com());
	return s;
}
const string& DlCore::terminalStr_app() {
	static const string s = grammar().stringOf(DlStructure::terminal_app());
	return s;
}
const string& DlCore::terminalStr_not() {
	static const string s = grammar().stringOf(DlStructure::terminal_not());
	return s;
}
const string& DlCore::terminalStr_nece() {
	static const string s = grammar().stringOf(DlStructure::terminal_nece());
	return s;
}
const string& DlCore::terminalStr_poss() {
	static const string s = grammar().stringOf(DlStructure::terminal_poss());
	return s;
}
const string& DlCore::terminalStr_obli() {
	static const string s = grammar().stringOf(DlStructure::terminal_obli());
	return s;
}
const string& DlCore::terminalStr_perm() {
	static const string s = grammar().stringOf(DlStructure::terminal_perm());
	return s;
}
const string& DlCore::terminalStr_top() {
	static const string s = grammar().stringOf(DlStructure::terminal_top());
	return s;
}
const string& DlCore::terminalStr_bot() {
	static const string s = grammar().stringOf(DlStructure::terminal_bot());
	return s;
}
const unordered_map<string, DlOperator>& DlCore::dlOperators() {
	static const unordered_map<string, DlOperator> o = { { terminalStr_and(), DlOperator::And }, { terminalStr_or(), DlOperator::Or }, { terminalStr_nand(), DlOperator::Nand }, { terminalStr_nor(), DlOperator::Nor }, { terminalStr_imply(), DlOperator::Imply }, { terminalStr_implied(), DlOperator::Implied }, { terminalStr_nimply(), DlOperator::Nimply }, { terminalStr_nimplied(), DlOperator::Nimplied }, { terminalStr_equiv(), DlOperator::Equiv }, { terminalStr_xor(), DlOperator::Xor }, { terminalStr_com(), DlOperator::Com }, { terminalStr_app(), DlOperator::App }, { terminalStr_not(), DlOperator::Not }, { terminalStr_nece(), DlOperator::Nece }, { terminalStr_poss(), DlOperator::Poss }, { terminalStr_obli(), DlOperator::Obli }, { terminalStr_perm(), DlOperator::Perm }, { terminalStr_top(), DlOperator::Top }, { terminalStr_bot(), DlOperator::Bot } };
	return o;
}

unsigned DlCore::dlOperatorArity(DlOperator op) {
	switch (op) {
	case DlOperator::Top:
	case DlOperator::Bot:
		return 0;
	case DlOperator::Not:
	case DlOperator::Nece:
	case DlOperator::Poss:
	case DlOperator::Obli:
	case DlOperator::Perm:
		return 1;
	case DlOperator::And:
	case DlOperator::Or:
	case DlOperator::Nand:
	case DlOperator::Nor:
	case DlOperator::Imply:
	case DlOperator::Implied:
	case DlOperator::Nimply:
	case DlOperator::Nimplied:
	case DlOperator::Equiv:
	case DlOperator::Xor:
	case DlOperator::Com:
	case DlOperator::App:
		return 2;
	default:
		throw domain_error("DlCore::dlOperatorArity(): Unknown DlOperator " + to_string(static_cast<unsigned>(op)) + ".");
	}
}

const string& DlCore::dlOperatorToString(DlOperator op) {
	switch (op) {
	case DlOperator::And:
		return terminalStr_and();
	case DlOperator::Or:
		return terminalStr_or();
	case DlOperator::Nand:
		return terminalStr_nand();
	case DlOperator::Nor:
		return terminalStr_nor();
	case DlOperator::Imply:
		return terminalStr_imply();
	case DlOperator::Implied:
		return terminalStr_implied();
	case DlOperator::Nimply:
		return terminalStr_nimply();
	case DlOperator::Nimplied:
		return terminalStr_nimplied();
	case DlOperator::Equiv:
		return terminalStr_equiv();
	case DlOperator::Xor:
		return terminalStr_xor();
	case DlOperator::Com:
		return terminalStr_com();
	case DlOperator::App:
		return terminalStr_app();
	case DlOperator::Not:
		return terminalStr_not();
	case DlOperator::Nece:
		return terminalStr_nece();
	case DlOperator::Poss:
		return terminalStr_poss();
	case DlOperator::Obli:
		return terminalStr_obli();
	case DlOperator::Perm:
		return terminalStr_perm();
	case DlOperator::Top:
		return terminalStr_top();
	case DlOperator::Bot:
		return terminalStr_bot();
	default:
		throw domain_error("DlCore::dlOperatorToString(): Unknown DlOperator " + to_string(static_cast<unsigned>(op)) + ".");
	}
}

const shared_ptr<String>& DlCore::obtainDefiniteOpSymbol(DlOperator op) {
	switch (op) {
	case DlOperator::And:
		return DRuleParser::_and();
	case DlOperator::Or:
		return DRuleParser::_or();
	case DlOperator::Nand:
		return DRuleParser::_nand();
	case DlOperator::Nor:
		return DRuleParser::_nor();
	case DlOperator::Imply:
		return DRuleParser::_imply();
	case DlOperator::Implied:
		return DRuleParser::_implied();
	case DlOperator::Nimply:
		return DRuleParser::_nimply();
	case DlOperator::Nimplied:
		return DRuleParser::_nimplied();
	case DlOperator::Equiv:
		return DRuleParser::_equiv();
	case DlOperator::Xor:
		return DRuleParser::_xor();
	case DlOperator::Com:
		return DRuleParser::_com();
	case DlOperator::App:
		return DRuleParser::_app();
	case DlOperator::Not:
		return DRuleParser::_not();
	case DlOperator::Nece:
		return DRuleParser::_nece();
	case DlOperator::Poss:
		return DRuleParser::_poss();
	case DlOperator::Obli:
		return DRuleParser::_obli();
	case DlOperator::Perm:
		return DRuleParser::_perm();
	case DlOperator::Top:
		return DRuleParser::_top();
	case DlOperator::Bot:
		return DRuleParser::_bot();
	default:
		throw domain_error("DlCore::obtainDefiniteOpSymbol(): Unknown DlOperator " + to_string(static_cast<unsigned>(op)) + ".");
	}
}

const vector<uint32_t>& DlCore::digits() {
	static const vector<uint32_t> v = { DlStructure::terminal_0(), DlStructure::terminal_1(), DlStructure::terminal_2(), DlStructure::terminal_3(), DlStructure::terminal_4(), DlStructure::terminal_5(), DlStructure::terminal_6(), DlStructure::terminal_7(), DlStructure::terminal_8(), DlStructure::terminal_9() };
	return v;
}
tbb::concurrent_map<string, vector<uint32_t>>& DlCore::labelToTerminalSymbols_variables() {
	static tbb::concurrent_map<string, vector<uint32_t>> m { make_pair("a", vector<uint32_t> { digits()[0] }) };
	return m;
}
tbb::concurrent_vector<string>& DlCore::variableToLabel() {
	static tbb::concurrent_vector<string> v { "a" };
	return v;
}
tbb::concurrent_unordered_map<string, string>& DlCore::variableMeaningToLabel() {
	static tbb::concurrent_unordered_map<string, string> m { make_pair("0", "a") };
	return m;
}

// ------------------------------------------------------------------------------------------------ //
// END Fields                                                                                       //
// ------------------------------------------------------------------------------------------------ //

unordered_set<string> DlCore::primitivesOfFormula(const shared_ptr<DlFormula>& formula) {
	unordered_set<string> result;
	auto recurse = [&](const shared_ptr<DlFormula>& formula, const auto& me) -> void {
		if (formula->getChildren().empty()) {
			const string& value = formula->getValue()->value;
			if (value != terminalStr_bot() && value != terminalStr_top())
				result.insert(value);
		} else
			for (const shared_ptr<DlFormula>& subformula : formula->getChildren())
				me(subformula, me);
	};
	recurse(formula, recurse);
	return result;
}

vector<string> DlCore::primitivesOfFormula_ordered(const shared_ptr<DlFormula>& formula) {
	vector<string> result;
	vector<string> resultSequence = primitiveSequenceOfFormula(formula);
	unordered_set<string> resultSet;
	for (const string& name : resultSequence)
		if (resultSet.emplace(name).second)
			result.push_back(name);
	return result;
}

// Extract the sequence of variables of the given DL-formula
vector<string> DlCore::primitiveSequenceOfFormula(const shared_ptr<DlFormula>& formula) {
	vector<string> result;
	auto recurse = [&](const shared_ptr<DlFormula>& formula, const auto& me) -> void {
		if (formula->getChildren().empty()) {
			const string& value = formula->getValue()->value;
			if (value != terminalStr_bot() && value != terminalStr_top())
				result.push_back(value);
		} else
			for (const shared_ptr<DlFormula>& subformula : formula->getChildren())
				me(subformula, me);
	};
	recurse(formula, recurse);
	return result;
}

bool DlCore::tryRegisterVariable(const string& variableName, vector<uint32_t>* optOut_variableNameSequence) {
	if (dlOperators().count(variableName))
		return false; // variableName cannot be a variable since it is an operator
	static mutex mtx;
	static atomic<uint32_t> variablesStateId = 0;
	uint32_t myWriteStateId = variablesStateId; // remember registered variables state
	// NOTE: Since 'variablesStateId' is increased after every modification of 'labelToTerminalSymbols_variables()', it
	//       is guaranteed to increase in case 'variableName' is not found below but added afterwards by another thread.
	tbb::concurrent_map<string, vector<uint32_t>>::const_iterator searchResult = labelToTerminalSymbols_variables().find(variableName);
	if (searchResult == labelToTerminalSymbols_variables().end()) { // new variable
		unique_lock<mutex> writeLock(mtx); // to avoid duplicate registrations, need to wait until other threads registered their potential variables
		bool stillNew = true;
		if (myWriteStateId != variablesStateId) { // other threads registered new variables in the meantime => update search result
			searchResult = labelToTerminalSymbols_variables().find(variableName);
			if (searchResult != labelToTerminalSymbols_variables().end())
				stillNew = false;
		}
		if (stillNew) { // register new variable ; NOTE: myWriteStateId == variablesStateId => ('variableName' new), since ('variableName' added) => myWriteStateId != variablesStateId.
			//#cout << "tryRegisterVariable(" << variableName << "): new variable [tid:" << this_thread::get_id() << "]" << endl;
			string name = to_string(labelToTerminalSymbols_variables().size());
			vector<uint32_t> variableNameSequence;
			for (char c : name)
				switch (c) {
				case '0':
					variableNameSequence.push_back(digits()[0]);
					break;
				case '1':
					variableNameSequence.push_back(digits()[1]);
					break;
				case '2':
					variableNameSequence.push_back(digits()[2]);
					break;
				case '3':
					variableNameSequence.push_back(digits()[3]);
					break;
				case '4':
					variableNameSequence.push_back(digits()[4]);
					break;
				case '5':
					variableNameSequence.push_back(digits()[5]);
					break;
				case '6':
					variableNameSequence.push_back(digits()[6]);
					break;
				case '7':
					variableNameSequence.push_back(digits()[7]);
					break;
				case '8':
					variableNameSequence.push_back(digits()[8]);
					break;
				case '9':
					variableNameSequence.push_back(digits()[9]);
					break;
				}
			labelToTerminalSymbols_variables().insert(make_pair(variableName, variableNameSequence));
			variableToLabel().push_back(variableName);
			variableMeaningToLabel().insert(make_pair(name, variableName));
			variablesStateId++;
			writeLock.unlock();
			if (optOut_variableNameSequence)
				*optOut_variableNameSequence = variableNameSequence;
		} else {
			writeLock.unlock();
			//#cout << "tryRegisterVariable(" << variableName << "): found variable [tid:" << this_thread::get_id() << "]" << endl;
			if (optOut_variableNameSequence)
				*optOut_variableNameSequence = searchResult->second;
		}
	} else if (optOut_variableNameSequence)
		*optOut_variableNameSequence = searchResult->second;
	return true;
}

// Returns equivalent tree (equal w.r.t. 'aliases' in Definition 2.1) that contains only \not, \imply, \nece, \com as operators
shared_ptr<DlFormula> DlCore::toBasicDlFormula(const shared_ptr<DlFormula>& formula, unordered_map<shared_ptr<DlFormula>, shared_ptr<DlFormula>>* optOut_originals, bool* optOut_hasUniqueOriginals, unordered_map<shared_ptr<DlFormula>, shared_ptr<DlFormula>, dlFormulaHash, dlFormulaEqual>* optOut_representativeOriginals, bool calculateMeanings) {
	bool extra = optOut_hasUniqueOriginals || optOut_representativeOriginals;
	unique_ptr<unordered_map<shared_ptr<DlFormula>, shared_ptr<DlFormula>>> __originals;
	if (optOut_originals) {
		if (!optOut_originals->empty())
			optOut_originals->clear();
	} else if (extra) {
		__originals = make_unique<unordered_map<shared_ptr<DlFormula>, shared_ptr<DlFormula>>>();
		optOut_originals = __originals.get();
	}
	shared_ptr<DlFormula> rootNode = make_shared<DlFormula>(make_shared<String>());
	_toBasicDlFormula(rootNode, formula, optOut_originals, calculateMeanings);
	if (extra) {
		bool hasUniqueOriginals = true;
		unordered_map<shared_ptr<DlFormula>, shared_ptr<DlFormula>, dlFormulaHash, dlFormulaEqual> representativeOriginals;
		for (pair<const shared_ptr<DlFormula>, shared_ptr<DlFormula>>& p : *optOut_originals) {
			pair<unordered_map<shared_ptr<DlFormula>, shared_ptr<DlFormula>, dlFormulaHash, dlFormulaEqual>::iterator, bool> insertResult = representativeOriginals.insert(p);
			if (!insertResult.second) {
				shared_ptr<DlFormula>& storedOriginal = insertResult.first->second;
				if (optOut_hasUniqueOriginals && hasUniqueOriginals && *storedOriginal != *p.second)
					hasUniqueOriginals = false;
				if (storedOriginal->meaning().size() > p.second->meaning().size())
					storedOriginal = p.second;
			}
		}
		if (optOut_hasUniqueOriginals)
			*optOut_hasUniqueOriginals = hasUniqueOriginals;
		if (optOut_representativeOriginals)
			*optOut_representativeOriginals = representativeOriginals;
	}
	return rootNode;
}

void DlCore::_toBasicDlFormula(const shared_ptr<DlFormula>& destinationNode, const shared_ptr<DlFormula>& formula, unordered_map<shared_ptr<DlFormula>, shared_ptr<DlFormula>>* optOut_originals, bool calculateMeanings) {
	unordered_map<string, DlOperator>::const_iterator itOperator = dlOperators().find(formula->getValue()->value);
	if (itOperator != dlOperators().end()) { // at an operator
		const vector<shared_ptr<DlFormula>>& subformulas = formula->getChildren();
		auto argumentNode = [&](unsigned childIndex) -> shared_ptr<DlFormula> {
			shared_ptr<DlFormula> node = make_shared<DlFormula>(make_shared<String>());
			_toBasicDlFormula(node, subformulas[childIndex], optOut_originals, calculateMeanings); // NOTE: Also adds originals in case optOut_originals is requested.
			return node;
		};
		auto extraUnaryOp = [&](const string& terminalStr, const shared_ptr<DlFormula>& onlyChild) -> shared_ptr<DlFormula> {
			shared_ptr<DlFormula> node = make_shared<DlFormula>(make_shared<String>(terminalStr));
			node->addChild(onlyChild);
			if (calculateMeanings)
				recalculateMeaningUsingMeaningOfChildren(node);
			return node;
		};
		auto extraBinaryOp = [&](const string& terminalStr, const shared_ptr<DlFormula>& leftChild, const shared_ptr<DlFormula>& rightChild) -> shared_ptr<DlFormula> {
			shared_ptr<DlFormula> node = make_shared<DlFormula>(make_shared<String>(terminalStr));
			node->addChild(leftChild);
			node->addChild(rightChild);
			if (calculateMeanings)
				recalculateMeaningUsingMeaningOfChildren(node);
			return node;
		};
		auto fillUnaryDestination = [&](const string& terminalStr, const shared_ptr<DlFormula>& onlyChild) {
			destinationNode->getValue()->value = terminalStr;
			destinationNode->addChild(onlyChild);
			if (calculateMeanings)
				recalculateMeaningUsingMeaningOfChildren(destinationNode);
			if (optOut_originals)
				optOut_originals->insert(make_pair(destinationNode, formula));
		};
		auto fillBinaryDestination = [&](const string& terminalStr, const shared_ptr<DlFormula>& leftChild, const shared_ptr<DlFormula>& rightChild) {
			destinationNode->getValue()->value = terminalStr;
			destinationNode->addChild(leftChild);
			destinationNode->addChild(rightChild);
			if (calculateMeanings)
				recalculateMeaningUsingMeaningOfChildren(destinationNode);
			if (optOut_originals)
				optOut_originals->insert(make_pair(destinationNode, formula));
		};
		auto firstVariable = []() -> shared_ptr<DlFormula> {
			vector<uint32_t> variableNameSequence = { digits()[0] };
			return make_shared<DlFormula>(variableNameSequence, make_shared<String>(variableToLabel()[0]));
		};
		switch (itOperator->second) {
		case DlOperator::And: // X\andY = \not(X\imply\notY)
			fillUnaryDestination(terminalStr_not(), extraBinaryOp(terminalStr_imply(), argumentNode(0), extraUnaryOp(terminalStr_not(), argumentNode(1))));
			break;
		case DlOperator::Or: // X\orY = \notX\implyY
			fillBinaryDestination(terminalStr_imply(), extraUnaryOp(terminalStr_not(), argumentNode(0)), argumentNode(1));
			break;
		case DlOperator::Nand: // X\nandY = X\imply\notY
			fillBinaryDestination(terminalStr_imply(), argumentNode(0), extraUnaryOp(terminalStr_not(), argumentNode(1)));
			break;
		case DlOperator::Nor: // X\norY = \not(\notX\implyY)
			fillUnaryDestination(terminalStr_not(), extraBinaryOp(terminalStr_imply(), extraUnaryOp(terminalStr_not(), argumentNode(0)), argumentNode(1)));
			break;
		case DlOperator::Imply: // X\implyY is a basic formula
			fillBinaryDestination(terminalStr_imply(), argumentNode(0), argumentNode(1));
			break;
		case DlOperator::Implied: // X\impliedY = Y\implyX
			fillBinaryDestination(terminalStr_imply(), argumentNode(1), argumentNode(0));
			break;
		case DlOperator::Nimply: // X\nimplyY = \not(X\implyY)
			fillUnaryDestination(terminalStr_not(), extraBinaryOp(terminalStr_imply(), argumentNode(0), argumentNode(1)));
			break;
		case DlOperator::Nimplied: // X\nimpliedY = \not(X\impliedY) = \not(Y\implyX)
			fillUnaryDestination(terminalStr_not(), extraBinaryOp(terminalStr_imply(), argumentNode(1), argumentNode(0)));
			break;
		case DlOperator::Equiv: { // X\equivY = (X\implyY)\and(X\impliedY) = \not((X\implyY)\imply\not(Y\implyX))
			shared_ptr<DlFormula> X = argumentNode(0);
			shared_ptr<DlFormula> Y = argumentNode(1);
			shared_ptr<DlFormula> XImplyY = extraBinaryOp(terminalStr_imply(), X, Y);
			shared_ptr<DlFormula> XNimpliedY = extraUnaryOp(terminalStr_not(), extraBinaryOp(terminalStr_imply(), Y, X));
			fillUnaryDestination(terminalStr_not(), extraBinaryOp(terminalStr_imply(), XImplyY, XNimpliedY));
			break;
		}
		case DlOperator::Xor: { // X\xorY = (X\implyY)\imply(X\nimpliedY) = (X\implyY)\imply\not(Y\implyX)
			shared_ptr<DlFormula> X = argumentNode(0);
			shared_ptr<DlFormula> Y = argumentNode(1);
			shared_ptr<DlFormula> XImplyY = extraBinaryOp(terminalStr_imply(), X, Y);
			shared_ptr<DlFormula> XNimpliedY = extraUnaryOp(terminalStr_not(), extraBinaryOp(terminalStr_imply(), Y, X));
			fillBinaryDestination(terminalStr_imply(), XImplyY, XNimpliedY);
			break;
		}
		case DlOperator::Com: // X\comY is a basic formula
			fillBinaryDestination(terminalStr_com(), argumentNode(0), argumentNode(1));
			break;
		case DlOperator::App: // X\appY = \not(X\com\notY)
			fillUnaryDestination(terminalStr_not(), extraBinaryOp(terminalStr_com(), argumentNode(0), extraUnaryOp(terminalStr_not(), argumentNode(1))));
			break;
		case DlOperator::Not: // \notX is a basic formula
			fillUnaryDestination(terminalStr_not(), argumentNode(0));
			break;
		case DlOperator::Nece: // \neceX is a basic formula
			fillUnaryDestination(terminalStr_nece(), argumentNode(0));
			break;
		case DlOperator::Poss: // \possX = \not\nece\notX
			fillUnaryDestination(terminalStr_not(), extraUnaryOp(terminalStr_nece(), extraUnaryOp(terminalStr_not(), argumentNode(0))));
			break;
		case DlOperator::Obli: { // \obliX = \top\comX = (A\implyA)\comX
			shared_ptr<DlFormula> A = firstVariable();
			fillBinaryDestination(terminalStr_com(), extraBinaryOp(terminalStr_imply(), A, A), argumentNode(0));
			break;
		}
		case DlOperator::Perm: { // \permX = \top\appX = (A\implyA)\appX = \not((A\implyA)\com\notX)
			shared_ptr<DlFormula> A = firstVariable();
			shared_ptr<DlFormula> topComNotX = extraBinaryOp(terminalStr_com(), extraBinaryOp(terminalStr_imply(), A, A), extraUnaryOp(terminalStr_not(), argumentNode(0)));
			fillUnaryDestination(terminalStr_not(), topComNotX);
			break;
		}
		case DlOperator::Top: { // \top = A\implyA
			shared_ptr<DlFormula> A = firstVariable();
			fillBinaryDestination(terminalStr_imply(), A, A);
			break;
		}
		case DlOperator::Bot: { // \bot = \not(A\implyA)
			shared_ptr<DlFormula> A = firstVariable();
			fillUnaryDestination(terminalStr_not(), extraBinaryOp(terminalStr_imply(), A, A));
			break;
		}
		}
	} else { // not at an operator, i.e. at a variable
		*destinationNode = *formula; // copy original variable (includes meaning) // NOTE: Meanings of variables are copied regardless of 'calculateMeanings'.
		if (optOut_originals)
			optOut_originals->insert(make_pair(destinationNode, formula));
	}
}

// Returns whether there is a substitution of potentialSchema to formula (and optionally, which)
bool DlCore::isSchemaOf(const shared_ptr<DlFormula>& potentialSchema, const shared_ptr<DlFormula>& formula, map<string, shared_ptr<DlFormula>>* optOut_substitutions) {
	map<string, shared_ptr<DlFormula>> substitutions;
	if (_isSchemaOf(potentialSchema, formula, substitutions)) {
		if (optOut_substitutions) // NOTE: Trivial substitution entries may still be necessary, e.g. when looking for contradictions. Thus do not filter here.
			*optOut_substitutions = substitutions;
		return true;
	} else
		return false;
}

bool DlCore::_isSchemaOf(const shared_ptr<DlFormula>& potentialSchema, const shared_ptr<DlFormula>& formula, map<string, shared_ptr<DlFormula>>& substitutions) {
	const string& potentialSchemaValue = potentialSchema->getValue()->value;
	if (potentialSchema->getChildren().empty() && (potentialSchemaValue != terminalStr_top() && potentialSchemaValue != terminalStr_bot())) { // try to substitute potentialSchema's variable to formula
		pair<map<string, shared_ptr<DlFormula>>::iterator, bool> result = substitutions.try_emplace(potentialSchemaValue, formula);
		if (!result.second)
			return *result.first->second == *formula; // the key was already present => check whether the inserted substitution equals this one
		else
			return true; // newly inserted substitution
	} else { // Do potentialSchema and formula share the same operator?
		if (potentialSchemaValue != formula->getValue()->value)
			return false;
		const vector<shared_ptr<DlFormula>>& potentialSchemaChildren = potentialSchema->getChildren();
		const vector<shared_ptr<DlFormula>>& formulaChildren = formula->getChildren();
		if (potentialSchemaChildren.size() != formulaChildren.size())
			throw domain_error("DlCore::_isSchemaOf(): Nodes represent the same operator '" + potentialSchemaValue + "', but differ in arity (" + to_string(potentialSchemaChildren.size()) + " vs. " + to_string(formulaChildren.size()) + ").");
		for (size_t i = 0; i < potentialSchemaChildren.size(); i++) // check all subformulas
			if (!_isSchemaOf(potentialSchemaChildren[i], formulaChildren[i], substitutions))
				return false;
	}
	return true;
}

bool DlCore::isSchemaOf_polishNotation_noRename_numVars(const string& potentialSchema, const string& formula, map<size_t, string>* optOut_substitutions) {
	map<size_t, string> substitutions;
	string::size_type formulaIndex = 0;
	size_t varNum = 0;
	bool prevVar = false;
	auto readSubstitutedFormula = [&]() -> bool {
		if (prevVar) { // read previous variable first
			string::size_type finalIndex = traverseFormulas_polishNotation_noRename_numVars(formula, formulaIndex);
			string substitutedFormula = formula.substr(formulaIndex, finalIndex - formulaIndex + 1);
			formulaIndex += substitutedFormula.length();
			pair<map<size_t, string>::iterator, bool> emplaceResult = substitutions.emplace(varNum, substitutedFormula);
			if (!emplaceResult.second && emplaceResult.first->second != substitutedFormula)
				return false;
			varNum = 0;
			prevVar = false;
		}
		return true;
	};
	for (char c : potentialSchema)
		switch (c) {
		default:
			if (formulaIndex >= formula.length())
				return false;
			if (!readSubstitutedFormula())
				return false;
			if (formula[formulaIndex++] != c)
				return false;
			break;
		case '.': // NOTE: A schema may contain a '.' without a concrete formula of it containing a corresponding '.'.
			if (!readSubstitutedFormula())
				return false;
			if (formula[formulaIndex] == '.')
				formulaIndex++; // need to traverse an extra '.' to arrive at the next formula
			break;
		case '0':
			varNum = 10 * varNum;
			prevVar = true;
			break;
		case '1':
			varNum = 10 * varNum + 1;
			prevVar = true;
			break;
		case '2':
			varNum = 10 * varNum + 2;
			prevVar = true;
			break;
		case '3':
			varNum = 10 * varNum + 3;
			prevVar = true;
			break;
		case '4':
			varNum = 10 * varNum + 4;
			prevVar = true;
			break;
		case '5':
			varNum = 10 * varNum + 5;
			prevVar = true;
			break;
		case '6':
			varNum = 10 * varNum + 6;
			prevVar = true;
			break;
		case '7':
			varNum = 10 * varNum + 7;
			prevVar = true;
			break;
		case '8':
			varNum = 10 * varNum + 8;
			prevVar = true;
			break;
		case '9':
			varNum = 10 * varNum + 9;
			prevVar = true;
			break;
		}
	if (!readSubstitutedFormula())
		return false;
	if (optOut_substitutions)
		*optOut_substitutions = substitutions;
	return true;
}

bool DlCore::isSchemaOf_polishNotation_noRename_numVars_vec(const string& potentialSchema, const string& formula) {
	vector<string> substitutions;
	string::size_type formulaIndex = 0;
	size_t varNum = 0;
	bool prevVar = false;
	auto readSubstitutedFormula = [&]() -> bool {
		if (prevVar) { // read previous variable first
			string::size_type finalIndex = traverseFormulas_polishNotation_noRename_numVars(formula, formulaIndex);
			string substitutedFormula = formula.substr(formulaIndex, finalIndex - formulaIndex + 1);
			formulaIndex += substitutedFormula.length();
			if (substitutions.size() <= varNum) {
				substitutions.resize(varNum + 1);
				substitutions[varNum] = substitutedFormula;
			} else {
				string& entry = substitutions[varNum];
				if (entry != substitutedFormula) {
					if (entry.empty())
						entry = substitutedFormula;
					else
						return false;
				}
			}
			varNum = 0;
			prevVar = false;
		}
		return true;
	};
	for (char c : potentialSchema)
		switch (c) {
		default:
			if (formulaIndex >= formula.length())
				return false;
			if (!readSubstitutedFormula())
				return false;
			if (formula[formulaIndex++] != c)
				return false;
			break;
		case '.': // NOTE: A schema may contain a '.' without a concrete formula of it containing a corresponding '.'.
			if (!readSubstitutedFormula())
				return false;
			if (formula[formulaIndex] == '.')
				formulaIndex++; // need to traverse an extra '.' to arrive at the next formula
			break;
		case '0':
			varNum = 10 * varNum;
			prevVar = true;
			break;
		case '1':
			varNum = 10 * varNum + 1;
			prevVar = true;
			break;
		case '2':
			varNum = 10 * varNum + 2;
			prevVar = true;
			break;
		case '3':
			varNum = 10 * varNum + 3;
			prevVar = true;
			break;
		case '4':
			varNum = 10 * varNum + 4;
			prevVar = true;
			break;
		case '5':
			varNum = 10 * varNum + 5;
			prevVar = true;
			break;
		case '6':
			varNum = 10 * varNum + 6;
			prevVar = true;
			break;
		case '7':
			varNum = 10 * varNum + 7;
			prevVar = true;
			break;
		case '8':
			varNum = 10 * varNum + 8;
			prevVar = true;
			break;
		case '9':
			varNum = 10 * varNum + 9;
			prevVar = true;
			break;
		}
	if (!readSubstitutedFormula())
		return false;
	return true;
}

bool DlCore::tryUnifyTrees(const shared_ptr<DlFormula>& formulaA, const shared_ptr<DlFormula>& formulaB, map<string, shared_ptr<DlFormula>>* optOut_substitutions, bool debug) {
	map<string, shared_ptr<DlFormula>> substitutions;
	if (_tryUnifyTrees(formulaA, formulaB, substitutions, debug)) {
		if (optOut_substitutions) // NOTE: Trivial substitution entries may still be necessary, e.g. when looking for contradictions. Thus do not filter here.
			*optOut_substitutions = substitutions;
		return true;
	} else
		return false;
}

bool DlCore::_tryUnifyTrees(const shared_ptr<DlFormula>& formulaA, const shared_ptr<DlFormula>& formulaB, map<string, shared_ptr<DlFormula>>& substitutions, bool debug) {
	// Need a comparison function which also tells where the mismatch occurs. We use substitutions implicitly, without actually building all the substituted formulas.
	// NOTE: We only want to substitute once within the same node, so we have to remember whether the recursive call's arguments are formulas within a substituted tree,
	//       i.e. for which of 'lhs' and 'rhs' a substitution has already taken place. It is important to note that not applying a substitution to a side is fine when it
	//       contains no substitutable leaf. But we must apply one whenever a substitutable leaf occurs for the first time (i.e. when not already within substitution value).
	auto formulaEquals = [&](const shared_ptr<DlFormula>& lhs, const shared_ptr<DlFormula>& rhs, const auto& me, pair<shared_ptr<DlFormula>, shared_ptr<DlFormula>>& mismatch, bool withinSubstLhs, bool withinSubstRhs) -> bool {
		if (lhs.get() == rhs.get())
			return true; // pointer type (here: DlFormula*) comparison
		string& lhsValue = lhs->getValue()->value;
		string& rhsValue = rhs->getValue()->value;
		bool lhsHasSubstitution;
		shared_ptr<DlFormula> lhsComp;
		if (withinSubstLhs) {
			lhsHasSubstitution = false; // avoid applying a substitution on the left-hand side when we already have
			lhsComp = lhs;
		} else {
			const vector<shared_ptr<DlFormula>>& lhsChildren = lhs->getChildren();
			map<string, shared_ptr<DlFormula>>::iterator lhsSubstIt;
			lhsHasSubstitution = lhsChildren.empty() && (lhsSubstIt = substitutions.find(lhsValue)) != substitutions.end();
			lhsComp = lhsHasSubstitution ? lhsSubstIt->second : lhs;
			withinSubstLhs = lhsHasSubstitution; // remember that we applied a substitution on the left-hand side
		}
		bool rhsHasSubstitution;
		shared_ptr<DlFormula> rhsComp;
		if (withinSubstRhs) {
			rhsHasSubstitution = false; // avoid applying a substitution on the right-hand side when we already have
			rhsComp = rhs;
		} else {
			const vector<shared_ptr<DlFormula>>& rhsChildren = rhs->getChildren();
			map<string, shared_ptr<DlFormula>>::iterator rhsSubstIt;
			rhsHasSubstitution = rhsChildren.empty() && (rhsSubstIt = substitutions.find(rhsValue)) != substitutions.end();
			rhsComp = rhsHasSubstitution ? rhsSubstIt->second : rhs;
			withinSubstRhs = rhsHasSubstitution; // remember that we applied a substitution on the right-hand side
		}
		const string& lhsCompValue = lhsHasSubstitution ? lhsComp->getValue()->value : lhsValue;
		const string& rhsCompValue = rhsHasSubstitution ? rhsComp->getValue()->value : rhsValue;
		if (lhsCompValue != rhsCompValue) { // string comparison
			mismatch = make_pair(lhsComp, rhsComp); // store mismatching formulas
			if (debug)
				cout << "Mismatch since " << lhsCompValue << " != " << rhsCompValue << ", for formulas: " << formulaRepresentation_traverse(lhsComp) << " and " << formulaRepresentation_traverse(rhsComp) << "." << endl;
			return false;
		}
		const vector<shared_ptr<DlFormula>>& lhsCompChildren = lhsComp->getChildren();
		const vector<shared_ptr<DlFormula>>& rhsCompChildren = rhsComp->getChildren();
		if (lhsCompChildren.size() != rhsCompChildren.size()) // integer comparison
			throw domain_error("DlCore::_tryUnifyTrees(): Nodes represent the same operator '" + lhs->getValue()->value + "', but differ in arity (" + to_string(lhsCompChildren.size()) + " vs. " + to_string(rhsCompChildren.size()) + ").");
		for (size_t i = 0; i < lhsCompChildren.size(); i++)
			if (!me(lhsCompChildren[i], rhsCompChildren[i], me, mismatch, withinSubstLhs, withinSubstRhs)) { // recursive DL-formula comparison
				// No need to store mismatching formulas here, since that would happen in the recursive call.
				return false;
			}
		return true;
	};

	// Essentially, loop while (*substitute(formulaA, substitutions) != *substitute(formulaB, substitutions)).
	// But use the substitution in the equals function instead of actually constructing the formulas each time.
	// Furthermore, the mismatching subformulas are returned when the formulas are not equal.
	pair<shared_ptr<DlFormula>, shared_ptr<DlFormula>> mismatch;
	while (!formulaEquals(formulaA, formulaB, formulaEquals, mismatch, false, false)) {
		const shared_ptr<DlFormula>& mismatchInA = mismatch.first;
		const shared_ptr<DlFormula>& mismatchInB = mismatch.second;
		const string& mismatchInAValue = mismatchInA->getValue()->value;
		const string& mismatchInBValue = mismatchInB->getValue()->value;
		bool mismatchInAIsVariable = mismatchInA->getChildren().empty() && (mismatchInAValue != terminalStr_top() && mismatchInAValue != terminalStr_bot());
		bool mismatchInBIsVariable = mismatchInB->getChildren().empty() && (mismatchInBValue != terminalStr_top() && mismatchInBValue != terminalStr_bot());
		if (!mismatchInAIsVariable && !mismatchInBIsVariable) {
			if (debug)
				cerr << "DlCore::_tryUnifyTrees(): Cannot unify a mismatch between two non-variables. Formulas: " << formulaRepresentation_traverse(mismatchInA) << " and " << formulaRepresentation_traverse(mismatchInB) << "." << endl;
			return false;
		}
		const string& mismatchVariableValue = mismatchInBIsVariable ? mismatchInBValue : mismatchInAValue; // NOTE: We want to preferably keep variables in formulaA, i.e. map variables in formulaB to substituted subtrees of formulaA.
		shared_ptr<DlFormula> mismatchTerm = mismatchInBIsVariable ? mismatchInA : mismatchInB;
		if (primitivesOfFormula(mismatchTerm).count(mismatchVariableValue)) {
			if (debug)
				cerr << "DlCore::_tryUnifyTrees(): Cannot unify a mismatch between a variable and a formula that contains said variable. Formulas: " << formulaRepresentation_traverse(mismatchInA) << " and " << formulaRepresentation_traverse(mismatchInB) << "." << endl;
			return false;
		}

		// Now that we have received a substitution entry that is calculated as if substitutions previously applied, we must first apply substitutions on mismatchTerm.
		mismatchTerm = substitute(mismatchTerm, substitutions);

		// Calculate substitutions = substitutions[mismatchVariableValue/mismatchTerm] (sequential composition)
		map<string, shared_ptr<DlFormula>> singleSubstitution = { { mismatchVariableValue, mismatchTerm } };
		for (pair<const string, shared_ptr<DlFormula>>& p : substitutions)
			p.second = substitute(p.second, singleSubstitution); // insert substitution step into substitutions
		if (!substitutions.count(mismatchVariableValue))
			substitutions.insert(singleSubstitution.begin(), singleSubstitution.end()); // insert the pair when the substitution does not yet handle mismatchVariable
		if (debug)
			cout << "Next substitution:\n" << substitutionRepresentation_traverse(substitutions) << endl;
	}
	return true;
}

string DlCore::formulaRepresentation_traverse(const shared_ptr<DlFormula>& formula) {
	stringstream ss;
	traverseLeftToRightInOrder(formula, [&](const shared_ptr<DlFormula>& node) {
		ss << node->getValue()->value;
	}, [&](const shared_ptr<DlFormula>& node, const shared_ptr<DlFormula>& child) {
		if (child->getChildren().size() >= 2)
			ss << "(";
	}, [&](const shared_ptr<DlFormula>& child, const shared_ptr<DlFormula>& node) {
		if (child->getChildren().size() >= 2)
			ss << ")";
	});
	return ss.str();
}

string DlCore::standardFormulaRepresentation(const shared_ptr<DlFormula>& formula) {
	return formula->getChildren().size() >= 2 ? "(" + formulaRepresentation_traverse(formula) + ")" : formulaRepresentation_traverse(formula);
}

size_t DlCore::standardFormulaLength(const shared_ptr<DlFormula>& formula) {
	size_t len = 0;
	traverseLeftToRightInOrder(formula, [&](const shared_ptr<DlFormula>& node) {
		len++;
	}, [&](const shared_ptr<DlFormula>& node, const shared_ptr<DlFormula>& child) {
		if (child->getChildren().size() >= 2)
			len++;
	}, [&](const shared_ptr<DlFormula>& child, const shared_ptr<DlFormula>& node) {
		if (child->getChildren().size() >= 2)
			len++;
	});
	if (formula->getChildren().size() >= 2)
		len += 2;
	return len;
}

void DlCore::traverseLeftToRightInOrder(const shared_ptr<DlFormula>& formula, const function<void(const shared_ptr<DlFormula>&)>& fVisit, const function<void(const shared_ptr<DlFormula>&, const shared_ptr<DlFormula>&)>& fDown, const function<void(const shared_ptr<DlFormula>&, const shared_ptr<DlFormula>&)>& fUp) {
	const vector<shared_ptr<DlFormula>>& children = formula->getChildren();
	switch (children.size()) {
	case 0:
		fVisit(formula);
		break;
	case 1:
		fVisit(formula);
		fDown(formula, children[0]);
		traverseLeftToRightInOrder(children[0], fVisit, fDown, fUp);
		fUp(children[0], formula);
		break;
	case 2:
		fDown(formula, children[0]);
		traverseLeftToRightInOrder(children[0], fVisit, fDown, fUp);
		fUp(children[0], formula);
		fVisit(formula);
		fDown(formula, children[1]);
		traverseLeftToRightInOrder(children[1], fVisit, fDown, fUp);
		fUp(children[1], formula);
		break;
	default:
		throw domain_error("DlCore::traverseLeftToRightInOrder(): There are too many children (" + to_string(children.size()) + ").");
		break;
	}
}

string DlCore::toPolishNotation(const shared_ptr<DlFormula>& f, bool prioritizeBochenski, const map<string, string>* customOperatorTranslation, const map<string, string>* customVariableTranslation, const vector<string>& sequenceOfVarNames) {
	// NOTE: In Bocheński notation \nimply and \nimplied are L and M, but in Łukasiewicz notation those are already taken by \nece and \poss, respectively.
	static const unordered_map<string, string> operatorNames_luk = { { terminalStr_and(), "K" }, { terminalStr_or(), "A" }, { terminalStr_nand(), "D" }, { terminalStr_nor(), "X" }, { terminalStr_imply(), "C" }, { terminalStr_implied(), "B" }, { terminalStr_nimply(), "F" }, { terminalStr_nimplied(), "G" }, { terminalStr_equiv(), "E" }, { terminalStr_xor(), "J" }, { terminalStr_com(), "S" }, { terminalStr_app(), "U" }, { terminalStr_not(), "N" }, { terminalStr_nece(), "L" }, { terminalStr_poss(), "M" }, { terminalStr_obli(), "Z" }, { terminalStr_perm(), "P" }, { terminalStr_top(), "V" }, { terminalStr_bot(), "O" } };
	static const unordered_map<string, string> operatorNames_boc = { { terminalStr_and(), "K" }, { terminalStr_or(), "A" }, { terminalStr_nand(), "D" }, { terminalStr_nor(), "X" }, { terminalStr_imply(), "C" }, { terminalStr_implied(), "B" }, { terminalStr_nimply(), "L" }, { terminalStr_nimplied(), "M" }, { terminalStr_equiv(), "E" }, { terminalStr_xor(), "J" }, { terminalStr_com(), "S" }, { terminalStr_app(), "U" }, { terminalStr_not(), "N" }, { terminalStr_nece(), "H" }, { terminalStr_poss(), "I" }, { terminalStr_obli(), "Z" }, { terminalStr_perm(), "P" }, { terminalStr_top(), "V" }, { terminalStr_bot(), "O" } };
	const unordered_map<string, string>& operatorNames = prioritizeBochenski ? operatorNames_boc : operatorNames_luk;

	map<string, string> operatorTranslations;
	if (customOperatorTranslation)
		operatorTranslations = *customOperatorTranslation;
	map<string, string> variableTranslations;
	if (customVariableTranslation)
		variableTranslations = *customVariableTranslation;
	size_t nextVariableIndex = 0;
	auto recurse = [&](const shared_ptr<DlFormula>& node, const auto& me) -> string {
		auto valToString = [&](const string& s) -> string {
			// 1. Operator names
			map<string, string>::const_iterator itOperator = operatorTranslations.find(s);
			if (itOperator == operatorTranslations.end()) {
				unordered_map<string, string>::const_iterator searchResult = operatorNames.find(s);
				if (searchResult != operatorNames.end())
					return operatorTranslations[s] = searchResult->second;
			} else
				return itOperator->second;
			if (dlOperators().count(s))
				return operatorTranslations[s] = "<" + s + ">"; // unsupported operator

			// 2. Variable names
			map<string, string>::const_iterator itVariable = variableTranslations.find(s);
			if (itVariable == variableTranslations.end()) {
				if (nextVariableIndex >= sequenceOfVarNames.size())
					return variableTranslations[s] = "<" + s + ">"; // unsupported variable
				return variableTranslations[s] = sequenceOfVarNames[nextVariableIndex++];
			} else
				return itVariable->second;
		};
		string str = valToString(node->getValue()->value);
		for (size_t i = 0; i < node->getChildren().size(); i++)
			str += me(node->getChildren()[i], me);
		return str;
	};
	return recurse(f, recurse);
}

string DlCore::toPolishNotation_noRename(const shared_ptr<DlFormula>& f, bool prioritizeBochenski) {
	// NOTE: In Bocheński notation \nimply and \nimplied are L and M, but in Łukasiewicz notation those are already taken by \nece and \poss, respectively.
	static const unordered_map<string, string> operatorNames_luk = { { terminalStr_and(), "K" }, { terminalStr_or(), "A" }, { terminalStr_nand(), "D" }, { terminalStr_nor(), "X" }, { terminalStr_imply(), "C" }, { terminalStr_implied(), "B" }, { terminalStr_nimply(), "F" }, { terminalStr_nimplied(), "G" }, { terminalStr_equiv(), "E" }, { terminalStr_xor(), "J" }, { terminalStr_com(), "S" }, { terminalStr_app(), "U" }, { terminalStr_not(), "N" }, { terminalStr_nece(), "L" }, { terminalStr_poss(), "M" }, { terminalStr_obli(), "Z" }, { terminalStr_perm(), "P" }, { terminalStr_top(), "V" }, { terminalStr_bot(), "O" } };
	static const unordered_map<string, string> operatorNames_boc = { { terminalStr_and(), "K" }, { terminalStr_or(), "A" }, { terminalStr_nand(), "D" }, { terminalStr_nor(), "X" }, { terminalStr_imply(), "C" }, { terminalStr_implied(), "B" }, { terminalStr_nimply(), "L" }, { terminalStr_nimplied(), "M" }, { terminalStr_equiv(), "E" }, { terminalStr_xor(), "J" }, { terminalStr_com(), "S" }, { terminalStr_app(), "U" }, { terminalStr_not(), "N" }, { terminalStr_nece(), "H" }, { terminalStr_poss(), "I" }, { terminalStr_obli(), "Z" }, { terminalStr_perm(), "P" }, { terminalStr_top(), "V" }, { terminalStr_bot(), "O" } };
	const unordered_map<string, string>& operatorNames = prioritizeBochenski ? operatorNames_boc : operatorNames_luk;

	auto recurse = [&](const shared_ptr<DlFormula>& node, bool& startsWithVar, bool& endsWithVar, const auto& me) -> string {
		auto valToString = [&](const string& s, bool& isVar) -> string {
			// 1. Operator names
			unordered_map<string, string>::const_iterator searchResult = operatorNames.find(s);
			if (searchResult != operatorNames.end()) {
				isVar = false;
				return searchResult->second;
			}

			// 2. Variable names
			isVar = true;
			return s;
		};
		string str = valToString(node->getValue()->value, startsWithVar);
		bool prevEndsWithVar = startsWithVar;
		for (size_t i = 0; i < node->getChildren().size(); i++) {
			bool childStartsWithVar, childEndsWithVar;
			string tmp = me(node->getChildren()[i], childStartsWithVar, childEndsWithVar, me);
			str += prevEndsWithVar && childStartsWithVar ? "." + tmp : tmp;
			prevEndsWithVar = childEndsWithVar;
		}
		endsWithVar = prevEndsWithVar;
		return str;
	};
	bool x, y;
	return recurse(f, x, y, recurse);
}

string DlCore::toPolishNotation_numVars(const shared_ptr<DlFormula>& f, bool prioritizeBochenski) {
	// NOTE: In Bocheński notation \nimply and \nimplied are L and M, but in Łukasiewicz notation those are already taken by \nece and \poss, respectively.
	static const unordered_map<string, string> operatorNames_luk = { { terminalStr_and(), "K" }, { terminalStr_or(), "A" }, { terminalStr_nand(), "D" }, { terminalStr_nor(), "X" }, { terminalStr_imply(), "C" }, { terminalStr_implied(), "B" }, { terminalStr_nimply(), "F" }, { terminalStr_nimplied(), "G" }, { terminalStr_equiv(), "E" }, { terminalStr_xor(), "J" }, { terminalStr_com(), "S" }, { terminalStr_app(), "U" }, { terminalStr_not(), "N" }, { terminalStr_nece(), "L" }, { terminalStr_poss(), "M" }, { terminalStr_obli(), "Z" }, { terminalStr_perm(), "P" }, { terminalStr_top(), "V" }, { terminalStr_bot(), "O" } };
	static const unordered_map<string, string> operatorNames_boc = { { terminalStr_and(), "K" }, { terminalStr_or(), "A" }, { terminalStr_nand(), "D" }, { terminalStr_nor(), "X" }, { terminalStr_imply(), "C" }, { terminalStr_implied(), "B" }, { terminalStr_nimply(), "L" }, { terminalStr_nimplied(), "M" }, { terminalStr_equiv(), "E" }, { terminalStr_xor(), "J" }, { terminalStr_com(), "S" }, { terminalStr_app(), "U" }, { terminalStr_not(), "N" }, { terminalStr_nece(), "H" }, { terminalStr_poss(), "I" }, { terminalStr_obli(), "Z" }, { terminalStr_perm(), "P" }, { terminalStr_top(), "V" }, { terminalStr_bot(), "O" } };
	const unordered_map<string, string>& operatorNames = prioritizeBochenski ? operatorNames_boc : operatorNames_luk;

	vector<string> variables = DlCore::primitivesOfFormula_ordered(f);
	unordered_map<string, string> variableTranslation;
	unsigned counter = 0;
	for (const string& v : variables)
		variableTranslation.emplace(v, to_string(counter++));

	auto recurse = [&](const shared_ptr<DlFormula>& node, bool& startsWithVar, bool& endsWithVar, const auto& me) -> string {
		auto valToString = [&](const string& s, bool& isVar) -> string {
			// 1. Operator names
			unordered_map<string, string>::const_iterator searchResult = operatorNames.find(s);
			if (searchResult != operatorNames.end()) {
				isVar = false;
				return searchResult->second;
			}

			// 2. Variable names
			isVar = true;
			return variableTranslation.at(s);
		};
		string str = valToString(node->getValue()->value, startsWithVar);
		bool prevEndsWithVar = startsWithVar;
		for (size_t i = 0; i < node->getChildren().size(); i++) {
			bool childStartsWithVar, childEndsWithVar;
			string tmp = me(node->getChildren()[i], childStartsWithVar, childEndsWithVar, me);
			str += prevEndsWithVar && childStartsWithVar ? "." + tmp : tmp;
			prevEndsWithVar = childEndsWithVar;
		}
		endsWithVar = prevEndsWithVar;
		return str;
	};
	bool x, y;
	return recurse(f, x, y, recurse);
}

bool DlCore::fromPolishNotation(shared_ptr<DlFormula>& output, const string& input, bool prioritizeBochenski, bool debug) {
	static tbb::concurrent_unordered_map<string, shared_ptr<String>> vars;
	auto obtainDefiniteVarSymbol = [](const string& s) -> const shared_ptr<String>& { // i.e. make_shared<String>(s), but definite for each variable name s
		tbb::concurrent_unordered_map<string, shared_ptr<String>>::const_iterator searchResult = vars.find(s);
		return searchResult == vars.end() ? vars.emplace(s, make_shared<String>(s)).first->second : searchResult->second;
	};
	static const unordered_map<char, DlOperator> operators_luk = { { 'K', DlOperator::And }, { 'A', DlOperator::Or }, { 'D', DlOperator::Nand }, { 'X', DlOperator::Nor }, { 'C', DlOperator::Imply }, { 'B', DlOperator::Implied }, { 'F', DlOperator::Nimply }, { 'G', DlOperator::Nimplied }, { 'E', DlOperator::Equiv }, { 'J', DlOperator::Xor }, { 'S', DlOperator::Com }, { 'U', DlOperator::App }, { 'N', DlOperator::Not }, { 'L', DlOperator::Nece }, { 'M', DlOperator::Poss }, { 'Z', DlOperator::Obli }, { 'P', DlOperator::Perm }, { 'V', DlOperator::Top }, { 'O', DlOperator::Bot } };
	static const unordered_map<char, DlOperator> operators_boc = { { 'K', DlOperator::And }, { 'A', DlOperator::Or }, { 'D', DlOperator::Nand }, { 'X', DlOperator::Nor }, { 'C', DlOperator::Imply }, { 'B', DlOperator::Implied }, { 'L', DlOperator::Nimply }, { 'M', DlOperator::Nimplied }, { 'E', DlOperator::Equiv }, { 'J', DlOperator::Xor }, { 'S', DlOperator::Com }, { 'U', DlOperator::App }, { 'N', DlOperator::Not }, { 'H', DlOperator::Nece }, { 'I', DlOperator::Poss }, { 'Z', DlOperator::Obli }, { 'P', DlOperator::Perm }, { 'V', DlOperator::Top }, { 'O', DlOperator::Bot } };
	const unordered_map<char, DlOperator>& operators = prioritizeBochenski ? operators_boc : operators_luk;
	deque<shared_ptr<DlFormula>> stack;
	for (int64_t i = static_cast<int64_t>(input.length()) - 1; i >= 0; i--) {
		char c = input[i];
		if (c == '>') { // unsupported variable ending
			string::size_type start = input.rfind('<', i);
			if (start == string::npos) {
				if (debug)
					cerr << "Parse error: Missing '<'." << endl;
				return false;
			} else if (start + 1 == (string::size_type) i) {
				if (debug)
					cerr << "Parse error: Empty variable name in \"<>\"." << endl;
				return false;
			} else if (debug && start + 2 == (string::size_type) i && 'a' <= input[start + 1] && input[start + 1] <= 'z')
				cerr << "Warning: Variable '" << string { input[start + 1] } << "' from \"<" << string { input[start + 1] } << ">\" might be merged. To circumvent this, avoid names 'a', 'b', ..., 'z' for variables that occur as 27th or later." << endl;
			stack.push_back(make_shared<DlFormula>(obtainDefiniteVarSymbol(input.substr(start + 1, i - start - 1))));
			i = start;
		} else {
			unordered_map<char, DlOperator>::const_iterator searchResult = operators.find(c);
			if (searchResult == operators.end())
				stack.push_back(make_shared<DlFormula>(obtainDefiniteVarSymbol(string { c })));
			else { // NOTE: It is assumed that all operators are addressed by 'operators', everything else will be treated as a variable.
				DlOperator op = searchResult->second;
				unsigned arity = dlOperatorArity(op);
				if (stack.size() < arity) {
					if (debug)
						cerr << "Parse error: Missing variable for '" << string { c } << "' (alias " << dlOperatorToString(op) << ") at index " << i << "." << endl;
					return false;
				}
				switch (arity) {
				case 0:
					stack.push_back(make_shared<DlFormula>(obtainDefiniteVarSymbol(dlOperatorToString(op))));
					break;
				case 1:
					stack.back() = make_shared<DlFormula>(obtainDefiniteOpSymbol(op), vector<shared_ptr<DlFormula>> { stack.back() });
					break;
				case 2: {
					shared_ptr<DlFormula> term = make_shared<DlFormula>(obtainDefiniteOpSymbol(op), vector<shared_ptr<DlFormula>> { stack.back(), stack[stack.size() - 2] });
					stack.pop_back();
					stack.back() = term;
					break;
				}
				default:
					throw logic_error("DlCore::fromPolishNotation(): Impossible arity (" + to_string(arity) + ") for " + dlOperatorToString(op) + ".");
				}
			}
		}
	}
	if (stack.size() != 1) {
		if (debug)
			cerr << "Parse error: Missing or extra variables resulted in non-singleton stack " << FctHelper::dequeString(stack) << "." << endl;
		return false;
	}
	output = stack[0];
	return true;
}

bool DlCore::fromPolishNotation_noRename(shared_ptr<DlFormula>& output, const string& input, bool prioritizeBochenski, bool debug) {
	static tbb::concurrent_unordered_map<string, shared_ptr<String>> vars;
	auto obtainDefiniteVarSymbol = [](const string& s) -> const shared_ptr<String>& { // i.e. make_shared<String>(s), but definite for each variable name s
		tbb::concurrent_unordered_map<string, shared_ptr<String>>::const_iterator searchResult = vars.find(s);
		return searchResult == vars.end() ? vars.emplace(s, make_shared<String>(s)).first->second : searchResult->second;
	};
	static const unordered_map<char, DlOperator> operators_luk = { { 'K', DlOperator::And }, { 'A', DlOperator::Or }, { 'D', DlOperator::Nand }, { 'X', DlOperator::Nor }, { 'C', DlOperator::Imply }, { 'B', DlOperator::Implied }, { 'F', DlOperator::Nimply }, { 'G', DlOperator::Nimplied }, { 'E', DlOperator::Equiv }, { 'J', DlOperator::Xor }, { 'S', DlOperator::Com }, { 'U', DlOperator::App }, { 'N', DlOperator::Not }, { 'L', DlOperator::Nece }, { 'M', DlOperator::Poss }, { 'Z', DlOperator::Obli }, { 'P', DlOperator::Perm }, { 'V', DlOperator::Top }, { 'O', DlOperator::Bot } };
	static const unordered_map<char, DlOperator> operators_boc = { { 'K', DlOperator::And }, { 'A', DlOperator::Or }, { 'D', DlOperator::Nand }, { 'X', DlOperator::Nor }, { 'C', DlOperator::Imply }, { 'B', DlOperator::Implied }, { 'L', DlOperator::Nimply }, { 'M', DlOperator::Nimplied }, { 'E', DlOperator::Equiv }, { 'J', DlOperator::Xor }, { 'S', DlOperator::Com }, { 'U', DlOperator::App }, { 'N', DlOperator::Not }, { 'H', DlOperator::Nece }, { 'I', DlOperator::Poss }, { 'Z', DlOperator::Obli }, { 'P', DlOperator::Perm }, { 'V', DlOperator::Top }, { 'O', DlOperator::Bot } };
	const unordered_map<char, DlOperator>& operators = prioritizeBochenski ? operators_boc : operators_luk;
	deque<shared_ptr<DlFormula>> stack;
	string::size_type varLast = string::npos;
	for (int64_t i = static_cast<int64_t>(input.length()) - 1; i >= 0; i--) {
		char c = input[i];
		if (c == '.') { // separator of variables
			if (varLast == string::npos) {
				if (debug)
					cerr << "Parse error: Separator '.' does not precede a variable at index " << i << "." << endl;
				return false;
			}
			stack.push_back(make_shared<DlFormula>(obtainDefiniteVarSymbol(input.substr(i + 1, varLast - i)))); // register completed variable
			varLast = string::npos;
		} else {
			unordered_map<char, DlOperator>::const_iterator searchResult = operators.find(c);
			if (searchResult == operators.end()) {
				if (varLast == string::npos)
					varLast = i;
			} else { // NOTE: It is assumed that all operators are addressed by 'operators', everything else will be treated as a variable.
				if (varLast != string::npos) {
					stack.push_back(make_shared<DlFormula>(obtainDefiniteVarSymbol(input.substr(i + 1, varLast - i)))); // first register completed variable
					varLast = string::npos;
				}
				DlOperator op = searchResult->second;
				unsigned arity = dlOperatorArity(op);
				if (stack.size() < arity) {
					if (debug)
						cerr << "Parse error: Missing variable for '" << string { c } << "' (alias " << dlOperatorToString(op) << ") at index " << i << "." << endl;
					return false;
				}
				switch (arity) {
				case 0:
					stack.push_back(make_shared<DlFormula>(obtainDefiniteOpSymbol(op)));
					break;
				case 1:
					stack.back() = make_shared<DlFormula>(obtainDefiniteOpSymbol(op), vector<shared_ptr<DlFormula>> { stack.back() });
					break;
				case 2: {
					shared_ptr<DlFormula> term = make_shared<DlFormula>(obtainDefiniteOpSymbol(op), vector<shared_ptr<DlFormula>> { stack.back(), stack[stack.size() - 2] });
					stack.pop_back();
					stack.back() = term;
					break;
				}
				default:
					throw logic_error("DlCore::fromPolishNotation(): Impossible arity (" + to_string(arity) + ") for " + dlOperatorToString(op) + ".");
				}
			}
		}
	}
	if (varLast != string::npos) // still need to register variable
		stack.push_back(make_shared<DlFormula>(obtainDefiniteVarSymbol(input)));
	if (stack.size() != 1) {
		if (debug)
			cerr << "Parse error: Missing or extra variables resulted in non-singleton stack " << FctHelper::dequeString(stack) << "." << endl;
		return false;
	}
	output = stack[0];
	return true;
}

size_t DlCore::symbolicLen_polishNotation_noRename_numVars(const string& formula) {
	size_t repLen = formula.length(); // formula representation length
	size_t substract = 0;
	bool atVar = false;
	for (char c : formula)
		switch (c) {
		default:
			if (atVar)
				atVar = false;
			break;
		case '.':
			substract++;
			if (atVar)
				atVar = false;
			break;
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			if (atVar)
				substract++;
			else
				atVar = true;
			break;
		}
	return repLen - substract;
}

size_t DlCore::symbolicLen_polishNotation_noRename_numVars(const string& formula, string::size_type startIndex) {
	size_t repLen = formula.length() - startIndex; // formula representation length
	size_t substract = 0;
	bool atVar = false;
	for (string::const_iterator it = formula.begin() + startIndex; it != formula.end(); ++it)
		switch (*it) {
		default:
			if (atVar)
				atVar = false;
			break;
		case '.':
			substract++;
			if (atVar)
				atVar = false;
			break;
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			if (atVar)
				substract++;
			else
				atVar = true;
			break;
		}
	return repLen - substract;
}

size_t DlCore::standardLen_polishNotation_noRename_numVars(const string& formula) {
	size_t repLen = formula.length(); // formula representation length
	size_t add = 0;
	size_t substract = 0;
	bool atVar = false;
	for (char c : formula)
		switch (c) {
		default:
			if (atVar)
				atVar = false;
			break;
		case '.':
			substract++;
			if (atVar)
				atVar = false;
			break;
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			if (atVar)
				substract++;
			else
				atVar = true;
			break;
		case 'K':
		case 'A':
		case 'D':
		case 'X':
		case 'C':
		case 'B':
		case 'F':
		case 'G':
		case 'E':
		case 'J':
		case 'S':
		case 'U':
			if (atVar)
				atVar = false;
			add += 2;
			break;
		}
	return repLen - substract + add;
}

string::size_type DlCore::traverseFormulas_polishNotation_noRename_numVars(const string& formula, string::size_type startIndex, string::size_type formulasToTraverse) {
	bool prevVar = false;
	string::const_iterator strIt;
	for (strIt = formula.begin() + startIndex; strIt != formula.end(); ++strIt) {
		char c = *strIt;
		switch (c) {
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			prevVar = true; // indicate that possibly we've just completed the formula but don't know it yet
			break;
		case '.': // implies 'prevVar' == true
			if (formulasToTraverse == 1) { // end at previous variable
				strIt = prev(strIt);
				formulasToTraverse = 0;
				break;
			}
			formulasToTraverse--; // completed previous (sub-)formula with a variable
			prevVar = false;
			break;
		case 'V':
		case 'O':
			if (formulasToTraverse == 1 && prevVar) { // end at previous variable
				strIt = prev(strIt);
				formulasToTraverse = 0;
				break;
			}
			if (prevVar)
				formulasToTraverse -= 2; // completed previous (sub-)formula with a variable, and completed this (sub-)formula (which is a nullary operator)
			else
				formulasToTraverse--; // completed this (sub-)formula (which ends with a nullary operator)
			prevVar = false;
			break;
		case 'N':
		case 'L':
		case 'M':
		case 'Z':
		case 'P':
			if (formulasToTraverse == 1 && prevVar) { // end at previous variable
				strIt = prev(strIt);
				formulasToTraverse = 0;
				break;
			}
			if (prevVar)
				formulasToTraverse--; // completed previous (sub-)formula with a variable
			prevVar = false;
			break;
		case 'K':
		case 'A':
		case 'D':
		case 'X':
		case 'C':
		case 'B':
		case 'F':
		case 'G':
		case 'E':
		case 'J':
		case 'S':
		case 'U':
			if (formulasToTraverse == 1 && prevVar) { // end at previous variable
				strIt = prev(strIt);
				formulasToTraverse = 0;
				break;
			}
			if (!prevVar)
				formulasToTraverse++; // need to read an extra subformula ; otherwise: completed previous (sub-)formula with a variable, and need to read an extra subformula
			prevVar = false;
			break;
		default:
			throw domain_error("Unknown Łukasiewicz operator '" + string { c } + "'.");
		}
		if (!formulasToTraverse)
			break;
	}
	return distance(formula.cbegin(), strIt);
}

string DlCore::substitutionRepresentation_traverse(const map<string, shared_ptr<DlFormula>>& substitutions) {
	return FctHelper::mapStringF(substitutions, [](const pair<string, shared_ptr<DlFormula>>& pair) { return "\u3008" + pair.first + ", " + formulaRepresentation_traverse(pair.second) + "\u3009"; }, { }, { });
}

shared_ptr<DlFormula> DlCore::substitute(const shared_ptr<DlFormula>& formula, const map<string, shared_ptr<DlFormula>>& substitutions) {
	shared_ptr<DlFormula> rootNode = make_shared<DlFormula>(make_shared<String>());
	_substitute(rootNode, formula, substitutions);
	return rootNode;
}

void DlCore::_substitute(const shared_ptr<DlFormula>& destinationNode, const shared_ptr<DlFormula>& formula, const map<string, shared_ptr<DlFormula>>& substitutions) {
	if (formula->getChildren().empty()) { // Substitutions can only happen in leaves.
		map<string, shared_ptr<DlFormula>>::const_iterator searchResult = substitutions.find(formula->getValue()->value);
		if (searchResult != substitutions.end())
			*destinationNode = *searchResult->second; // substitute (includes meaning)
		else
			*destinationNode = *formula; // copy original primitive (includes meaning)
	} else {
		for (const shared_ptr<DlFormula>& subformula : formula->getChildren()) {
			shared_ptr<DlFormula> childNode = make_shared<DlFormula>(make_shared<String>());
			destinationNode->addChild(childNode);
			_substitute(childNode, subformula, substitutions);
		}
		destinationNode->getValue()->value = formula->getValue()->value; // take original value
		recalculateMeaningUsingMeaningOfChildren(destinationNode);
	}
}

void DlCore::calculateEmptyMeanings(const shared_ptr<DlFormula>& formula) { // NOTE: Does the same as reduceFormulaMeaning_modifying(), except it reduces changes to empty meanings and does not return its (modified) input.
	if (formula->meaning().empty()) {
		if (formula->getChildren().empty()) {
			const string& value = formula->getValue()->value;
			tbb::concurrent_map<string, vector<uint32_t>>::const_iterator itVariable = labelToTerminalSymbols_variables().find(value);
			if (itVariable != labelToTerminalSymbols_variables().end())
				formula->meaning() = itVariable->second; // recalculate meaning of variable
			else if (value == terminalStr_bot())
				formula->meaning() = { DlStructure::terminal_bot() }; // recalculate meaning of \\bot
			else if (value == terminalStr_top())
				formula->meaning() = { DlStructure::terminal_top() }; // recalculate meaning of \\top
			else {
				vector<uint32_t> variableNameSequence;
				if (value.find(' ') == string::npos && tryRegisterVariable(value, &variableNameSequence)) // Could not find such a variable, can define?
					formula->meaning() = variableNameSequence; // recalculate meaning of new variable
				else
					throw domain_error("DlCore::calculateEmptyMeanings(): Could not define variable '" + value + "'.");
			}
		} else {
			for (const shared_ptr<DlFormula>& subformula : formula->getChildren())
				calculateEmptyMeanings(subformula);
			recalculateMeaningUsingMeaningOfChildren(formula);
		}
	}
}

// NOTE: Supports search trees, so it can be used in DlFormulaStructuralSearchInfo::toSearchTree().
void DlCore::recalculateMeaningUsingMeaningOfChildren(const shared_ptr<DlFormula>& destinationNode) {
	const vector<shared_ptr<DlFormula>>& children = destinationNode->getChildren();
	if (children.empty()) // destinationNode requires to have at least one child node
		throw invalid_argument("DlCore::recalculateMeaningUsingMeaningOfChildren(): There shall be children.");
	vector<uint32_t>& meaning = destinationNode->meaning();
	meaning.clear();
	uint32_t opTerminal = grammar().idLookup(destinationNode->getValue()->value);
	const vector<uint32_t>& childAMeaning = children.front()->getMeaning();
	bool needToSurroundA = false; // If there is a binary operator in childAMeaning at depth 0, we may have to surround childAMeaning with parentheses.
	int depth = 0;
	bool unary = children.size() == 1;
	for (uint32_t symbol : childAMeaning)
		if (symbol == DlStructure::terminal_leftParenthesis())
			depth++;
		else if (symbol == DlStructure::terminal_rightParenthesis())
			depth--;
		else if (depth == 0) {
			if (unary) { // If the operand is unary, we have to surround A if it has a binary operator.
				if (symbol == DlStructure::terminal_and() || symbol == DlStructure::terminal_or() || symbol == DlStructure::terminal_nand() || symbol == DlStructure::terminal_nor() || symbol == DlStructure::terminal_imply() || symbol == DlStructure::terminal_implied() || symbol == DlStructure::terminal_nimply() || symbol == DlStructure::terminal_nimplied() || symbol == DlStructure::terminal_equiv() || symbol == DlStructure::terminal_xor() || symbol == DlStructure::terminal_com() || symbol == DlStructure::terminal_app()) {
					needToSurroundA = true;
					break;
				}
			} else if (opTerminal == DlStructure::terminal_com() || opTerminal == DlStructure::terminal_app()) {
				// If the operand is binary and in {\com, \app}, we have surround A if it has a binary operator that is not in {\com, \app},
				// since the default is to bracket left first, and \com, \app bind stronger than all other binary operators.
				if (symbol == DlStructure::terminal_and() || symbol == DlStructure::terminal_or() || symbol == DlStructure::terminal_nand() || symbol == DlStructure::terminal_nor() || symbol == DlStructure::terminal_imply() || symbol == DlStructure::terminal_implied() || symbol == DlStructure::terminal_nimply() || symbol == DlStructure::terminal_nimplied() || symbol == DlStructure::terminal_equiv() || symbol == DlStructure::terminal_xor()) {
					needToSurroundA = true;
					break;
				}
			} // else : If the operand is binary and not in {\com, \app}, we do not have to surround A, since the default is to bracket left first.
		}
	if (unary) {
		meaning.push_back(opTerminal);
		if (needToSurroundA)
			meaning.push_back(DlStructure::terminal_leftParenthesis());
		meaning.insert(meaning.end(), childAMeaning.begin(), childAMeaning.end());
		if (needToSurroundA)
			meaning.push_back(DlStructure::terminal_rightParenthesis());
	} else { // children.size() == 2
		if (needToSurroundA)
			meaning.push_back(DlStructure::terminal_leftParenthesis());
		meaning.insert(meaning.end(), childAMeaning.begin(), childAMeaning.end());
		if (needToSurroundA)
			meaning.push_back(DlStructure::terminal_rightParenthesis());
		meaning.push_back(opTerminal);
		const vector<uint32_t>& childBMeaning = children.back()->getMeaning();
		bool needToSurroundB = false; // If there is a binary operator in childBMeaning at depth 0, we have to surround childBMeaning with parentheses.
		depth = 0;
		for (uint32_t symbol : childBMeaning)
			if (symbol == DlStructure::terminal_leftParenthesis())
				depth++;
			else if (symbol == DlStructure::terminal_rightParenthesis())
				depth--;
			else if (depth == 0) {
				if (opTerminal != DlStructure::terminal_com() && opTerminal != DlStructure::terminal_app()) { // If the operand is not in {\com, \app}, we do not have to surround com and app.
					if (symbol == DlStructure::terminal_and() || symbol == DlStructure::terminal_or() || symbol == DlStructure::terminal_nand() || symbol == DlStructure::terminal_nor() || symbol == DlStructure::terminal_imply() || symbol == DlStructure::terminal_implied() || symbol == DlStructure::terminal_nimply() || symbol == DlStructure::terminal_nimplied() || symbol == DlStructure::terminal_equiv() || symbol == DlStructure::terminal_xor()) {
						needToSurroundB = true;
						break;
					}
				} else if (symbol == DlStructure::terminal_and() || symbol == DlStructure::terminal_or() || symbol == DlStructure::terminal_nand() || symbol == DlStructure::terminal_nor() || symbol == DlStructure::terminal_imply() || symbol == DlStructure::terminal_implied() || symbol == DlStructure::terminal_nimply() || symbol == DlStructure::terminal_nimplied() || symbol == DlStructure::terminal_equiv() || symbol == DlStructure::terminal_xor() || symbol == DlStructure::terminal_com() || symbol == DlStructure::terminal_app()) {
					needToSurroundB = true;
					break;
				}
			}
		if (needToSurroundB)
			meaning.push_back(DlStructure::terminal_leftParenthesis());
		meaning.insert(meaning.end(), childBMeaning.begin(), childBMeaning.end());
		if (needToSurroundB)
			meaning.push_back(DlStructure::terminal_rightParenthesis());
	}
}

}
}
