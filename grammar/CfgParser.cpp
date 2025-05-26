#include "CfgParser.h"

#include "../helper/FctHelper.h"
#include "CfgGrammar.h"

using namespace std;
using namespace xamidi::tree;
using namespace xamidi::helper;

namespace xamidi {
namespace grammar {

//#######################################################
//#                 Earley Parser                       #
//#######################################################

CfgParser::CfgParser(const CfgGrammar& grammar) :
		_grammar(grammar) {
	// A nonterminal symbol "@" is required for the initial Earley state. Register the symbol if it is still missing.
	// Since that does not change the meaning of the grammar, still treat it as const for convenience.
	const_cast<CfgGrammar&>(_grammar).maybeStoreNonterminal("@");
}

vector<const CfgParserChart*> CfgParser::earleyParse(const vector<uint32_t>& symbolSequence) {
	// Earley parsing ; Used pseudo-code from https://en.wikipedia.org/wiki/Earley_parser
	// INIT(words).. (S is charts - NOTE: Every chart is a state set)
	vector<CfgParserChart*> charts;
	for (size_t i = 0; i <= symbolSequence.size(); i++) {
		CfgParserChart* newChart = new CfgParserChart(*this);
		_chartSmartPtrs.emplace_back(newChart); // Construct a unique_ptr<CfgParserChart> to automatically release the pointer when this class instance is deleted.
		charts.push_back(newChart);
	}

	const shared_ptr<CfgParserState> initialState = make_shared<CfgParserState>(*this, 0, 0, 0, 0, _grammar.idLookup("@"), vector<uint32_t> { _grammar.startSymbolId() }, CfgParserStateProducer::InitialState);
	charts[0]->addState(initialState); // ADD-TO-SET((γ → •S, 0), S[0])

	for (uint64_t k = 0; k <= symbolSequence.size(); k++) { // for k ← from 0 to LENGTH(words) do
		size_t counter = 0;
		vector<uint32_t> predictedNonterminals; // remember which nonterminals have already been predicted
		while (counter < charts[k]->size()) { // continue, if more states can be added
			// for each state in S[k] do ; Note that S[k] receives more elements dynamically ; Queue every element
			const shared_ptr<CfgParserState> state = charts[k]->getState(counter); // NOTE: This cannot be a reference, since changes of vector charts[k]._table may invalidate it.
			if (!state->isComplete()) { // if not FINISHED(state) then
				uint32_t nextElement = state->getCurrentElement();
				if (FctHelper::vectorContains(_grammar.nonterminalIds(), nextElement)) { // if NEXT-ELEMENT-OF(state) is a nonterminal then
					if (!FctHelper::vectorContains(predictedNonterminals, nextElement)) { // only call the predictor for new nonterminals
						predictedNonterminals.push_back(nextElement);
						_predictor(nextElement, k, charts); // PREDICTOR(state, k, grammar) // non-terminal
					}
				} else if (k < symbolSequence.size()) // need to be able to scan the next character of the input
					_scanner(state, k, symbolSequence, charts); // SCANNER(state, k, words) // terminal
			} else
				_completer(state, k, charts); // COMPLETER(state, k)
			counter++;
		}
	}

	// NOTE: We just stick to the "efficient" parse trees.
	//       Alternatively, we could shift final states to the end of their chart in order to generate more (but not all – there are possibly infinitely many) parse trees.

	// Charts are done => Do vector<CfgParserChart*> to vector<const CfgParserChart*> conversion. Takes almost no time (few µs), since only (|sentence| + 1) many pointers are copied.
	vector<const CfgParserChart*> constCharts;
	for (size_t i = 0; i < charts.size(); i++)
		constCharts.push_back(charts[i]);
	return constCharts;
}

void CfgParser::_predictor(uint32_t nonterminal, uint64_t k, const vector<CfgParserChart*>& charts) {
	const vector<vector<uint32_t>>& productions = _grammar.productionRuleOf(nonterminal);
	for (const vector<uint32_t>& production : productions)
		charts[k]->emplaceStateIfNew(*this, k, charts[k]->size(), 0, k, nonterminal, production, CfgParserStateProducer::Predictor);
}

void CfgParser::_scanner(const shared_ptr<CfgParserState>& state, uint64_t k, const vector<uint32_t>& sentence, const vector<CfgParserChart*>& charts) {
	if (sentence[k] == state->getCurrentElement())
		charts[k + 1]->emplaceStateIfNew(*this, state->getOriginChartIndex(), charts[k + 1]->size(), state->getDotIndex() + 1, state->getFinalChartIndex() + 1, state->getNonterminal(), state->getProduction(), state->getPointerPreviousRule(), CfgParserStateProducer::Scanner);
}

void CfgParser::_completer(const shared_ptr<CfgParserState>& state, uint64_t k, const vector<CfgParserChart*>& charts) {
	for (size_t i = 0; i < charts[state->getOriginChartIndex()]->size(); i++) { //                                      For each unfinished state in the origin chart from
		shared_ptr<CfgParserState> stateInOriginChart = charts[state->getOriginChartIndex()]->getState(i);
		if (!stateInOriginChart->isComplete() && stateInOriginChart->getCurrentElement() == state->getNonterminal()) { // nonterminal of the current (completed) state,
			vector<uint64_t> v2(stateInOriginChart->getPointerPreviousRule());
			v2.push_back(state->getStateNumber()); //                                                                     add 'increased' state to chart k.
			charts[k]->emplaceStateIfNew(*this, stateInOriginChart->getOriginChartIndex(), charts[k]->size(), stateInOriginChart->getDotIndex() + 1, state->getFinalChartIndex(), stateInOriginChart->getNonterminal(), stateInOriginChart->getProduction(), v2, CfgParserStateProducer::Completer);
		}
	}
}

//#######################################################
//#                 Parse Tree Generation               #
//#######################################################

const shared_ptr<CfgParserState> _nullptrState = nullptr;
const shared_ptr<CfgParserState>& CfgParser::getFinalState(const vector<const CfgParserChart*>& charts) const {
	for (size_t i = 0; i < charts[charts.size() - 1]->size(); i++) { // find final state in last chart (if it exists)
		const shared_ptr<CfgParserState>& state = charts[charts.size() - 1]->getState(i);
		if (state->equals(_grammar.idLookup("@"), { _grammar.startSymbolId() }, 0, 1))
			return state;
	}
	return _nullptrState;
}

shared_ptr<TreeNode<CfgParserState>> CfgParser::generateEarleyParseTree(const shared_ptr<CfgParserState>& finalState, const vector<const CfgParserChart*>& charts) const {
	// 1. Build map for complete states
	unordered_map<uint64_t, shared_ptr<CfgParserState>> mapCompleteStates;
	for (size_t i = 0; i < charts.size(); i++) {
		const vector<shared_ptr<CfgParserState>>& vec = charts[i]->getTable();
		for (const shared_ptr<CfgParserState>& state : vec)
			if (state->isComplete())
				mapCompleteStates.insert(make_pair(state->getStateNumber(), state));
	}
	// 2. Generate Earley tree
	shared_ptr<TreeNode<CfgParserState>> rootNode = make_shared<TreeNode<CfgParserState>>(finalState);
	return _generateEarleyParseTree(rootNode, mapCompleteStates);
}

shared_ptr<TreeNode<CfgParserState>> CfgParser::_generateEarleyParseTree(const shared_ptr<TreeNode<CfgParserState>>& node, const unordered_map<uint64_t, shared_ptr<CfgParserState>>& mapStates) const {
	for (uint64_t rulePointer : node->getValue()->getPointerPreviousRule()) {
		shared_ptr<TreeNode<CfgParserState>> child = make_shared<TreeNode<CfgParserState>>(mapStates.at(rulePointer));
		node->addChild(_generateEarleyParseTree(child, mapStates));
	}
	return node;
}

//#######################################################
//#           Abstract Syntax Tree Generation           #
//#######################################################

shared_ptr<TreeNode<String>> CfgParser::generateASTFromParseTree(const shared_ptr<TreeNode<CfgParserState>>& parseTree, const vector<string>& terminalsToIgnore) const {
	if (parseTree->getChildren().size() != 1)
		throw invalid_argument("An Earley parse tree root node must have exactly one child.");
	// The root node of an Earley parse tree contains no terminals and has only one child, since its rule is @ -> S, for S being the start symbol.
	// So we can just initialize an empty node for the AST, and propagate it as destination to its child node.
	shared_ptr<TreeNode<String>> rootNode = make_shared<TreeNode<String>>(parseTree->getMeaning(), make_shared<String>());
	_generateASTFromParseTree(rootNode, parseTree->getChildren().back(), terminalsToIgnore);
	return rootNode;
}

void CfgParser::_generateASTFromParseTree(const shared_ptr<TreeNode<String>>& destinationNode, const shared_ptr<TreeNode<CfgParserState>>& stateNode, const vector<string>& terminalsToIgnore) const {
	// Build representational string
	string representation; // Note that after appending symbols here, their borders become indistinguishable (since symbols may consist of multiple characters).
	for (uint32_t symbol : stateNode->getValue()->getProduction()) {
		const string& strSymbol = _grammar.stringOf(symbol);
		if (!_grammar.nonterminalStringLookup().count(symbol) && !FctHelper::vectorContains(terminalsToIgnore, strSymbol))
			representation += strSymbol;
	}

	// Handle children of 'stateNode'
	if (representation.empty()) // No terminal information is here, proceed to children.
		for (const shared_ptr<TreeNode<CfgParserState>>& childStateNode : stateNode->getChildren())
			_generateASTFromParseTree(destinationNode, childStateNode, terminalsToIgnore);
	else { // We can already insert new nodes.
		destinationNode->getValue()->value = representation; // set label of destination
		for (const shared_ptr<TreeNode<CfgParserState>>& childStateNode : stateNode->getChildren()) {
			shared_ptr<TreeNode<String>> childNode = make_shared<TreeNode<String>>(childStateNode->getMeaning(), make_shared<String>());
			destinationNode->addChild(childNode);
			_generateASTFromParseTree(childNode, childStateNode, terminalsToIgnore);
		}
	}
}

//#######################################################
//#         Earley Charts and Parse Tree View           #
//#######################################################

string CfgParser::writeCharts(const string& name, const vector<const CfgParserChart*>& charts, const vector<uint32_t>& sentence) const {
	// 1. Generate variable sized elements and get their maximum lengths
	vector<vector<string>> chartStrings(charts.size());
	string::size_type maxStateInnerStringLength = 0;
	vector<vector<string>> pointersStrings(charts.size());
	string::size_type maxStatePointersLength = 0;
	for (size_t i = 0; i < charts.size(); i++) {
		chartStrings[i] = vector<string>(charts[i]->size());
		pointersStrings[i] = vector<string>(charts[i]->size());
		for (size_t j = 0; j < charts[i]->size(); j++) {
			chartStrings[i][j] = charts[i]->getState(j)->getInnerString();
			if (chartStrings[i][j].length() > maxStateInnerStringLength)
				maxStateInnerStringLength = chartStrings[i][j].length();

			string strPointers("[");
			if (!charts[i]->getState(j)->getPointerPreviousRule().empty())
				for (uint64_t k = 0; k < charts[i]->getState(j)->getPointerPreviousRule().size(); k++) {
					strPointers += string("S") + to_string(charts[i]->getState(j)->getPointerPreviousRule()[k]);
					if (k != charts[i]->getState(j)->getPointerPreviousRule().size() - 1)
						strPointers += string(",");
				}
			strPointers += string("]");
			pointersStrings[i][j] = strPointers;
			if (pointersStrings[i][j].length() > maxStatePointersLength)
				maxStatePointersLength = pointersStrings[i][j].length();
		}
	}

	// 2. Write the charts
	string retVal = name + string(", for input ") + string("[\"") + FctHelper::stringJoin("\",\"", _grammar.stringsOf(sentence)) + string("\"]:\n");
	size_t maxChartIndexStrLen = to_string(charts.size() - 1).length();
	size_t stateIndent = 8;
	size_t ptrsIndent = stateIndent + maxStateInnerStringLength + 5;
	size_t producerIndent = ptrsIndent + maxStatePointersLength + 3;
	for (size_t i = 0; i < charts.size(); i++) {
		string iStr = to_string(i);
		retVal += string("== Chart ") + iStr + string(" ") + string(maxStateInnerStringLength + (maxChartIndexStrLen - iStr.length() - 1), '=');
		retVal += string("\n");
		for (size_t j = 0; j < charts[i]->size(); j++) {
			shared_ptr<CfgParserState> state = charts[i]->getState(j);
			string strChartRow = string("S") + to_string(state->getStateNumber()) + string("  ");
			strChartRow += string(stateIndent > strChartRow.length() ? stateIndent - strChartRow.length() : 0, ' ') + chartStrings[i][j];
			strChartRow += string(ptrsIndent > strChartRow.length() ? ptrsIndent - strChartRow.length() : 0, ' ') + pointersStrings[i][j];
			strChartRow += string(producerIndent > strChartRow.length() ? producerIndent - strChartRow.length() : 0, ' ');
			if (state->getProducer() == CfgParserStateProducer::InitialState)
				strChartRow += string("Initial State");
			else if (state->getProducer() == CfgParserStateProducer::Completer)
				strChartRow += string("Completer");
			else if (state->getProducer() == CfgParserStateProducer::Scanner)
				strChartRow += string("Scanner");
			else if (state->getProducer() == CfgParserStateProducer::Predictor)
				strChartRow += string("Predictor");
			if (i + 1 != charts.size() || j + 1 != charts[i]->size())
				strChartRow += string("\n");
			retVal += strChartRow;
		}
	}
	return retVal;
}

//#######################################################
//#                 Helper Classes                      #
//#######################################################

CfgParserState::CfgParserState(CfgParser& owner, size_t originChartIndex, size_t indexInChart, size_t dotIndex, size_t finalChartIndex, uint32_t nonterminal, const vector<uint32_t>& production, const CfgParserStateProducer& producer) :
		CfgParserState(owner, originChartIndex, indexInChart, dotIndex, finalChartIndex, nonterminal, production, { }, producer) {
}

CfgParserState::CfgParserState(CfgParser& owner, size_t originChartIndex, size_t indexInChart, size_t dotIndex, size_t finalChartIndex, uint32_t nonterminal, const vector<uint32_t>& production, const vector<uint64_t>& pointerPreviousRule, const CfgParserStateProducer& producer) :
		_owner(owner), _grammar(owner._grammar) {
	_stateNumber = owner._stateNumberCounter++;
	_originChartIndex = originChartIndex;
	_indexInChart = indexInChart;
	_dotIndex = dotIndex;
	_finalChartIndex = finalChartIndex;
	_nonterminal = nonterminal;
	_rule.push_back(nonterminal);
	for (size_t i = 0; i < production.size(); i++) {
		_rule.push_back(production[i]);
		_production.push_back(production[i]);
	}
	_producer = producer;
	_pointerPreviousRule = pointerPreviousRule;
}

bool CfgParserState::isComplete() const {
	return _dotIndex + 1 >= _rule.size();
}

bool CfgParserState::isInitial() const {
	return _dotIndex == 0;
}

uint32_t CfgParserState::getCurrentElement() const {
	if (isComplete())
		throw logic_error("There is no current element, this state is already complete!");
	else
		return _production[_dotIndex];
}

uint32_t CfgParserState::getPreviousElement() const {
	if (isInitial())
		throw logic_error("There is no previous element, this state is initial!");
	else
		return _production[_dotIndex - 1];
}

uint32_t CfgParserState::getProductionNonterminalByIndex(size_t index) const {
	size_t nonterminalIndex = 0;
	for (size_t i = 0; i < _production.size(); i++)
		if (FctHelper::vectorContains(_grammar.nonterminalIds(), _production[i])) {
			if (nonterminalIndex == index)
				return _production[i];
			nonterminalIndex++;
		}
	throw out_of_range(string("There is no nonterminal in the production rule of ") + toString() + string(" with the given index."));
}

size_t CfgParserState::getProductionNonterminalIndexByDotIndex(size_t dotIndex) const {
	if (dotIndex >= _production.size())
		throw invalid_argument("The dot index is invalid.");
	else if (!FctHelper::vectorContains(_grammar.nonterminalIds(), _production[dotIndex]))
		throw invalid_argument("There is no nonterminal at the given index.");
	size_t nonterminalIndex = 0;
	for (size_t i = dotIndex - 1; i != size_t(-1); i--)
		if (FctHelper::vectorContains(_grammar.nonterminalIds(), _production[i]))
			nonterminalIndex++;
	return nonterminalIndex;
}

uint32_t CfgParserState::getPreviousProductionNonterminal() const {
	if (isInitial())
		throw logic_error("There is no previous element, this state is initial!");
	for (size_t i = _dotIndex - 1; i != size_t(-1); i--)
		if (FctHelper::vectorContains(_grammar.nonterminalIds(), _production[i]))
			return _production[i];
	throw logic_error("There is no nonterminal ahead of the dot.");
}

vector<uint32_t> CfgParserState::getProductionNonterminals() const {
	vector<uint32_t> prodNonterminals;
	for (size_t i = 0; i < _production.size(); i++)
		if (FctHelper::vectorContains(_grammar.nonterminalIds(), _production[i]))
			prodNonterminals.push_back(_production[i]);
	return prodNonterminals;
}

vector<uint32_t> CfgParserState::getTerminalProductionBetweenNonterminalsAt(size_t gapIndex) const {
	if (gapIndex > getProductionNonterminalNumber())
		throw invalid_argument(string("The gap index is invalid, there are only ") + to_string(getProductionNonterminalNumber()) + string(" many gaps between nonterminals."));
	vector<uint32_t> terminalProductionSlice;
	size_t nextNonterminalIndex = 0;
	for (size_t i = 0; i < _production.size(); i++)
		if (FctHelper::vectorContains(_grammar.nonterminalIds(), _production[i])) {
			if (nextNonterminalIndex > gapIndex)
				break;
			nextNonterminalIndex++;
		} else if (nextNonterminalIndex == gapIndex)
			terminalProductionSlice.push_back(_production[i]);
	return terminalProductionSlice;
}

bool CfgParserState::hasTerminalProduction() const {
	for (size_t i = 0; i < _production.size(); i++)
		if (FctHelper::vectorContains(_grammar.nonterminalIds(), _production[i]))
			return false;
	return true;
}

size_t CfgParserState::getProductionNonterminalNumber() const {
	size_t nonterminalCount = 0;
	for (size_t i = 0; i < _production.size(); i++)
		if (FctHelper::vectorContains(_grammar.nonterminalIds(), _production[i]))
			nonterminalCount++;
	return nonterminalCount;
}

void CfgParserState::decreaseDotIndex() {
	_dotIndex--;
}

uint64_t CfgParserState::getStateNumber() const {
	return _stateNumber;
}

size_t CfgParserState::getOriginChartIndex() const {
	return _originChartIndex;
}

size_t CfgParserState::getIndexInChart() const {
	return _indexInChart;
}

size_t CfgParserState::getDotIndex() const {
	return _dotIndex;
}

size_t CfgParserState::getFinalChartIndex() const {
	return _finalChartIndex;
}

uint32_t CfgParserState::getNonterminal() const {
	return _nonterminal;
}

const vector<uint32_t>& CfgParserState::getRule() const {
	return _rule;
}

const vector<uint32_t>& CfgParserState::getProduction() const {
	return _production;
}

const vector<uint64_t>& CfgParserState::getPointerPreviousRule() const {
	return _pointerPreviousRule;
}

CfgParserStateProducer CfgParserState::getProducer() const {
	return _producer;
}

string CfgParserState::getInnerString() const {
	if (_rule.empty())
		return string("(, ") + to_string(_originChartIndex) + string(")");
	else {
		string strRet = string("(") + _grammar.stringOf(_rule[0]) + string(" ->");
		for (size_t i = 1; i < _rule.size(); i++) {
			strRet += string(" ");
			if (i == _dotIndex + 1)
				strRet += string("•");
			strRet += _grammar.stringOf(_rule[i]);
		}
		if (_rule.size() == _dotIndex + 1)
			strRet += string("•");
		strRet += string(", ") + to_string(_originChartIndex) + string(")");
		return strRet;
	}
}

string CfgParserState::toString() const {
	return to_string(_stateNumber) + string(":") + getInnerString() + string(" ∈ Q") + to_string(_finalChartIndex);
}

string CfgParserState::getInnerString(const CfgGrammar& grammar) const {
	if (_rule.empty())
		return string("(, ") + to_string(_originChartIndex) + string(")");
	else {
		string strRet = string("(") + grammar.stringOf(_rule[0]) + string(" ->");
		for (size_t i = 1; i < _rule.size(); i++) {
			strRet += string(" ");
			if (i == _dotIndex + 1)
				strRet += string("•");
			strRet += grammar.stringOf(_rule[i]);
		}
		if (_rule.size() == _dotIndex + 1)
			strRet += string("•");
		strRet += string(", ") + to_string(_originChartIndex) + string(")");
		return strRet;
	}
}

string CfgParserState::toString(const CfgGrammar& grammar) const {
	return to_string(_stateNumber) + string(":") + getInnerString(grammar) + string(" ∈ Q") + to_string(_finalChartIndex);
}

bool CfgParserState::equals(const CfgParserState& obj) const {
	if (this == &obj)
		return true;
	return _rule == obj._rule && _originChartIndex == obj._originChartIndex && _dotIndex == obj._dotIndex;
}

bool CfgParserState::equals(uint32_t nonterminal, const vector<uint32_t>& production, size_t originChartIndex, size_t dotIndex) const {
	return _nonterminal == nonterminal && _production == production && _originChartIndex == originChartIndex && _dotIndex == dotIndex;
}

CfgParserChart::CfgParserChart(CfgParser& owner) :
		_owner(owner) {
}

void CfgParserChart::addState(const shared_ptr<CfgParserState>& state) {
	_table.push_back(state);
}

bool CfgParserChart::emplaceStateIfNew(CfgParser& owner, size_t originChartIndex, size_t indexInChart, size_t dotIndex, size_t finalChartIndex, uint32_t nonterminal, const vector<uint32_t>& production, const CfgParserStateProducer& producer) {
	bool notAlreadyContained = true;
	for (size_t i = 0; i < _table.size(); i++)
		if (_table[i]->equals(nonterminal, production, originChartIndex, dotIndex)) {
			notAlreadyContained = false;
			break;
		}
	if (notAlreadyContained) {
		const shared_ptr<CfgParserState> newState = make_shared<CfgParserState>(owner, originChartIndex, indexInChart, dotIndex, finalChartIndex, nonterminal, production, producer);
		_table.push_back(newState);
	}
	return notAlreadyContained;
}

bool CfgParserChart::emplaceStateIfNew(CfgParser& owner, size_t originChartIndex, size_t indexInChart, size_t dotIndex, size_t finalChartIndex, uint32_t nonterminal, const vector<uint32_t>& production, const vector<uint64_t>& pointerPreviousRule, const CfgParserStateProducer& producer) {
	bool notAlreadyContained = true;
	for (size_t i = 0; i < _table.size(); i++)
		if (_table[i]->equals(nonterminal, production, originChartIndex, dotIndex)) {
			notAlreadyContained = false;
			break;
		}
	if (notAlreadyContained) {
		const shared_ptr<CfgParserState> newState = make_shared<CfgParserState>(owner, originChartIndex, indexInChart, dotIndex, finalChartIndex, nonterminal, production, pointerPreviousRule, producer);
		_table.push_back(newState);
	}
	return notAlreadyContained;
}

const shared_ptr<CfgParserState>& CfgParserChart::getState(size_t index) const {
	return _table[index];
}

const vector<shared_ptr<CfgParserState>>& CfgParserChart::getTable() const {
	return _table;
}

size_t CfgParserChart::size() const {
	return _table.size();
}

string CfgParserChart::toString() const {
	stringstream ss;
	ss << "[";
	for (size_t i = 0; i < _table.size(); ++i) {
		if (i)
			ss << ", ";
		ss << _table[i]->toString();
	}
	ss << "]";
	return ss.str();
}

}
}
