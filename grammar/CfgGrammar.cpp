#include "CfgGrammar.h"

#include "../helper/FctHelper.h"

#include <boost/algorithm/string.hpp>

using namespace std;
using namespace xamidi::helper;

namespace xamidi {
namespace grammar {

CfgGrammar::CfgGrammar(const string& startSymbolString, const string& grammarString) :
		_elementCounter(0), _startSymbolString(startSymbolString), _grammarString(grammarString) {
	// 1. Replace "\r\n" with "\n" in the grammar string
	boost::replace_all(_grammarString, "\r\n", "\n");

	// 2. Build up nonterminals and production rules
	istringstream reader1(_grammarString);
	istringstream reader2(_grammarString);
	string grammarLine;
	unordered_map<string, vector<string>> productionRules;
	vector<string> nonterminals;
	while (getline(reader1, grammarLine)) {
		const vector<string>& ruleElements = FctHelper::stringSplit(grammarLine, " ");
		if (!FctHelper::vectorContains(nonterminals, ruleElements[0]))
			nonterminals.push_back(ruleElements[0]);
		const vector<string>& splitGrammarLine = FctHelper::stringSplit(grammarLine, " ::= ");

		vector<string> grammarRule;
		if (splitGrammarLine[1].find('|') != string::npos) { // multiple rules
			vector<string> rightHandSideElements = FctHelper::stringSplit(splitGrammarLine[1], " | ");
			for (size_t i = 0; i < rightHandSideElements.size(); i++)
				grammarRule.push_back(rightHandSideElements[i]);
			productionRules[splitGrammarLine[0]] = grammarRule;
		} else { // single rule
			grammarRule.push_back(splitGrammarLine[1]);
			productionRules[splitGrammarLine[0]] = grammarRule;
		}
	}

	// 3. Fill nonterminal pointers
	_startSymbolId = _elementCounter++;
	_nonterminalStringLookup.insert(make_pair(_startSymbolId, _startSymbolString));
	_nonterminalStrings.push_back(_startSymbolString);
	_nonterminalIds.push_back(_startSymbolId);
	_idLookup.insert(make_pair(_startSymbolString, _startSymbolId));
	for (size_t i = 0; i < nonterminals.size(); i++)
		if (nonterminals[i] != _startSymbolString) {
			uint32_t id = _elementCounter++;
			_nonterminalStringLookup.insert(make_pair(id, nonterminals[i]));
			_nonterminalStrings.push_back(nonterminals[i]);
			_nonterminalIds.push_back(id);
			_idLookup.insert(make_pair(nonterminals[i], id));
		}

	// 4. Build up terminals
	vector<string> terminals;
	while (getline(reader2, grammarLine)) {
		const vector<string>& ruleElements = FctHelper::stringSplit(grammarLine, " ");
		for (size_t i = 1; i < ruleElements.size(); i++)
			if (!FctHelper::vectorContains(nonterminals, ruleElements[i]) && !FctHelper::vectorContains(terminals, ruleElements[i]) && (ruleElements[i] != "::=") && (ruleElements[i] != "|"))
				terminals.push_back(ruleElements[i]);
	}

	// 5. Fill terminal pointers
	for (size_t i = 0; i < terminals.size(); i++) {
		uint32_t id = _elementCounter++;
		_terminalStringLookup.insert(make_pair(id, terminals[i]));
		_terminalStrings.push_back(terminals[i]);
		_terminalIds.push_back(id);
		_idLookup.insert(make_pair(terminals[i], id));
	}

	// 6. Fill production rule pointers
	unordered_map<string, vector<string>>::const_iterator it = productionRules.begin();
	while (it != productionRules.end()) {
		vector<vector<uint32_t>> grammarRule;
		for (size_t i = 0; i < it->second.size(); i++) {
			vector<string> ruleStrElements = FctHelper::stringSplit(it->second[i], " ");
			vector<uint32_t> ruleElements;
			for (size_t j = 0; j < ruleStrElements.size(); j++)
				ruleElements.push_back(_idLookup[ruleStrElements[j]]);
			grammarRule.push_back(ruleElements);
		}
		_productionRules.insert(make_pair(_idLookup[it->first], grammarRule));
		++it;
	}
}

const string& CfgGrammar::startSymbolString() const {
	return _startSymbolString;
}

uint32_t CfgGrammar::startSymbolId() const {
	return _startSymbolId;
}

const string& CfgGrammar::grammarString() const {
	return _grammarString;
}

const vector<uint32_t>& CfgGrammar::nonterminalIds() const {
	return _nonterminalIds;
}

const vector<uint32_t>& CfgGrammar::terminalIds() const {
	return _terminalIds;
}

const vector<string>& CfgGrammar::nonterminalStrings() const {
	return _nonterminalStrings;
}

const vector<string>& CfgGrammar::terminalStrings() const {
	return _terminalStrings;
}

const unordered_map<uint32_t, const string>& CfgGrammar::nonterminalStringLookup() const {
	return _nonterminalStringLookup;
}

const unordered_map<uint32_t, const string>& CfgGrammar::terminalStringLookup() const {
	return _terminalStringLookup;
}

const string& CfgGrammar::stringOf(uint32_t id) const {
	unordered_map<uint32_t, const string>::const_iterator search = _nonterminalStringLookup.find(id);
	if (search == _nonterminalStringLookup.end())
		search = _terminalStringLookup.find(id);
	return search->second;
}

vector<string> CfgGrammar::stringsOf(const vector<uint32_t>& ids) const {
	vector<string> strings;
	for (uint32_t id : ids)
		strings.push_back(stringOf(id));
	return strings;
}

string CfgGrammar::symbolSequenceOf(const vector<uint32_t>& ids) const {
	return FctHelper::stringJoin(stringsOf(ids));
}

const unordered_map<uint32_t, vector<vector<uint32_t>>>& CfgGrammar::productionRules() const {
	return _productionRules;
}

const vector<vector<uint32_t>>& CfgGrammar::productionRuleOf(uint32_t nonterminalId) const {
	return _productionRules.at(nonterminalId);
}

uint32_t CfgGrammar::maybeStoreNonterminal(const string& nonterminalString) {
	unordered_map<string, uint32_t>::const_iterator search = _idLookup.find(nonterminalString);
	if (search == _idLookup.end()) { // if the string is not yet part of the grammar
		uint32_t id = _elementCounter++;
		_nonterminalStringLookup.insert(make_pair(id, nonterminalString));
		_nonterminalStrings.push_back(nonterminalString);
		_nonterminalIds.push_back(id);
		_idLookup.insert(make_pair(nonterminalString, id));
		search = _idLookup.find(nonterminalString);
	}
	return search->second;
}

uint32_t CfgGrammar::maybeStoreTerminal(const string& terminalString) {
	unordered_map<string, uint32_t>::const_iterator search = _idLookup.find(terminalString);
	if (search == _idLookup.end()) { // if the string is not yet part of the grammar
		uint32_t id = _elementCounter++;
		_terminalStringLookup.insert(make_pair(id, terminalString));
		_terminalStrings.push_back(terminalString);
		_terminalIds.push_back(id);
		_idLookup.insert(make_pair(terminalString, id));
		search = _idLookup.find(terminalString);
	}
	return search->second;
}

uint32_t CfgGrammar::idLookup(const string& s) const {
	return _idLookup.at(s);
}

string CfgGrammar::productionString() const {
	stringstream ss;
	ss << "{";
	for (unordered_map<uint32_t, vector<vector<uint32_t>>>::const_iterator it = _productionRules.begin(); it != _productionRules.end(); ++it) {
		if (it != _productionRules.begin())
			ss << ", ";
		ss << stringOf(it->first) << "=[";
		for (size_t i = 0; i < it->second.size(); ++i) {
			if (i)
				ss << ", ";
			ss << FctHelper::vectorString(stringsOf(it->second[i]));
		}
		ss << "]";
	}
	ss << "}";
	return ss.str();
}

string CfgGrammar::toString() const {
	stringstream ss;
	ss << string("(") << FctHelper::vectorString(_nonterminalStrings) << string(", ") << FctHelper::vectorString(_terminalStrings) << string(", ") << productionString() << string(", ") << _startSymbolString << string(")");
	return ss.str();
}

vector<uint32_t> CfgGrammar::firstFitLex(const string& s, bool utf8) {
	vector<uint32_t> refinedSymbolSequence;
	if (s.empty())
		return {};
	string::size_type sStartIndex = 0;
	for (string::size_type sEndIndex = 1; sEndIndex <= s.length(); sEndIndex++) {
		unordered_map<string, uint32_t>::const_iterator it = _idLookup.find(s.substr(sStartIndex, sEndIndex - sStartIndex));
		if (it != _idLookup.end()) { // match
			refinedSymbolSequence.push_back(it->second);
			sStartIndex = sEndIndex;
		}
		if (sEndIndex == s.length() && sStartIndex < sEndIndex) {
			string::size_type skips = 0;
			if (utf8) {
				auto utf8Skips = [](const string& s) -> string::size_type {
					string::const_iterator begin = s.begin(), end = s.end();
					string::size_type skips = 0;
					while (begin != end) {
						unsigned char c = *begin;
						string::size_type skip;
						if ((c & 0x80) == 0)
							skip = 0;
						else if ((c & 0xE0) == 0xC0)
							skip = 1;
						else if ((c & 0xF0) == 0xE0)
							skip = 2;
						else if ((c & 0xF8) == 0xF0)
							skip = 3;
						else
							throw invalid_argument("CfgGrammar::firstFitLex(): Invalid char for UTF-8.");
						string::size_type n = skip + 1;
						if (end < begin + n)
							throw invalid_argument("CfgGrammar::firstFitLex(): String too short for UTF-8.");
						for (unsigned i = 1; i < n; i++)
							if ((begin[i] & 0xC0) != 0x80)
								throw invalid_argument("CfgGrammar::firstFitLex(): Missing continuation byte for UTF-8.");
						begin += n;
						skips += skip;
					}
					return skips;
				};
				skips = utf8Skips(s.substr(0, sStartIndex));
			}
			stringstream ss_err;
			ss_err << "CfgGrammar::firstFitLex(): The expression could not be lexed successfully: Symbol at index " << sStartIndex << " not found.";
			ss_err << "\nExpression:  " << s << "\nUnlexed:     " << string(sStartIndex - skips, ' ') << s.substr(sStartIndex, sEndIndex - sStartIndex) << flush;
			throw domain_error(ss_err.str());
		}
	}
	return refinedSymbolSequence;
}

}
}
