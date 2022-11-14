#ifndef XAMID_GRAMMAR_CFGGRAMMAR_H
#define XAMID_GRAMMAR_CFGGRAMMAR_H

#include "../helper/IPrintable.h"

#include <unordered_map>
#include <vector>

namespace xamid {
namespace grammar {

// Represents a context-free grammar
struct CfgGrammar: public helper::IPrintable {
private:
	uint32_t _elementCounter;
	std::string _startSymbolString;
	std::string _grammarString;
	uint32_t _startSymbolId;
	std::unordered_map<uint32_t, const std::string> _nonterminalStringLookup;
	std::vector<std::string> _nonterminalStrings;
	std::vector<uint32_t> _nonterminalIds;
	std::unordered_map<uint32_t, const std::string> _terminalStringLookup;
	std::vector<std::string> _terminalStrings;
	std::vector<uint32_t> _terminalIds;
	std::unordered_map<std::string, uint32_t> _idLookup;
	std::unordered_map<uint32_t, std::vector<std::vector<uint32_t>>> _productionRules;

public:
	CfgGrammar(const std::string& startSymbolString, const std::string& grammarString);

	const std::string& startSymbolString() const;

	uint32_t startSymbolId() const;

	const std::string& grammarString() const;

	const std::vector<uint32_t>& nonterminalIds() const;

	const std::vector<uint32_t>& terminalIds() const;

	const std::vector<std::string>& nonterminalStrings() const;

	const std::vector<std::string>& terminalStrings() const;

	const std::unordered_map<uint32_t, const std::string>& nonterminalStringLookup() const;

	const std::unordered_map<uint32_t, const std::string>& terminalStringLookup() const;

	const std::string& stringOf(uint32_t id) const;

	std::vector<std::string> stringsOf(const std::vector<uint32_t>& ids) const;

	std::string symbolSequenceOf(const std::vector<uint32_t>& ids) const;

	const std::unordered_map<uint32_t, std::vector<std::vector<uint32_t>>>& productionRules() const;

	uint32_t maybeStoreNonterminal(const std::string&);

	uint32_t maybeStoreTerminal(const std::string&);

	uint32_t idLookup(const std::string&) const;

	std::string productionString() const;

	virtual std::string toString() const override;
};

}
}

#endif // XAMID_GRAMMAR_CFGGRAMMAR_H
