#ifndef XAMIDI_GRAMMAR_CFGGRAMMAR_H
#define XAMIDI_GRAMMAR_CFGGRAMMAR_H

#include "../helper/IPrintable.h"

#include <cstdint>
#include <unordered_map>
#include <vector>

namespace xamidi {
namespace grammar {

// Represents a context-free grammar
struct CfgGrammar: public helper::IPrintable {
private:
	std::uint32_t _elementCounter;
	std::string _startSymbolString;
	std::string _grammarString;
	std::uint32_t _startSymbolId;
	std::unordered_map<std::uint32_t, const std::string> _nonterminalStringLookup;
	std::vector<std::string> _nonterminalStrings;
	std::vector<std::uint32_t> _nonterminalIds;
	std::unordered_map<std::uint32_t, const std::string> _terminalStringLookup;
	std::vector<std::string> _terminalStrings;
	std::vector<std::uint32_t> _terminalIds;
	std::unordered_map<std::string, std::uint32_t> _idLookup;
	std::unordered_map<std::uint32_t, std::vector<std::vector<std::uint32_t>>> _productionRules;

public:
	CfgGrammar(const std::string& startSymbolString, const std::string& grammarString);

	const std::string& startSymbolString() const;

	std::uint32_t startSymbolId() const;

	const std::string& grammarString() const;

	const std::vector<std::uint32_t>& nonterminalIds() const;

	const std::vector<std::uint32_t>& terminalIds() const;

	const std::vector<std::string>& nonterminalStrings() const;

	const std::vector<std::string>& terminalStrings() const;

	const std::unordered_map<std::uint32_t, const std::string>& nonterminalStringLookup() const;

	const std::unordered_map<std::uint32_t, const std::string>& terminalStringLookup() const;

	const std::string& stringOf(std::uint32_t id) const;

	std::vector<std::string> stringsOf(const std::vector<std::uint32_t>& ids) const;

	std::string symbolSequenceOf(const std::vector<std::uint32_t>& ids) const;

	const std::unordered_map<std::uint32_t, std::vector<std::vector<std::uint32_t>>>& productionRules() const;

	std::uint32_t maybeStoreNonterminal(const std::string&);

	std::uint32_t maybeStoreTerminal(const std::string&);

	std::uint32_t idLookup(const std::string&) const;

	std::string productionString() const;

	virtual std::string toString() const override;
};

}
}

#endif // XAMIDI_GRAMMAR_CFGGRAMMAR_H
