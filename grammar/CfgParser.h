#ifndef XAMIDI_GRAMMAR_CFGPARSER_H
#define XAMIDI_GRAMMAR_CFGPARSER_H

#include "../tree/TreeNode.h"

namespace xamidi {
namespace grammar {

class CfgGrammar;
struct CfgParser;

//#######################################################
//#                   Helper Classes                    #
//#######################################################

enum class CfgParserStateProducer {
	InitialState, Predictor, Scanner, Completer
};

class CfgParserState: public helper::IPrintable {
	CfgParser& _owner;
	const CfgGrammar& _grammar;
	std::uint64_t _stateNumber = 0;
	std::size_t _originChartIndex = 0;
	std::size_t _indexInChart = 0;
	std::size_t _dotIndex = 0;
	std::size_t _finalChartIndex = 0;
	std::uint32_t _nonterminal;
	std::vector<std::uint32_t> _rule;
	std::vector<std::uint32_t> _production;
	std::vector<std::uint64_t> _pointerPreviousRule;
	CfgParserStateProducer _producer;
public:
	CfgParserState(CfgParser&, std::size_t, std::size_t, std::size_t, std::size_t, std::uint32_t, const std::vector<std::uint32_t>&, const CfgParserStateProducer&);
	CfgParserState(CfgParser&, std::size_t, std::size_t, std::size_t, std::size_t, std::uint32_t, const std::vector<std::uint32_t>&, const std::vector<std::uint64_t>&, const CfgParserStateProducer&);
	bool isComplete() const;
	bool isInitial() const;
	std::uint32_t getCurrentElement() const;
	std::uint32_t getPreviousElement() const;
	std::uint32_t getProductionNonterminalByIndex(std::size_t) const;
	std::size_t getProductionNonterminalIndexByDotIndex(std::size_t) const;
	std::uint32_t getPreviousProductionNonterminal() const;
	std::vector<std::uint32_t> getProductionNonterminals() const;
	std::vector<std::uint32_t> getTerminalProductionBetweenNonterminalsAt(std::size_t) const;
	bool hasTerminalProduction() const;
	std::size_t getProductionNonterminalNumber() const;
	void decreaseDotIndex();
	std::uint64_t getStateNumber() const;
	std::size_t getOriginChartIndex() const;
	std::size_t getIndexInChart() const;
	std::size_t getDotIndex() const;
	std::size_t getFinalChartIndex() const;
	std::uint32_t getNonterminal() const;
	const std::vector<std::uint32_t>& getRule() const;
	const std::vector<std::uint32_t>& getProduction() const;
	const std::vector<std::uint64_t>& getPointerPreviousRule() const;
	CfgParserStateProducer getProducer() const;
	std::string getInnerString() const;
	std::string getInnerString(const CfgGrammar&) const;
	std::string toString(const CfgGrammar&) const;
	bool equals(const CfgParserState&) const;
	bool equals(std::uint32_t, const std::vector<std::uint32_t>&, std::size_t, std::size_t) const;

	// Overrides
	std::string toString() const override;

private:
	// Operators
	CfgParserState& operator=(const CfgParserState& other) { // NOTE: Since _owner and _grammar are const attributes, we need to override the assignment operator, which will be deleted otherwise.
		if (&_owner != &other._owner)
			throw std::invalid_argument("Trying to assign a state of another Earley parser.");
		_stateNumber = other._stateNumber;
		_originChartIndex = other._originChartIndex;
		_indexInChart = other._indexInChart;
		_dotIndex = other._dotIndex;
		_finalChartIndex = other._finalChartIndex;
		_nonterminal = other._nonterminal;
		_rule = other._rule;
		_production = other._production;
		_pointerPreviousRule = other._pointerPreviousRule;
		_producer = other._producer;
		return *this;
	}
public:
	friend bool operator==(const CfgParserState& lhs, const CfgParserState& rhs) {
		return lhs.equals(rhs);
	}
};

class CfgParserChart: public helper::IPrintable {
	CfgParser& _owner;
	std::vector<std::shared_ptr<CfgParserState>> _table;
public:
	explicit CfgParserChart(CfgParser&);
	void addState(const std::shared_ptr<CfgParserState>&);
	bool emplaceStateIfNew(CfgParser&, std::size_t, std::size_t, std::size_t, std::size_t, std::uint32_t, const std::vector<std::uint32_t>&, const CfgParserStateProducer&);
	bool emplaceStateIfNew(CfgParser&, std::size_t, std::size_t, std::size_t, std::size_t, std::uint32_t, const std::vector<std::uint32_t>&, const std::vector<std::uint64_t>&, const CfgParserStateProducer&);
	const std::shared_ptr<CfgParserState>& getState(std::size_t) const;
	const std::vector<std::shared_ptr<CfgParserState>>& getTable() const;
	std::size_t size() const;
	std::string toString() const override;
};

//#######################################################
//#                     Main Class                      #
//#######################################################

struct CfgParser {
	friend CfgParserState;

	//#######################################################
	//#                    Earley Parser                    #
	//#######################################################

private:
	const CfgGrammar& _grammar;
	std::uint64_t _stateNumberCounter = 0;
	std::vector<std::unique_ptr<CfgParserChart>> _chartSmartPtrs; // Earley charts are owned by CfgParser only.

public:
	// Construction
	explicit CfgParser(const CfgGrammar& grammar);

	// Runs the Earley algorithm for the given grammar on the given symbol sequence, and returns raw pointers to the resulting Earley charts, which are exclusively owned by the CfgParser instance. Nevertheless, states on the charts can be shared.
	std::vector<const CfgParserChart*> earleyParse(const std::vector<std::uint32_t>&);

private:
	void _predictor(std::uint32_t, std::uint64_t, const std::vector<CfgParserChart*>&);
	void _scanner(const std::shared_ptr<CfgParserState>&, std::uint64_t, const std::vector<std::uint32_t>&, const std::vector<CfgParserChart*>&);
	void _completer(const std::shared_ptr<CfgParserState>&, std::uint64_t, const std::vector<CfgParserChart*>&);

	//#######################################################
	//#                Parse Tree Generation                #
	//#######################################################

public:
	// Returns the final state of the given Earley charts
	const std::shared_ptr<CfgParserState>& getFinalState(const std::vector<const CfgParserChart*>&) const;

	// Generates the tree that is represented by the CfgParserState::_pointerPreviousRule connections in the given Earley charts
	std::shared_ptr<tree::TreeNode<CfgParserState>> generateEarleyParseTree(const std::shared_ptr<CfgParserState>&, const std::vector<const CfgParserChart*>&) const;

private:
	std::shared_ptr<tree::TreeNode<CfgParserState>> _generateEarleyParseTree(const std::shared_ptr<tree::TreeNode<CfgParserState>>&, const std::unordered_map<std::uint64_t, std::shared_ptr<CfgParserState>>&) const;

	//#######################################################
	//#           Abstract Syntax Tree Generation           #
	//#######################################################

public:
	// Generates the abstract syntax tree from the given parse tree, i.e. removes all nonterminal nodes, and labels remain nodes with terminals only.
	std::shared_ptr<tree::TreeNode<helper::String>> generateASTFromParseTree(const std::shared_ptr<tree::TreeNode<CfgParserState>>& parseTree, const std::vector<std::string>& terminalsToIgnore = { }) const;

private:
	void _generateASTFromParseTree(const std::shared_ptr<tree::TreeNode<helper::String>>& destinationNode, const std::shared_ptr<tree::TreeNode<CfgParserState>>& stateNode, const std::vector<std::string>& terminalsToIgnore) const;

	//#######################################################
	//#                    Earley Charts                    #
	//#######################################################

public:
	std::string writeCharts(const std::string&, const std::vector<const CfgParserChart*>&, const std::vector<std::uint32_t>&) const;
};

}
}

#endif // XAMIDI_GRAMMAR_CFGPARSER_H
