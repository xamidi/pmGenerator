#ifndef XAMIDI_ND_NDPARSER_H
#define XAMIDI_ND_NDPARSER_H

#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace xamidi {
namespace helper { struct String; }
namespace tree { template<typename T> class TreeNode; }
namespace grammar { class CfgGrammar; class CfgParserState; }
namespace logic { typedef tree::TreeNode<helper::String> DlFormula; }

namespace nd {

struct NdParser {
	static std::vector<std::string> readFromFile(const std::string& file, bool debug = false);

	//#######################################################
	//#    FitchFX (https://github.com/mrieppel/FitchFX)    #
	//#######################################################

	static grammar::CfgGrammar& ffxFormulaGrammar();
	enum class FFxProofReasonType {
		Assumption = 0, // "Assumption"
		IndirectProof = 1, // "IP  i-j"
		NegationIntroduction = 2, // "~I  i-j"
		NegationElimination = 3, // "~E  m,n"
		ConditionalIntroduction = 4, // ">I  i-j"
		ConditionalElimination = 5, // ">E  m,n"
		ConjunctionIntroduction = 6, // "&I  m,n"
		ConjunctionElimination = 7, // "&E  m"
		DisjunctionIntroduction = 8, // "vI  m"
		DisjunctionElimination = 9, // "vE  m,i-j,k-l"
		BiconditionalIntroduction = 10, // "<>I  i-j,k-l"
		BiconditionalElimination = 11, // "<>E  m,n"
		Reiteration = 12 // "Reit m"
	};
	struct FFxProofReason {
		FFxProofReasonType type;
		std::vector<std::size_t> metadata;
		FFxProofReason();
		FFxProofReason(const std::string& reason);
	};
	struct FFxProofLine {
		std::size_t lineNo;
		std::size_t depth;
		std::shared_ptr<logic::DlFormula> formula;
		FFxProofReason reason;
		FFxProofLine(std::size_t lineNo, const std::string& line);
	};
	struct FFxProof {
		std::string problem_str;
		std::vector<FFxProofLine> lines;
		std::map<std::size_t, std::array<std::size_t, 2>> blocks; // (from, (to, depth))
		std::map<std::size_t, std::size_t> blockStarts; // maps every line in a block to the assumption of its smallest containing block
		std::size_t size();
		const FFxProofLine& lineAt(std::size_t pos) const;
		const std::shared_ptr<logic::DlFormula>& formulaAt(std::size_t pos) const;
		const FFxProofReason& reasonAt(std::size_t pos) const;
		FFxProof(const std::vector<std::string>& lines);
	};

	// Lexer ; Input: string representing a FitchFX-formula, Output: integer sequence, called "meaning", representing a symbol sequence for ffxFormulaGrammar()
	static std::vector<std::uint32_t> ffxToSymbolSequence(const std::string& formulaString);

	// Parse to fresh DL-formulas based on FitchFX-meanings or FitchFX-strings.
	static std::shared_ptr<logic::DlFormula> ffxToDlFormula(const std::vector<std::uint32_t>& symbolSequence, bool printParseError = false); // based on meaning => no lexing required
	static std::shared_ptr<logic::DlFormula> ffxToDlFormula(const std::string& formulaString, bool printParseError = false); // based on string => lexing required

	static FFxProof parseFromFitchFxFile(const std::string& file, bool debug = false);
};

}
}

#endif // XAMIDI_ND_NDPARSER_H
