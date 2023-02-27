#ifndef XAMID_NORTMANN_DLSTRUCTURE_H
#define XAMID_NORTMANN_DLSTRUCTURE_H

#include <cstdint>

namespace xamid {
namespace tree { template<typename T> class TreeNode; }
namespace grammar { struct CfgGrammar; struct CfgParserState; }

namespace nortmann {

struct DlStructure {
	// ------------------------------------------------------------------------------------------------ //
	// Fields, using lazy initialization via singleton pattern (to prevent initialization order issues) //
	// ------------------------------------------------------------------------------------------------ //

	// Unambiguous context-free grammar for DL such that variables are natural numbers, with intended order of operations by Earley parse trees to omit parentheses, i.e.:
	//  S -> S \and ( S ) | S \and A | S \or ( S ) | S \or A | S \nand ( S ) | S \nand A | S \nor ( S ) | S \nor A | S \imply ( S ) | S \imply A | S \implied ( S ) | S \implied A | S \nimply ( S ) | S \nimply A | S \nimplied ( S ) | S \nimplied A | S \equiv ( S ) | S \equiv A | S \xor ( S ) | S \xor A | ( S ) | A
	//  A -> A \com ( S ) | A \com B | A \app ( S ) | A \app B | ( S ) | B
	//  B -> \not B | \nece B | \poss B | \obli B | \perm B | ( S ) | \top | \bot | X
	//  X -> 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | Y 0 | Y 1 | Y 2 | Y 3 | Y 4 | Y 5 | Y 6 | Y 7 | Y 8 | Y 9
	//  Y -> 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | Y 0 | Y 1 | Y 2 | Y 3 | Y 4 | Y 5 | Y 6 | Y 7 | Y 8 | Y 9
	static grammar::CfgGrammar& dlEvaluationGrammar();

	// Grammar constants (of dlEvaluationGrammar())
	static const std::uint32_t& nonterminal_at();
	static const std::uint32_t& nonterminal_S();
	static const std::uint32_t& nonterminal_A();
	static const std::uint32_t& nonterminal_B();
	static const std::uint32_t& nonterminal_X();
	static const std::uint32_t& nonterminal_Y();
	static const std::uint32_t& terminal_and();
	static const std::uint32_t& terminal_or();
	static const std::uint32_t& terminal_nand();
	static const std::uint32_t& terminal_nor();
	static const std::uint32_t& terminal_imply();
	static const std::uint32_t& terminal_implied();
	static const std::uint32_t& terminal_nimply();
	static const std::uint32_t& terminal_nimplied();
	static const std::uint32_t& terminal_equiv();
	static const std::uint32_t& terminal_xor();
	static const std::uint32_t& terminal_com();
	static const std::uint32_t& terminal_app();
	static const std::uint32_t& terminal_not();
	static const std::uint32_t& terminal_nece();
	static const std::uint32_t& terminal_poss();
	static const std::uint32_t& terminal_obli();
	static const std::uint32_t& terminal_perm();
	static const std::uint32_t& terminal_top();
	static const std::uint32_t& terminal_bot();
	static const std::uint32_t& terminal_0();
	static const std::uint32_t& terminal_1();
	static const std::uint32_t& terminal_2();
	static const std::uint32_t& terminal_3();
	static const std::uint32_t& terminal_4();
	static const std::uint32_t& terminal_5();
	static const std::uint32_t& terminal_6();
	static const std::uint32_t& terminal_7();
	static const std::uint32_t& terminal_8();
	static const std::uint32_t& terminal_9();
	static const std::uint32_t& terminal_leftParenthesis();
	static const std::uint32_t& terminal_rightParenthesis();
};

}
}

#endif // XAMID_NORTMANN_DLSTRUCTURE_H
