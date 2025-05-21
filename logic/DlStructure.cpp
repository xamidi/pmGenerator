#include "DlStructure.h"

#include "../grammar/CfgGrammar.h"

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::grammar;
using namespace xamidi::tree;

namespace xamidi {
namespace logic {

CfgGrammar& DlStructure::dlEvaluationGrammar() {
	// Unambiguous context-free grammar for DL such that variables are natural numbers.
	static CfgGrammar g("S",
			"S ::= S \\and ( S ) | S \\and A | S \\or ( S ) | S \\or A | S \\nand ( S ) | S \\nand A | S \\nor ( S ) | S \\nor A | S \\imply ( S ) | S \\imply A | S \\implied ( S ) | S \\implied A | S \\nimply ( S ) | S \\nimply A | S \\nimplied ( S ) | S \\nimplied A | S \\equiv ( S ) | S \\equiv A | S \\xor ( S ) | S \\xor A | ( S ) | A\n"
			"A ::= A \\com ( S ) | A \\com B | A \\app ( S ) | A \\app B | ( S ) | B\n"
			"B ::= \\not B | \\nece B | \\poss B | \\obli B | \\perm B | ( S ) | \\top | \\bot | X\n"
			"X ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | Y 0 | Y 1 | Y 2 | Y 3 | Y 4 | Y 5 | Y 6 | Y 7 | Y 8 | Y 9\n"
			"Y ::= 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | Y 0 | Y 1 | Y 2 | Y 3 | Y 4 | Y 5 | Y 6 | Y 7 | Y 8 | Y 9");
	return g;
}
const uint32_t& DlStructure::nonterminal_at() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreNonterminal("@");
	return x;
}
const uint32_t& DlStructure::nonterminal_S() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreNonterminal("S");
	return x;
}
const uint32_t& DlStructure::nonterminal_A() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreNonterminal("A");
	return x;
}
const uint32_t& DlStructure::nonterminal_B() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreNonterminal("B");
	return x;
}
const uint32_t& DlStructure::nonterminal_X() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreNonterminal("X");
	return x;
}
const uint32_t& DlStructure::nonterminal_Y() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreNonterminal("Y");
	return x;
}
const uint32_t& DlStructure::terminal_and() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\and");
	return x;
}
const uint32_t& DlStructure::terminal_or() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\or");
	return x;
}
const uint32_t& DlStructure::terminal_nand() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\nand");
	return x;
}
const uint32_t& DlStructure::terminal_nor() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\nor");
	return x;
}
const uint32_t& DlStructure::terminal_imply() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\imply");
	return x;
}
const uint32_t& DlStructure::terminal_implied() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\implied");
	return x;
}
const uint32_t& DlStructure::terminal_nimply() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\nimply");
	return x;
}
const uint32_t& DlStructure::terminal_nimplied() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\nimplied");
	return x;
}
const uint32_t& DlStructure::terminal_equiv() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\equiv");
	return x;
}
const uint32_t& DlStructure::terminal_xor() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\xor");
	return x;
}
const uint32_t& DlStructure::terminal_com() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\com");
	return x;
}
const uint32_t& DlStructure::terminal_app() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\app");
	return x;
}
const uint32_t& DlStructure::terminal_not() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\not");
	return x;
}
const uint32_t& DlStructure::terminal_nece() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\nece");
	return x;
}
const uint32_t& DlStructure::terminal_poss() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\poss");
	return x;
}
const uint32_t& DlStructure::terminal_obli() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\obli");
	return x;
}
const uint32_t& DlStructure::terminal_perm() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\perm");
	return x;
}
const uint32_t& DlStructure::terminal_top() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\top");
	return x;
}
const uint32_t& DlStructure::terminal_bot() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("\\bot");
	return x;
}
const uint32_t& DlStructure::terminal_0() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("0");
	return x;
}
const uint32_t& DlStructure::terminal_1() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("1");
	return x;
}
const uint32_t& DlStructure::terminal_2() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("2");
	return x;
}
const uint32_t& DlStructure::terminal_3() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("3");
	return x;
}
const uint32_t& DlStructure::terminal_4() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("4");
	return x;
}
const uint32_t& DlStructure::terminal_5() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("5");
	return x;
}
const uint32_t& DlStructure::terminal_6() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("6");
	return x;
}
const uint32_t& DlStructure::terminal_7() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("7");
	return x;
}
const uint32_t& DlStructure::terminal_8() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("8");
	return x;
}
const uint32_t& DlStructure::terminal_9() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("9");
	return x;
}
const uint32_t& DlStructure::terminal_leftParenthesis() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal("(");
	return x;
}
const uint32_t& DlStructure::terminal_rightParenthesis() {
	static uint32_t x = dlEvaluationGrammar().maybeStoreTerminal(")");
	return x;
}

}
}
