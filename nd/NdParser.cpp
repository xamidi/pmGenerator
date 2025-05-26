#include "NdParser.h"

#include "../helper/FctHelper.h"
#include "../grammar/CfgGrammar.h"
#include "../grammar/CfgParser.h"
#include "../logic/DlCore.h"

#include <boost/algorithm/string.hpp>

#include <iostream>

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::tree;
using namespace xamidi::grammar;
using namespace xamidi::logic;

namespace xamidi {
namespace nd {

vector<string> NdParser::readFromFile(const string& file, bool debug) {
	vector<string> lines;
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	string s;
	if (!FctHelper::readFile(file, s))
		throw invalid_argument("NdParser(): Could not read file \"" + file + "\".");
	lines = FctHelper::stringSplitAndSkip(s, "\n", "%", true);
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to read " << lines.size() << " natural deduction proof line" << (lines.size() == 1 ? "" : "s") << " from file \"" << file << "\"." << endl;
	//#cout << "lines (size " << lines.size() << ") = " << FctHelper::vectorString(lines, { }, { }, "\n") << endl;
	return lines;
}

//#######################################################
//#    FitchFX (https://github.com/mrieppel/FitchFX)    #
//#######################################################

CfgGrammar& NdParser::ffxFormulaGrammar() {
	static CfgGrammar g("_", "_ ::= ~ _ | ( _ & _ ) | ( _ /\\ _ ) | ( _ ^ _ ) | ( _ v _ ) | ( _ \\/ _ ) | ( _ > _ ) | ( _ -> _ ) | ( _ <> _ ) | ( _ <-> _ ) | # | A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z\n");
	return g;
}

NdParser::FFxProofReason::FFxProofReason() { type = FFxProofReasonType::Assumption; }

NdParser::FFxProofReason::FFxProofReason(const string& reason) {
	string::size_type pos = reason.find("  ");
	if (pos == string::npos) {
		if (reason != "Assumption")
			throw invalid_argument("NdParser(): Invalid FitchFX reason \"" + reason + "\".");
		type = FFxProofReasonType::Assumption;
	} else {
		string type_str = reason.substr(0, pos);
		if (type_str == "IP")
			type = FFxProofReasonType::IndirectProof;
		else if (type_str == "~I")
			type = FFxProofReasonType::NegationIntroduction;
		else if (type_str == "~E")
			type = FFxProofReasonType::NegationElimination;
		else if (type_str == ">I")
			type = FFxProofReasonType::ConditionalIntroduction;
		else if (type_str == ">E")
			type = FFxProofReasonType::ConditionalElimination;
		else if (type_str == "&I")
			type = FFxProofReasonType::ConjunctionIntroduction;
		else if (type_str == "&E")
			type = FFxProofReasonType::ConjunctionElimination;
		else if (type_str == "vI")
			type = FFxProofReasonType::DisjunctionIntroduction;
		else if (type_str == "vE")
			type = FFxProofReasonType::DisjunctionElimination;
		else if (type_str == "<>I")
			type = FFxProofReasonType::BiconditionalIntroduction;
		else if (type_str == "<>E")
			type = FFxProofReasonType::BiconditionalElimination;
		else if (type_str == "Reit")
			type = FFxProofReasonType::Reiteration;
		else
			throw invalid_argument("NdParser(): Invalid FitchFX reason \"" + reason + "\".");
		pos = reason.find_first_not_of(' ', pos + 2);
		string param_list = reason.substr(pos);
		pos = param_list.find("  ");
		if (pos != string::npos)
			throw invalid_argument("NdParser(): Invalid FitchFX reason \"" + reason + "\".");
		boost::replace_all(param_list, " ", "");
		bool ok = true;
		switch (type) {
		case FFxProofReasonType::ConjunctionElimination:
		case FFxProofReasonType::DisjunctionIntroduction:
		case FFxProofReasonType::Reiteration: // m
			metadata.resize(1);
			if (FctHelper::toUInt(param_list, metadata[0]).ec != errc())
				ok = false;
			break;
		case FFxProofReasonType::NegationElimination:
		case FFxProofReasonType::ConditionalElimination:
		case FFxProofReasonType::ConjunctionIntroduction:
		case FFxProofReasonType::BiconditionalElimination: // m,n
			pos = param_list.find(',');
			if (pos == string::npos) {
				ok = false;
				break;
			}
			metadata.resize(2);
			if (FctHelper::toUInt(param_list.substr(0, pos), metadata[0]).ec != errc() || FctHelper::toUInt(param_list.substr(pos + 1), metadata[1]).ec != errc())
				ok = false;
			break;
		case FFxProofReasonType::IndirectProof:
		case FFxProofReasonType::NegationIntroduction:
		case FFxProofReasonType::ConditionalIntroduction: // i-j
			pos = param_list.find('-');
			if (pos == string::npos) {
				ok = false;
				break;
			}
			metadata.resize(2);
			if (FctHelper::toUInt(param_list.substr(0, pos), metadata[0]).ec != errc() || FctHelper::toUInt(param_list.substr(pos + 1), metadata[1]).ec != errc())
				ok = false;
			break;
		case FFxProofReasonType::BiconditionalIntroduction: { // i-j,k-l
			pos = param_list.find('-');
			string::size_type pos2 = pos != string::npos ? param_list.find(',', pos + 1) : string::npos;
			string::size_type pos3 = pos2 != string::npos ? param_list.find('-', pos2 + 1) : string::npos;
			if (pos == string::npos || pos2 == string::npos || pos3 == string::npos) {
				ok = false;
				break;
			}
			metadata.resize(4);
			if (FctHelper::toUInt(param_list.substr(0, pos), metadata[0]).ec != errc() || FctHelper::toUInt(param_list.substr(pos + 1, pos2 - pos - 1), metadata[1]).ec != errc() || FctHelper::toUInt(param_list.substr(pos2 + 1, pos3 - pos2 - 1), metadata[2]).ec != errc() || FctHelper::toUInt(param_list.substr(pos3 + 1), metadata[3]).ec != errc())
				ok = false;
			break;
		}
		case FFxProofReasonType::DisjunctionElimination: { // m,i-j,k-l
			pos = param_list.find(',');
			string::size_type pos2 = pos != string::npos ? param_list.find('-', pos + 1) : string::npos;
			string::size_type pos3 = pos2 != string::npos ? param_list.find(',', pos2 + 1) : string::npos;
			string::size_type pos4 = pos3 != string::npos ? param_list.find('-', pos3 + 1) : string::npos;
			if (pos == string::npos) {
				ok = false;
				break;
			}
			metadata.resize(5);
			if (FctHelper::toUInt(param_list.substr(0, pos), metadata[0]).ec != errc() || FctHelper::toUInt(param_list.substr(pos + 1, pos2 - pos - 1), metadata[1]).ec != errc() || FctHelper::toUInt(param_list.substr(pos2 + 1, pos3 - pos2 - 1), metadata[2]).ec != errc() || FctHelper::toUInt(param_list.substr(pos3 + 1, pos4 - pos3 - 1), metadata[3]).ec != errc() || FctHelper::toUInt(param_list.substr(pos4 + 1), metadata[4]).ec != errc())
				ok = false;
			break;
		}
		default:
			throw logic_error("FFxProofReason(): type == " + to_string(static_cast<unsigned>(type)));
			break;
		}
		if (!ok)
			throw invalid_argument("NdParser(): Invalid FitchFX reason \"" + reason + "\".");
	}
}

NdParser::FFxProofLine::FFxProofLine(size_t lineNo, const string& line) {
	// 1. Parse basic structure.
	if (!line.starts_with(to_string(lineNo) + "  "))
		throw invalid_argument("NdParser(): Correct line specification (\"" + to_string(lineNo) + "  \") missing from FitchFX proof at entry number " + to_string(lineNo) + " in \"" + line + "\".");
	this->lineNo = lineNo;
	string::size_type pos = line.find_first_not_of(' ', FctHelper::digitsNum_uint64(lineNo) + 2);
	if (pos == string::npos)
		throw invalid_argument("NdParser(): Line specification in FitchFX proof at entry number " + to_string(lineNo) + " is empty in \"" + line + "\".");
	string::size_type pos2 = line.find_last_not_of(' ');
	string line_str = line.substr(pos, pos2 - pos + 1);
	pos = line_str.find("  ");
	bool endsPremiseOrAssumption = false;
	bool ok = false;
	if (pos != string::npos) {
		pos2 = line_str.rfind('|', pos);
		if (pos2 != string::npos) {
			if (line_str[pos2 + 1] == '_') {
				endsPremiseOrAssumption = true;
				pos2++;
			}
			if (pos2 + 1 == pos)
				ok = true;
		}
	}
	if (!ok)
		throw invalid_argument("NdParser(): FitchFX proof at line number " + to_string(lineNo) + " is missing separator (\"  \") before formula in \"" + line_str + "\".");
	string depth_str = line_str.substr(0, pos2 + 1);
	pos = line_str.find_first_not_of(' ', pos + 2);
	if (pos == string::npos)
		throw invalid_argument("NdParser(): Formula specification in FitchFX proof at line number " + to_string(lineNo) + " is empty in \"" + line + "\".");
	size_t depth = 0;
	ok = false;
	line_str = line_str.substr(pos);
	if (depth_str.starts_with('|')) {
		ok = true;
		for (size_t j = 1; ok && j < depth_str.size(); j++)
			switch (depth_str[j]) {
			case ' ':
				break;
			case '|':
				depth++;
				break;
			case '_':
				if (j != depth_str.size() - 1)
					ok = false;
				break;
			default:
				ok = false;
			}
	}
	if (!ok)
		throw invalid_argument("NdParser(): Formula specification in FitchFX proof at line number " + to_string(lineNo) + " has invalid depth string \"" + depth_str + "\".");
	if (!depth && endsPremiseOrAssumption)
		throw invalid_argument("NdParser(): Formula specification in FitchFX proof at line number " + to_string(lineNo) + " has invalid depth 0 for \"" + line_str + "\".");
	this->depth = depth;
	pos = line_str.find("  ");
	if (pos == string::npos)
		throw invalid_argument("NdParser(): FitchFX proof at line number " + to_string(lineNo) + " is missing separator (\"  \") after formula in \"" + line_str + "\".");
	string formula_str = line_str.substr(0, pos);
	pos = line_str.find_first_not_of(' ', pos + 2);
	string reason_str = line_str.substr(pos);
	if (reason_str == "Premise")
		throw invalid_argument("NdParser(): Formula specification in FitchFX proof at line number " + to_string(lineNo) + " has unsupported reason \"Premise\".");
	if (endsPremiseOrAssumption != (reason_str == "Assumption"))
		throw invalid_argument("NdParser(): Formula specification in FitchFX proof at line number " + to_string(lineNo) + " has unmatching reason \"" + reason_str + "\" for depth string \"" + depth_str + "\".");
	//#cout << "lineNo = " << this->lineNo << ", depth = " << this->depth << ", formula_str = \"" << formula_str << "\", reason_str = \"" << reason_str << "\"" << endl;

	// 2. Parse formula.
	boost::replace_all(formula_str, " ", "");
	formula = NdParser::ffxToDlFormula(formula_str, true);
	if (!formula)
		throw invalid_argument("NdParser(): Formula \"" + formula_str + "\" in FitchFX proof at line number " + to_string(lineNo) + " failed to parse.");
	//#cout << DlCore::formulaRepresentation_traverse(formula) << endl;
	//#const map<string, string> customVariableTranslation = { { "P", "p" }, { "Q", "q" }, { "R", "r" }, { "S", "s" }, { "T", "t" }, { "U", "u" }, { "V", "v" }, { "W", "w" }, { "X", "x" }, { "Y", "y" }, { "Z", "z" }, { "A", "a" }, { "B", "b" }, { "C", "c" }, { "D", "d" }, { "E", "e" }, { "F", "f" }, { "G", "g" }, { "H", "h" }, { "I", "i" }, { "J", "j" }, { "K", "k" }, { "L", "l" }, { "M", "m" }, { "N", "n" }, { "O", "o" } };
	//#cout << DlCore::toPolishNotation(formula, false, nullptr, &customVariableTranslation, { }) << endl;

	// 3. Parse reason.
	reason = FFxProofReason(reason_str);
	//#cout << "reason_str = " << "\"" << reason_str << "\", reason.metadata = " << FctHelper::vectorString(reason.metadata) << endl;
}

size_t NdParser::FFxProof::FFxProof::size() {
	return lines.size();
}

const NdParser::FFxProofLine& NdParser::FFxProof::lineAt(size_t pos) const {
	if (pos == 0 || pos > lines.size())
		throw invalid_argument("NdParser(): Position " + to_string(pos) + " is invalid.");
	return lines[pos - 1];
}

const shared_ptr<DlFormula>& NdParser::FFxProof::formulaAt(size_t pos) const {
	if (pos == 0 || pos > lines.size())
		throw invalid_argument("NdParser(): Position " + to_string(pos) + " is invalid.");
	return lines[pos - 1].formula;
}

const NdParser::FFxProofReason& NdParser::FFxProof::reasonAt(size_t pos) const {
	if (pos == 0 || pos > lines.size())
		throw invalid_argument("NdParser(): Position " + to_string(pos) + " is invalid.");
	return lines[pos - 1].reason;
}

NdParser::FFxProof::FFxProof(const vector<string>& lines) {
	// 1. Parse proof lines.
	if (lines.empty())
		throw invalid_argument("NdParser(): FitchFX proof is empty.");
	if (!lines[0].starts_with("Problem:"))
		throw invalid_argument("NdParser(): Problem specification missing from FitchFX proof.");
	string::size_type pos = lines[0].find_first_not_of(' ', 8);
	if (pos == string::npos)
		throw invalid_argument("NdParser(): Problem specification in FitchFX proof is empty.");
	string::size_type pos2 = lines[0].find_last_not_of(' ');
	problem_str = lines[0].substr(pos, pos2 - pos + 1);
	for (size_t i = 1; i < lines.size(); i++)
		this->lines.emplace_back(i, lines[i]);

	// 2. Detect and check blocks.
	{
		map<size_t, set<size_t>> active; // (depth, {x|x:from})
		size_t k = 1;
		for (const FFxProofLine& proofLine : this->lines) {
			if (proofLine.reason.type == FFxProofReasonType::Assumption) {
				blocks.emplace(k, array<size_t, 2> { SIZE_MAX, proofLine.depth });
				active[proofLine.depth].emplace(k);
			}
			k++;
		}
		k = 1;
		size_t prevDepth = 0;
		for (const FFxProofLine& proofLine : this->lines) {
			auto check = [&]() {
				const set<size_t> s = active[prevDepth];
				bool found = false;
				for (size_t x : s)
					if (x < k) {
						if (found)
							throw invalid_argument("NdParser(): Cannot end multiple blocks in FitchFX proof at line number " + to_string(k - 1) + ".");
						found = true;
						active[prevDepth].erase(x);
						blocks[x][0] = k - 1;
					}
			};
			size_t depth = proofLine.depth;
			if (depth < prevDepth) {
				if (depth + 1 != prevDepth)
					throw invalid_argument("NdParser(): Cannot increase depth in FitchFX proof at line number " + to_string(k) + " by more than 1.");
				check();
			} else if (depth == prevDepth && proofLine.reason.type == FFxProofReasonType::Assumption)
				check();
			else if (depth > prevDepth) {
				if (depth != prevDepth + 1)
					throw invalid_argument("NdParser(): Cannot decrease depth in FitchFX proof at line number " + to_string(k) + " by more than 1.");
				if (proofLine.reason.type != FFxProofReasonType::Assumption)
					throw invalid_argument("NdParser(): Cannot increase depth in FitchFX proof at line number " + to_string(k) + " without reason \"Assumption\".");
			}
			prevDepth = proofLine.depth;
			k++;
		}
		for (pair<const size_t, set<size_t>>& p : active)
			for (size_t x : p.second)
				blocks[x][0] = size();
	}
	//#cout << "blocks = " << FctHelper::mapStringF(blocks, [](const pair<const size_t, array<size_t, 2>>& p) { return "[" + to_string(p.first) + "," + to_string(p.second[0]) + "](d=" + to_string(p.second[1]) + ")"; }) << endl;

	// 3. Check reasons for valid references.
	for (const pair<const size_t, array<size_t, 2>>& b : blocks)
		for (size_t i = b.first; i <= b.second[0]; i++) {
			size_t d = b.second[1];
			if (d == this->lines[i - 1].depth)
				blockStarts[i] = b.first;
		}
	//#cout << "blockStarts = " << FctHelper::mapString(blockStarts) << endl;
	size_t k = 1;
	for (const FFxProofLine& proofLine : this->lines) {
		const FFxProofReason& reason = proofLine.reason;
		const vector<size_t>& metadata = reason.metadata;
		if (!metadata.empty()) {
			size_t depth = proofLine.depth;
			auto checkLink = [&](size_t x) {
				size_t refDepth = this->lines[x - 1].depth;
				if (x >= k || refDepth > depth)
					throw invalid_argument("NdParser(): Invalid reference in FitchFX proof from line " + to_string(k) + " to " + to_string(x) + ".");
				else if (refDepth) { // referencing a previous line with non-higher depth of at least 1 => find containing block of referenced line
					map<size_t, size_t>::const_iterator searchResult = blockStarts.find(x);
					if (searchResult == blockStarts.end())
						throw invalid_argument("NdParser(): Missing block start in FitchFX proof for line number " + to_string(x) + " at depth " + to_string(refDepth) + ".");
					size_t refBlockStart = searchResult->second;
					size_t refBlockEnd = blocks.at(refBlockStart)[0];
					if (k > refBlockEnd)
						throw invalid_argument("NdParser(): Invalid reference in FitchFX proof from line " + to_string(k) + " to " + to_string(x) + ": Block [" + to_string(refBlockStart) + "," + to_string(refBlockEnd) + "] has already ended.");
				}
			};
			auto checkRange = [&](size_t from, size_t to) {
				map<size_t, array<size_t, 2>>::const_iterator searchResult = blocks.find(from);
				if (searchResult == blocks.end() || searchResult->second[0] != to)
					throw invalid_argument("NdParser(): Cannot refer to range \"" + to_string(from) + "-" + to_string(to) + "\" in FitchFX proof at line number " + to_string(k) + " since no such block exists.");
				size_t refDepth = this->lines[from - 1].depth;
				if (to >= k || refDepth > depth + 1)
					throw invalid_argument("NdParser(): Invalid reference in FitchFX proof from line " + to_string(k) + " to " + to_string(from) + "-" + to_string(to) + ".");
				else if (refDepth > 1) { // referencing a previous block sitting within non-higher depth of at least 1 => find containing block of referenced block
					size_t refBlockStart = 0;
					for (size_t lineNo = from - 1; lineNo > 0; lineNo--) {
						const FFxProofLine& line = this->lines[lineNo - 1];
						if (line.depth < refDepth) {
							if (line.reason.type == FFxProofReasonType::Assumption)
								refBlockStart = lineNo;
							else {
								map<size_t, size_t>::const_iterator searchResult = blockStarts.find(lineNo);
								if (searchResult == blockStarts.end())
									throw invalid_argument("NdParser(): Missing block start in FitchFX proof for line number " + to_string(lineNo) + " at depth " + to_string(line.depth) + ".");
								refBlockStart = searchResult->second;
							}
							break;
						}
					}
					if (!refBlockStart)
						throw invalid_argument("NdParser(): Missing block start in FitchFX proof for container of block " + to_string(from) + "-" + to_string(to) + " of depth " + to_string(refDepth) + ".");
					size_t refBlockEnd = blocks.at(refBlockStart)[0];
					if (k > refBlockEnd)
						throw invalid_argument("NdParser(): Invalid reference in FitchFX proof from line " + to_string(k) + " to " + to_string(from) + "-" + to_string(to) + ": Block [" + to_string(refBlockStart) + "," + to_string(refBlockEnd) + "] has already ended.");
				}
				if (refDepth < depth + 1)
					throw invalid_argument("NdParser(): Invalid reference in FitchFX proof from line " + to_string(k) + " to " + to_string(from) + "-" + to_string(to) + ": Referencing a block from higher up than the block's immediate container is disallowed.");
			};
			switch (reason.type) {
			case FFxProofReasonType::ConjunctionElimination:
			case FFxProofReasonType::DisjunctionIntroduction:
			case FFxProofReasonType::Reiteration: // m
				checkLink(metadata[0]);
				break; // no ranges
			case FFxProofReasonType::NegationElimination:
			case FFxProofReasonType::ConditionalElimination:
			case FFxProofReasonType::ConjunctionIntroduction:
			case FFxProofReasonType::BiconditionalElimination: // m,n
				checkLink(metadata[0]);
				checkLink(metadata[1]);
				break; // no ranges
			case FFxProofReasonType::IndirectProof:
			case FFxProofReasonType::NegationIntroduction:
			case FFxProofReasonType::ConditionalIntroduction: // i-j
				checkRange(metadata[0], metadata[1]);
				break;
			case FFxProofReasonType::BiconditionalIntroduction: // i-j,k-l
				checkRange(metadata[0], metadata[1]);
				checkRange(metadata[2], metadata[3]);
				break;
			case FFxProofReasonType::DisjunctionElimination: // m,i-j,k-l
				checkLink(metadata[0]);
				checkRange(metadata[1], metadata[2]);
				checkRange(metadata[3], metadata[4]);
				break;
			default:
				throw logic_error("FFxProof(): lines[" + to_string(k) + " - 1].reason.type == " + to_string(static_cast<unsigned>(reason.type)));
				break;
			}
		}
		k++;
	}
}

vector<uint32_t> NdParser::ffxToSymbolSequence(const string& formulaString) {
	return ffxFormulaGrammar().firstFitLex(formulaString);
}

// Parse grammar symbol sequence to a syntax tree
shared_ptr<DlFormula> NdParser::ffxToDlFormula(const vector<uint32_t>& symbolSequence, bool printParseError) {
	CfgParser parser(ffxFormulaGrammar());
	vector<const CfgParserChart*> charts = parser.earleyParse(symbolSequence);
	const shared_ptr<CfgParserState>& finalState = parser.getFinalState(charts);
	if (finalState) {
		shared_ptr<TreeNode<CfgParserState>> parseTree = parser.generateEarleyParseTree(finalState, charts);
		shared_ptr<DlFormula> syntaxTree = parser.generateASTFromParseTree(parseTree, { "(", ")" });
		static shared_ptr<String> _imply = make_shared<String>(DlCore::terminalStr_imply());
		static shared_ptr<String> _and = make_shared<String>(DlCore::terminalStr_and());
		static shared_ptr<String> _or = make_shared<String>(DlCore::terminalStr_or());
		static shared_ptr<String> _equiv = make_shared<String>(DlCore::terminalStr_equiv());
		static shared_ptr<String> _not = make_shared<String>(DlCore::terminalStr_not());
		static shared_ptr<String> _bot = make_shared<String>(DlCore::terminalStr_bot());
		static const map<string, shared_ptr<String>&> translation = { { "~", _not }, { "&", _and }, { "/\\", _and }, { "^", _and }, { "v", _or }, { "\\/", _or }, { ">", _imply }, { "->", _imply }, { "<>", _equiv }, { "<->", _equiv }, { "#", _bot } };
		DlCore::traverseLeftToRightInOrder(syntaxTree, [&](const shared_ptr<DlFormula>& node) {
			map<string, shared_ptr<String>&>::const_iterator searchResult = translation.find(node->getValue()->value);
			if (searchResult != translation.end())
				node->value() = searchResult->second;
		}, [](const shared_ptr<DlFormula>& node, const shared_ptr<DlFormula>& child) {
		}, [](const shared_ptr<DlFormula>& child, const shared_ptr<DlFormula>& node) {
		});
		return syntaxTree;
	} else {
		if (printParseError)
			cerr << "NdParser::toDlFormula(): Parse error." << endl;
		//#cout << parser.writeCharts("Failure", charts, symbolSequence) << endl;
		return nullptr;
	}
}

// Lex and parse string formula to a syntax tree
shared_ptr<DlFormula> NdParser::ffxToDlFormula(const string& formulaString, bool printParseError) {
	return ffxToDlFormula(ffxToSymbolSequence(formulaString), printParseError);
}

NdParser::FFxProof NdParser::parseFromFitchFxFile(const string& file, bool debug) {
	vector<string> lines = readFromFile(file, debug);
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	FFxProof ndProof(lines);
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to parse FitchFX proof." << endl;
	return ndProof;
}

}
}
