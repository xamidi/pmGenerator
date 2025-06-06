#include "NdConverter.h"

#include "../helper/FctHelper.h"
#include "../tree/TreeNode.h"
#include "../logic/DlCore.h"
#include "../logic/DlProofEnumerator.h"
#include "NdParser.h"

#include <boost/algorithm/string.hpp>

#include <numeric>

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::metamath;
using namespace xamidi::logic;

namespace xamidi {
namespace nd {

namespace {
enum class FFxExactProofReasonType {
	Assumption = 0, // "Assumption"
	IndirectProof = 1, // "IP  i-j"
	NegationIntroduction = 2, // "~I  i-j"
	NegationElimination = 3, // "~E  m,n"
	ConditionalIntroduction = 4, // ">I  i-j"
	ConditionalElimination = 5, // ">E  m,n"
	ConjunctionIntroduction = 6, // "&I  m,n"
	ConjunctionElimination_l = 7, // "&E  m: (ψ&φ)⊢ψ"
	ConjunctionElimination_r = 8, // "&E  m: (ψ&φ)⊢φ"
	DisjunctionIntroduction_l = 9, // "vI  m: ψ⊢(ψvφ)"
	DisjunctionIntroduction_r = 10, // "vI  m: ψ⊢(φvψ)"
	DisjunctionElimination = 11, // "vE  m,i-j,k-l"
	BiconditionalIntroduction = 12, // "<>I  i-j,k-l"
	BiconditionalElimination_l = 13, // "<>E  m,n: {(ψ<>φ),ψ}⊢φ"
	BiconditionalElimination_r = 14, // "<>E  m,n: {(ψ<>φ),φ}⊢ψ"
	Reiteration = 15 // "Reit m"
};
inline string stringOfFFxExactProofReasonType(FFxExactProofReasonType type) {
	switch (type) {
	case FFxExactProofReasonType::Assumption:
		return "Assumption";
	case FFxExactProofReasonType::IndirectProof:
		return "IP";
	case FFxExactProofReasonType::NegationIntroduction:
		return "~I";
	case FFxExactProofReasonType::NegationElimination:
		return "~E";
	case FFxExactProofReasonType::ConditionalIntroduction:
		return ">I";
	case FFxExactProofReasonType::ConditionalElimination:
		return ">E";
	case FFxExactProofReasonType::ConjunctionIntroduction:
		return "&I";
	case FFxExactProofReasonType::ConjunctionElimination_l:
		return "&E-l";
	case FFxExactProofReasonType::ConjunctionElimination_r:
		return "&E-r";
	case FFxExactProofReasonType::DisjunctionIntroduction_l:
		return "vI-l";
	case FFxExactProofReasonType::DisjunctionIntroduction_r:
		return "vI-r";
	case FFxExactProofReasonType::DisjunctionElimination:
		return "vE";
	case FFxExactProofReasonType::BiconditionalIntroduction:
		return "<>I";
	case FFxExactProofReasonType::BiconditionalElimination_l:
		return "<>E-l";
	case FFxExactProofReasonType::BiconditionalElimination_r:
		return "<>E-r";
	case FFxExactProofReasonType::Reiteration:
		return "Reit";
	default:
		throw logic_error("type == " + to_string(static_cast<unsigned>(type)));
	}
}
inline void switchRefs(char& c, bool& inReference, unsigned& refIndex, const auto& inRefAction, const auto& outRefAction) {
	if (inReference)
		switch (c) {
		case '0':
			refIndex = 10 * refIndex;
			break;
		case '1':
			refIndex = 10 * refIndex + 1;
			break;
		case '2':
			refIndex = 10 * refIndex + 2;
			break;
		case '3':
			refIndex = 10 * refIndex + 3;
			break;
		case '4':
			refIndex = 10 * refIndex + 4;
			break;
		case '5':
			refIndex = 10 * refIndex + 5;
			break;
		case '6':
			refIndex = 10 * refIndex + 6;
			break;
		case '7':
			refIndex = 10 * refIndex + 7;
			break;
		case '8':
			refIndex = 10 * refIndex + 8;
			break;
		case '9':
			refIndex = 10 * refIndex + 9;
			break;
		case ']':
			inRefAction();
			refIndex = 0;
			inReference = false;
			break;
		default:
			throw invalid_argument("NdConverter::switchRefs(): Invalid character '" + string { c } + "': Not part of a proof reference.");
		}
	else if (c == '[')
		inReference = true;
	else
		outRefAction();
}
}

void NdConverter::convertFitchFxFileToDProofSummary(const string& ffxFile, const string* optIn_outputFile, const string* optIn_baseProofSummaryFile, bool normalPolishNotation, bool printInfixUnicode, bool pure, bool targetEverything, bool debug) {
	chrono::time_point<chrono::steady_clock> startTime;

	// 1. Parse natural deduction proof.
	NdParser::FFxProof ndProof = NdParser::parseFromFitchFxFile(ffxFile, debug);
	if (!pure && !optIn_baseProofSummaryFile)
		throw invalid_argument("NdConverter(): Heterogeneous operators require a user-defined base system.");

	// 2. Build library of relevant theorems and proofs.
	if (debug)
		startTime = chrono::steady_clock::now();
	const array<const char*, 22> thms = [&pure]() {
		constexpr array<const char*, 22> thms_pure = { "CpCqNCpNq", "CpCqNCqNp", "CNCpNqp", "CNCpNqq", "CpCNpq", "CpCNqp", "CCNpqCCprCCqrr", "CCNpqCCqrCCprr", "CCpqCCNprCCrqq", "CCpqCCrqCCNprq", "CCpqCCNrpCCrqq", "CCpqCCrqCCNrpq", "CCpqCCqpNCCpqNCqp", "CCpqCCqpNCCqpNCpq", "CNCCpqNCqpCpq", "CNCCpqNCqpCqp", "CCpNCqqNp", "CNpCpNCqq", "CpCNpNCqq", "CCNpNCqqp", "Cpp", "CCpqCpCrq" };
		constexpr array<const char*, 22> thms_impure = { "CpCqKpq", "CpCqKqp", "CKpqp", "CKpqq", "CpApq", "CpAqp", "CApqCCprCCqrr", "CApqCCqrCCprr", "CCpqCAprCCrqq", "CCpqCCrqCAprq", "CCpqCArpCCrqq", "CCpqCCrqCArpq", "CCpqCCqpEpq", "CCpqCCqpEqp", "CEpqCpq", "CEpqCqp", "CCpONp", "CNpCpO", "CpCNpO", "CCNpOp", "Cpp", "CCpqCpCrq" };
		return pure ? thms_pure : thms_impure;
	}();
	const array<const char*, 22> prfs = [&pure]() {
		constexpr array<const char*, 22> prfs_pure = { "DD2D13DD2D1D2DD2DD2D13DD2D13111", "DD2D1D2DD2D13DD2D1D2DD2DD2D13DD2D131111", "D3DD2D1D3DD2DD2D13DD2D1311DD2D131", "D3DD2D1D3DD2DD2D13DD2D13111", "DD2D1D2DD2D1311", "1", "DD2D1DD2D1DD2D1DD22D11DD2D112D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D1D2DD2D1211", "DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D1D2DD2D1211", "DD2D1D2DD2D12DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D1D2DD2D1211DD2D111", "DD2D1D2DD2D12DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D121DD2D111", "DD2D1D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D121", "DD2D1DD2D1DD2D1DD22D11DD2D112D2D1DD2D1D2D1DD2DD2D13D2DD2D1311DD2D1DD2D1D2DD2D1211DD2D13D2D1D3DD2DD2D13DD2D1311DD2D121", "[0]", "[1]", "[2]", "[3]", "DD2DD2D13DD2D1DD22D2DD2D13DD2D1311D1DD211", "DD2D131", "[4]", "DD23D1DD211", "DD211", "D2D11" };
		constexpr array<const char*, 22> prfs_impure = { "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "DD211", "D2D11" };
		return pure ? prfs_pure : prfs_impure;
	}();
	const vector<shared_ptr<DlFormula>> relevantTheorems = [&thms]() {
		vector<shared_ptr<DlFormula>> _;
		for (const char* s : thms) {
			shared_ptr<DlFormula> f;
			DlCore::fromPolishNotation(f, s);
			_.push_back(f);
		}
		return _;
	}();
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to obtain " << relevantTheorems.size() << " relevant theorems." << endl;
	const array<set<FFxExactProofReasonType>, 22> enabledRules = [&pure]() {
		using RT = FFxExactProofReasonType;
		static const array<set<RT>, 22> enabledRules_pure = []() {
			array<set<RT>, 22> _;
			_[0] = { RT::ConjunctionIntroduction, RT::BiconditionalIntroduction };
			_[1] = { RT::ConjunctionIntroduction, RT::BiconditionalIntroduction };
			_[2] = { RT::ConjunctionElimination_l, RT::BiconditionalElimination_l };
			_[3] = { RT::ConjunctionElimination_r, RT::BiconditionalElimination_r };
			_[4] = { RT::DisjunctionIntroduction_l, RT::NegationElimination };
			_[5] = { RT::DisjunctionIntroduction_r };
			_[6] = { RT::DisjunctionElimination };
			_[7] = { RT::DisjunctionElimination };
			_[8] = { RT::DisjunctionElimination };
			_[9] = { RT::DisjunctionElimination };
			_[10] = { RT::DisjunctionElimination };
			_[11] = { RT::DisjunctionElimination };
			_[12] = { RT::BiconditionalIntroduction };
			_[13] = { RT::BiconditionalIntroduction };
			_[14] = { RT::BiconditionalElimination_l };
			_[15] = { RT::BiconditionalElimination_r };
			_[16] = { RT::NegationIntroduction };
			_[17] = { RT::NegationElimination };
			_[18] = { RT::NegationElimination };
			_[19] = { RT::IndirectProof };
			return _;
		}();
		static const array<set<RT>, 22> enabledRules_impure = []() {
			array<set<RT>, 22> _;
			_[0] = { RT::ConjunctionIntroduction };
			_[1] = { RT::ConjunctionIntroduction };
			_[2] = { RT::ConjunctionElimination_l };
			_[3] = { RT::ConjunctionElimination_r };
			_[4] = { RT::DisjunctionIntroduction_l };
			_[5] = { RT::DisjunctionIntroduction_r };
			_[6] = { RT::DisjunctionElimination };
			_[7] = { RT::DisjunctionElimination };
			_[8] = { RT::DisjunctionElimination };
			_[9] = { RT::DisjunctionElimination };
			_[10] = { RT::DisjunctionElimination };
			_[11] = { RT::DisjunctionElimination };
			_[12] = { RT::BiconditionalIntroduction };
			_[13] = { RT::BiconditionalIntroduction };
			_[14] = { RT::BiconditionalElimination_l };
			_[15] = { RT::BiconditionalElimination_r };
			_[16] = { RT::NegationIntroduction };
			_[17] = { RT::NegationElimination };
			_[18] = { RT::NegationElimination };
			_[19] = { RT::IndirectProof };
			return _;
		}();
		return pure ? enabledRules_pure : enabledRules_impure;
	}();

	// 3. Build internal proof summary from library.
	string internalProofSummary;
	{
		string input;
		vector<string> dProofs;
		for (size_t i = 0; i < prfs.size(); i++) {
			const char* s = prfs[i];
			if (s[0] && s[1] && s[0] != '[')
				dProofs.push_back(s);
		}
		if (debug)
			cout << "Going to build internal proof summary with " << dProofs.size() << " relevant proofs." << endl;
		DlProofEnumerator::printProofs(dProofs, normalPolishNotation ? DlFormulaStyle::PolishStandard : DlFormulaStyle::PolishNumeric, false, true, UINT_MAX, true, nullptr, nullptr, debug, &internalProofSummary, nullptr, !debug);
		//#cout << internalProofSummary << flush;
	}

	// 4. Define procedure to append viable parts of the internal proof summary to another summary of potentially different axioms.
	auto mountTranslatedInternalProofSummary = [&](vector<string>& abstractDProof, vector<shared_ptr<DlFormula>>& conclusions, const map<size_t, size_t>& axiomToUserAxiom, const map<size_t, size_t>& axiomToUserIndex, size_t shift) -> map<size_t, size_t> {
		bool use3 = axiomToUserAxiom.count(3) || axiomToUserIndex.count(3);
		vector<string> primitiveTranslation;
		for (size_t ax = 1; ax <= 2 + (use3 ? 1 : 0); ax++) {
			map<size_t, size_t>::const_iterator searchResult = axiomToUserIndex.find(ax);
			if (searchResult != axiomToUserIndex.end())
				primitiveTranslation.push_back("[" + to_string(searchResult->second) + "]");
			else
				primitiveTranslation.push_back(to_string(axiomToUserAxiom.at(ax)));
		}
		map<size_t, size_t> indexTranslation; // proof step indices from internal proof summary to new composed summary
		auto substitute = [&](size_t i, const string& s, bool& use) -> string {
			string result;
			bool inReference = false;
			unsigned refIndex = 0;
			for (char c : s) {
				switchRefs(c, inReference, refIndex, [&]() {
					map<size_t, size_t>::const_iterator searchResult = indexTranslation.find(refIndex);
					if (searchResult == indexTranslation.end()) {
						use = false;
						return;
					}
					result += "[" + to_string(searchResult->second) + "]";
				}, [&]() {
					switch (c) {
					case 'D':
						result += "D";
						break;
					case '1':
						result += primitiveTranslation[0];
						break;
					case '2':
						result += primitiveTranslation[1];
						break;
					case '3':
						if (!use3) {
							use = false;
							return;
						}
						result += primitiveTranslation[2];
						break;
					default:
						throw logic_error("c == '" + string { c } + "'");
					}
				});
				if (!use)
					return "";
			}
			if (inReference)
				throw invalid_argument("NdConverter(): Missing character ']' after '['.");
			indexTranslation.emplace(i, indexTranslation.size() + shift);
			return result;
		};
		map<size_t, array<string, 2>> lines;
		stringstream ss(internalProofSummary);
		string line;
		size_t i = 0;
		while (getline(ss, line))
			if (line.starts_with("[")) {
				string::size_type offset = FctHelper::digitsNum_uint64(i) + 3;
				string::size_type pos = line.find(" = ");
				bool use = true;
				string translatedProof = substitute(i, line.substr(pos + 3), use);
				if (use)
					lines.emplace(indexTranslation[i], array<string, 2> { line.substr(offset, pos - offset), translatedProof });
				i++;
			}
		//#cout << FctHelper::mapStringF(lines, [](const pair<const size_t, array<string, 2>>& p) { return "[" + to_string(p.first) + "] " + p.second[0] + " = " + p.second[1]; }, { }, { }, "\n") << endl;
		for (const pair<const size_t, array<string, 2>>& p : lines) {
			abstractDProof.push_back(p.second[1]);
			const string& conclusion = p.second[0];
			shared_ptr<DlFormula> f;
			if (normalPolishNotation) {
				if (!DlCore::fromPolishNotation(f, conclusion, false, debug))
					throw domain_error("Could not parse \"" + conclusion + "\" as a formula in normal Polish notation.");
			} else if (!DlCore::fromPolishNotation_noRename(f, conclusion, false, debug))
				throw domain_error("Could not parse \"" + conclusion + "\" as a formula in dotted Polish notation.");
			conclusions.push_back(DRuleParser::AxiomInfo(conclusion, f).refinedAxiom);
		}
		return indexTranslation;
	};

	// 5. Obtain proof summary of rule-enabling theorems.
	vector<DRuleParser::AxiomInfo> targetAxioms;
	vector<string> abstractDProof;
	vector<shared_ptr<DlFormula>> conclusions;
	vector<size_t> fundamentalLengths;
	map<size_t, size_t> axiomToUserAxiom;
	map<size_t, size_t> axiomToUserIndex;
	auto printTargetSystem = [&]() {
		vector<string> targetAxiomFormulas;
		for (size_t i = 0; i < targetAxioms.size(); i++)
			targetAxiomFormulas.push_back(normalPolishNotation ? DlCore::toPolishNotation(targetAxioms[i].refinedAxiom) : DlCore::toPolishNotation_noRename(targetAxioms[i].refinedAxiom));
		cout << "Target system is (" << FctHelper::vectorString(targetAxiomFormulas, { }, { }, ",") << ")." << endl;
	};
	if (optIn_baseProofSummaryFile) {

		// 5.1 Parse user-defined proof summary, filter out duplicates, and obtain fundamental lengths.
		vector<size_t> fundamentalLengthsFromUser;
		{
			if (debug)
				startTime = chrono::steady_clock::now();
			DlProofEnumerator::convertProofSummaryToAbstractDProof(*optIn_baseProofSummaryFile, &targetAxioms, &abstractDProof, nullptr, true, normalPolishNotation, false, debug);
			if (debug)
				cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to read and convert proof summary from ./" << *optIn_baseProofSummaryFile << " to abstract D-proof of " << abstractDProof.size() << " theorem" << (abstractDProof.size() == 1 ? "." : "s.") << endl;
			printTargetSystem();
			if (debug)
				cout << "Going to recombine abstract D-proof of " << abstractDProof.size() << " theorem" << (abstractDProof.size() == 1 ? "" : "s") << " from user-defined proof summary." << endl;
			abstractDProof = DRuleParser::recombineAbstractDProof(abstractDProof, conclusions, &targetAxioms, true, nullptr, nullptr, 1, nullptr, debug, SIZE_MAX, true, SIZE_MAX, SIZE_MAX, true, false, 0, false, nullptr, false, false, false, !debug);
			vector<size_t> userIndices(abstractDProof.size());
			iota(userIndices.begin(), userIndices.end(), 0);
			fundamentalLengthsFromUser = DRuleParser::measureFundamentalLengthsInAbstractDProof(userIndices, abstractDProof, conclusions);
		}

		// 5.2 Detect default axioms in user-defined summary.
		{
			vector<shared_ptr<DlFormula>> defaultAxioms;
			for (const char* ax : { "C0C1.0", "CC0C1.2CC0.1C0.2", "CCN0N1C1.0" })
				defaultAxioms.push_back([](const string& s) -> shared_ptr<DlFormula> { shared_ptr<DlFormula> f; if (!DlCore::fromPolishNotation_noRename(f, s)) throw logic_error("Could not parse \"" + s + "\" as a formula."); return f; }(ax));
			vector<size_t> fundamentalLengthsOfDefaultAxioms(defaultAxioms.size(), SIZE_MAX);
			for (size_t i = 0; i < defaultAxioms.size(); i++)
				for (size_t j = 0; j < targetAxioms.size(); j++)
					if (DlCore::isSchemaOf(targetAxioms[j].refinedAxiom, defaultAxioms[i]) && fundamentalLengthsOfDefaultAxioms[i] > 1) {
						axiomToUserAxiom.emplace(i + 1, j + 1);
						fundamentalLengthsOfDefaultAxioms[i] = 1;
					}
			for (size_t i = 0; i < defaultAxioms.size(); i++)
				if (!axiomToUserAxiom.count(i + 1))
					for (size_t j = 0; j < conclusions.size(); j++)
						if (DlCore::isSchemaOf(conclusions[j], defaultAxioms[i]) && fundamentalLengthsOfDefaultAxioms[i] > fundamentalLengthsFromUser[j]) {
							axiomToUserIndex.emplace(i + 1, j);
							fundamentalLengthsOfDefaultAxioms[i] = fundamentalLengthsFromUser[j];
						}
			if (fundamentalLengthsOfDefaultAxioms[0] == SIZE_MAX)
				throw invalid_argument("NdConverter(): No proof for default axiom (A1) CpCqp was specified.");
			if (fundamentalLengthsOfDefaultAxioms[1] == SIZE_MAX)
				throw invalid_argument("NdConverter(): No proof for default axiom (A2) CCpCqrCCpqCpr was specified.");
			bool use3 = fundamentalLengthsOfDefaultAxioms[2] != SIZE_MAX;
			if (debug)
				cout << "User-defined proofs of (A1),(A2)" << (use3 ? ",(A3)" : "") << " have fundamental lengths of " << fundamentalLengthsOfDefaultAxioms[0] << "," << fundamentalLengthsOfDefaultAxioms[1] << (use3 ? "," + to_string(fundamentalLengthsOfDefaultAxioms[2]) : "") << ", respectively." << (use3 ? "" : " No proof for (A3) is given.") << endl;
		}
		//#cout << "axiomToUserAxiom = " << FctHelper::mapString(axiomToUserAxiom) << endl;
		//#cout << "axiomToUserIndex = " << FctHelper::mapString(axiomToUserIndex) << endl;

		// 5.3 Mount internal proof summary to user-defined proof summary, filter out suboptimal parts, and obtain fundamental lengths.
		if (debug)
			cout << "Going to enrich user-defined proof summary with internal proofs and filter out suboptimal variants." << endl;
		mountTranslatedInternalProofSummary(abstractDProof, conclusions, axiomToUserAxiom, axiomToUserIndex, abstractDProof.size());
		abstractDProof = DRuleParser::recombineAbstractDProof(abstractDProof, conclusions, &targetAxioms, true, nullptr, nullptr, 1, nullptr, debug, SIZE_MAX, true, SIZE_MAX, SIZE_MAX, true, false, 0, false, nullptr, false, false, false, !debug);
		vector<size_t> allIndices(abstractDProof.size());
		iota(allIndices.begin(), allIndices.end(), 0);
		fundamentalLengths = DRuleParser::measureFundamentalLengthsInAbstractDProof(allIndices, abstractDProof, conclusions);
	} else { // no input proof summary => pure, default system, all ND-rules are supported
		axiomToUserAxiom = { { 1, 1 }, { 2, 2 }, { 3, 3 } };

		// 5.4 Parse internal proof summary, filter out duplicates, and obtain fundamental lengths.
		vector<size_t> fundamentalLengthsFromUser;
		{
			if (debug)
				startTime = chrono::steady_clock::now();
			DlProofEnumerator::convertProofSummaryToAbstractDProof(internalProofSummary, &targetAxioms, &abstractDProof, nullptr, false, normalPolishNotation, false, debug);
			if (debug)
				cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to convert proof summary to abstract D-proof." << endl;
			printTargetSystem();
			if (debug)
				cout << "Going to recombine abstract D-proof of " << abstractDProof.size() << " theorem" << (abstractDProof.size() == 1 ? "" : "s") << " from internal proof summary." << endl;
			abstractDProof = DRuleParser::recombineAbstractDProof(abstractDProof, conclusions, &targetAxioms, true, nullptr, nullptr, 1, nullptr, debug, SIZE_MAX, true, SIZE_MAX, SIZE_MAX, true, false, 0, false, nullptr, false, false, false, !debug);
			vector<size_t> allIndices(abstractDProof.size());
			iota(allIndices.begin(), allIndices.end(), 0);
			fundamentalLengths = DRuleParser::measureFundamentalLengthsInAbstractDProof(allIndices, abstractDProof, conclusions);
		}
	}

	// 6. Track default axioms, helper theorems and ND-proof reasons that are supported for conversion.
	map<size_t, pair<bool, size_t>> locationsForDefaultAxioms;
	map<size_t, string> stringsForDefaultAxioms;
	map<FFxExactProofReasonType, pair<bool, size_t>> locationsForNdRuleHelpers;
	map<FFxExactProofReasonType, string> stringsForNdRuleHelpers;
	string proof_id; // (id) ψ→ψ (i.e. Cpp) [ID 20, default:DD211]
	string proof_ins; // (ins) (ψ→φ)→(ψ→(χ→φ)) (i.e. CCpqCpCrq) [ID 21, default: D2D11]
	{
		for (const pair<const size_t, size_t>& p : axiomToUserIndex)
			locationsForDefaultAxioms[p.first] = { false, p.second };
		for (const pair<const size_t, size_t>& p : axiomToUserAxiom)
			locationsForDefaultAxioms[p.first] = { true, p.second };
		for (const pair<const size_t, pair<bool, size_t>>& p : locationsForDefaultAxioms)
			stringsForDefaultAxioms[p.first] = (p.second.first ? to_string(p.second.second) : "[" + to_string(p.second.second) + "]");
		vector<size_t> axiomsOfRelevantTheorems(relevantTheorems.size());
		vector<size_t> bestIndicesOfRelevantTheorems(relevantTheorems.size());
		vector<size_t> fundamentalLengthsOfRelevantTheorems(relevantTheorems.size(), SIZE_MAX);
		for (size_t i = 0; i < relevantTheorems.size(); i++) {
			for (size_t j = 0; j < targetAxioms.size(); j++)
				if (DlCore::isSchemaOf(targetAxioms[j].refinedAxiom, relevantTheorems[i])) {
					fundamentalLengthsOfRelevantTheorems[i] = 1;
					axiomsOfRelevantTheorems[i] = j + 1;
				}
			for (size_t j = 0; j < abstractDProof.size(); j++)
				if (DlCore::isSchemaOf(conclusions[j], relevantTheorems[i])) {
					size_t& bestFunLen = fundamentalLengthsOfRelevantTheorems[i];
					size_t funLen = fundamentalLengths[j];
					if (bestFunLen > funLen) {
						bestFunLen = funLen;
						bestIndicesOfRelevantTheorems[i] = j;
					}
				}
		}
		if (debug) {
			size_t i = 0;
			cout << "Fundamental lengths of relevant theorems: " << FctHelper::vectorStringF(fundamentalLengthsOfRelevantTheorems, [&](size_t x) { return "[" + to_string(i++) + "]:" + (x == SIZE_MAX ? "-" : to_string(x)); }, { }, { }) << endl;
		}
		set<FFxExactProofReasonType> supportedNdRules = { FFxExactProofReasonType::Assumption, FFxExactProofReasonType::ConditionalIntroduction, FFxExactProofReasonType::ConditionalElimination, FFxExactProofReasonType::Reiteration };
		for (size_t i = 0; i < relevantTheorems.size(); i++)
			if (fundamentalLengthsOfRelevantTheorems[i] < SIZE_MAX) {
				const set<FFxExactProofReasonType>& s = enabledRules[i];
				supportedNdRules.insert(s.begin(), s.end());
				if (fundamentalLengthsOfRelevantTheorems[i] > 1)
					for (const FFxExactProofReasonType type : s) {
						map<FFxExactProofReasonType, pair<bool, size_t>>::iterator searchResult = locationsForNdRuleHelpers.find(type);
						if (searchResult == locationsForNdRuleHelpers.end() || fundamentalLengths[searchResult->second.second] > fundamentalLengthsOfRelevantTheorems[i]) // pick smallest variant
							locationsForNdRuleHelpers[type] = { false, bestIndicesOfRelevantTheorems[i] };
					}
				else
					for (const FFxExactProofReasonType type : s) {
						map<FFxExactProofReasonType, pair<bool, size_t>>::iterator searchResult = locationsForNdRuleHelpers.find(type);
						if (searchResult == locationsForNdRuleHelpers.end() || !searchResult->second.first) // pick smallest variant
							locationsForNdRuleHelpers[type] = { true, axiomsOfRelevantTheorems[i] };
					}
			}
		for (const pair<const FFxExactProofReasonType, pair<bool, size_t>>& p : locationsForNdRuleHelpers)
			stringsForNdRuleHelpers[p.first] = (p.second.first ? to_string(p.second.second) : "[" + to_string(p.second.second) + "]");
		if (debug) {
			cout << supportedNdRules.size() << " of 16 FitchFX rules are supported: " << FctHelper::setStringF(supportedNdRules, [](FFxExactProofReasonType type) { return stringOfFFxExactProofReasonType(type); }, "{ ", " }") << endl;
			set<FFxExactProofReasonType> unsupportedNdRules;
			for (size_t i = 0; i < 16; i++) {
				FFxExactProofReasonType type = static_cast<FFxExactProofReasonType>(i);
				if (!supportedNdRules.count(type))
					unsupportedNdRules.emplace(type);
			}
			if (!unsupportedNdRules.empty())
				cout << unsupportedNdRules.size() << " FitchFX rule" << (unsupportedNdRules.size() == 1 ? " is" : "s are") << " unsupported: " << FctHelper::setStringF(unsupportedNdRules, [](FFxExactProofReasonType type) { return stringOfFFxExactProofReasonType(type); }, "{ ", " }") << endl;
			vector<string> ruleHelpers;
			vector<string> ruleHelpers_funLen;
			for (const pair<const FFxExactProofReasonType, string>& p : stringsForNdRuleHelpers)
				ruleHelpers.push_back("(" + stringOfFFxExactProofReasonType(p.first) + "):" + p.second);
			for (const pair<const FFxExactProofReasonType, pair<bool, size_t>>& p : locationsForNdRuleHelpers)
				ruleHelpers_funLen.push_back(p.second.first ? "1" : to_string(fundamentalLengths[p.second.second]));
			vector<string> defaultAxioms;
			vector<string> defaultAxioms_funLen;
			for (const pair<const size_t, string>& p : stringsForDefaultAxioms)
				defaultAxioms.push_back("(A" + to_string(p.first) + "):" + p.second);
			for (const pair<const size_t, pair<bool, size_t>>& p : locationsForDefaultAxioms)
				defaultAxioms_funLen.push_back(p.second.first ? "1" : to_string(fundamentalLengths[p.second.second]));
			size_t i = 0;
			cout << "ND-rule helpers in prepared proof summary: " << FctHelper::vectorStringF(ruleHelpers, [&](const string& s) { string r; size_t l = ruleHelpers_funLen[i].length(); if (l > s.length()) r += string(l - s.length(), ' '); r += s; i++; return r; }, { }, { }) << endl;
			i = 0;
			cout << "               - with fundamental lengths: " << FctHelper::vectorStringF(ruleHelpers_funLen, [&](const string& s) { string r; size_t l = ruleHelpers[i].length(); if (l > s.length()) r += string(l - s.length(), ' '); r += s; i++; return r; }, { }, { }) << endl;
			i = 0;
			cout << "Default axioms in prepared proof summary: " << FctHelper::vectorStringF(defaultAxioms, [&](const string& s) { string r; size_t l = defaultAxioms_funLen[i].length(); if (l > s.length()) r += string(l - s.length(), ' '); r += s; i++; return r; }, { }, { }) << endl;
			i = 0;
			cout << "              - with fundamental lengths: " << FctHelper::vectorStringF(defaultAxioms_funLen, [&](const string& s) { string r; size_t l = defaultAxioms[i].length(); if (l > s.length()) r += string(l - s.length(), ' '); r += s; i++; return r; }, { }, { }) << endl;
		}
		if (fundamentalLengthsOfRelevantTheorems[20] < SIZE_MAX)
			proof_id = fundamentalLengthsOfRelevantTheorems[20] > 1 ? "[" + to_string(bestIndicesOfRelevantTheorems[20]) + "]" : to_string(axiomsOfRelevantTheorems[20]);
		else
			throw logic_error("fundamentalLengthsOfRelevantTheorems[20] == SIZE_MAX");
		if (fundamentalLengthsOfRelevantTheorems[21] < SIZE_MAX)
			proof_ins = fundamentalLengthsOfRelevantTheorems[21] > 1 ? "[" + to_string(bestIndicesOfRelevantTheorems[21]) + "]" : to_string(axiomsOfRelevantTheorems[21]);
		else
			throw logic_error("fundamentalLengthsOfRelevantTheorems[21] == SIZE_MAX");
		if (debug) {
			cout << "(id) Cpp = " << proof_id << " (fundamental length " << fundamentalLengthsOfRelevantTheorems[20] << ")" << endl;
			cout << "(ins) CCpqCpCrq = " << proof_ins << " (fundamental length " << fundamentalLengthsOfRelevantTheorems[21] << ")" << endl;
		}
	}

	// 7. Track which variants of ND-proof reasons are used for conversion.
	map<FFxExactProofReasonType, size_t> ruleVariants;
	for (FFxExactProofReasonType type : { FFxExactProofReasonType::NegationElimination, FFxExactProofReasonType::BiconditionalIntroduction, FFxExactProofReasonType::DisjunctionElimination, FFxExactProofReasonType::ConjunctionIntroduction }) {
		map<FFxExactProofReasonType, pair<bool, size_t>>::const_iterator searchResult = locationsForNdRuleHelpers.find(type);
		if (searchResult != locationsForNdRuleHelpers.end()) {
			const shared_ptr<DlFormula>& used = searchResult->second.first ? targetAxioms[searchResult->second.second - 1].refinedAxiom : conclusions[searchResult->second.second];
			string used_PN = DlCore::toPolishNotation(used);
			vector<size_t> relevantIndices;
			switch (type) {
			case FFxExactProofReasonType::NegationElimination:
				relevantIndices = { 17, 18 };
				break;
			case FFxExactProofReasonType::BiconditionalIntroduction:
				relevantIndices = { 12, 13 };
				break;
			case FFxExactProofReasonType::DisjunctionElimination:
				relevantIndices = { 6, 7, 8, 9, 10, 11 };
				break;
			case FFxExactProofReasonType::ConjunctionIntroduction:
				relevantIndices = { 0, 1 };
				break;
			default:
				throw logic_error("type == " + to_string(static_cast<unsigned>(type)));
			}
			for (size_t i : relevantIndices) {
				const shared_ptr<DlFormula>& helperTheorem = relevantTheorems[i];
				if (DlCore::isSchemaOf(used, helperTheorem))
					ruleVariants[type] = i;
			}
		}
	}
	if (debug)
		cout << "Rule variants: " << FctHelper::mapStringF(ruleVariants, [](const pair<const FFxExactProofReasonType, size_t>& p) { return "(" + stringOfFFxExactProofReasonType(p.first) + "):[ID=" + to_string(p.second) + "]"; }, { }, { }) << endl;

	// 8. Define building blocks of D-proof from ND-elements.
	// (a1-<n+1>) := (D<CCpqCpCrq>)ⁿ1:CpCq₀Cq₁…Cqₙp
	auto a1 = [&](size_t n) -> string {
		if (!n)
			throw logic_error("Called a1(0).");
		stringstream ss;
		for (size_t i = 1; i < n; i++)
			ss << "D" << proof_ins;
		ss << stringsForDefaultAxioms[1];
		return ss.str();
	};
	// (a1i-<n>) := (D1)ⁿ<#1>:Ca₁…Caₙp, for 1 premise of schema p
	auto a1i = [&](size_t n, const string& arg1) -> string {
		stringstream ss;
		for (size_t i = 0; i < n; i++)
			ss << "D" << stringsForDefaultAxioms[1];
		ss << arg1;
		return ss.str();
	};
	// (a1-0-a1i-<m>) := (D1)^m<Cpp>:Ca1…CaₘCpp
	// (a1-<n+1>-a1i-<m>) := (D1)^m(D<CCpqCpCrq>)ⁿ1:Ca₁…CaₘCpCq₀Cq₁…Cqₙp
	auto a1_a1i = [&](size_t n, size_t m) -> string {
		if (debug)
			cout << "[CALL] (a1-" << n << "-a1i-" << m << ")" << endl;
		return n ? a1i(m, a1(n)) : a1i(m, proof_id);
	};
	// (σ_mpd-0) := D ; (σ_mpd-<n+1>) := (σ_mpd-<n>)²(D1)ⁿ2
	auto s_mpd = [&](size_t n) -> string {
		auto _ = [&](size_t n, const auto& me) -> string {
			stringstream ss;
			if (n) {
				const string s_mpd_prev = me(n - 1, me);
				ss << s_mpd_prev << s_mpd_prev << a1i(n - 1, stringsForDefaultAxioms[2]);
			} else
				ss << "D";
			return ss.str();
		};
		return _(n, _);
	};
	// (mpd-<n>) := (σ_mpd-<n>)<#2><#1>:Ca₁…Caₙq, for 2 premises of schemas Ca₁…Caₙp,Ca₁…CaₙCpq
	auto mpd = [&](size_t n, const string& arg1, const string& arg2) -> string {
		stringstream ss;
		ss << s_mpd(n) << arg2 << arg1;
		return ss.str();
	};
	// (slip-0-<m>) := (a1i-<m>) ; (slip-<n+1>-<m>) := ((σ_mpd-<n>)(D1)ⁿ<CCpqCpCrq>)^m<#1>:Ca₁…CaₙCpCr₁…CrₘCq, for 1 premise of schema Ca₁…CaₙCpq
	// Can be used to slip in m new antecedents after n known antecedents for a known conclusion.
	auto slip = [&](size_t n, size_t m, const string& arg1) -> string {
		if (debug)
			cout << "[CALL] (slip-" << n << "-" << m << ")" << endl;
		if (!m)
			return arg1;
		if (!n)
			return a1i(m, arg1);
		const string slip_n_1_prefix = s_mpd(n - 1) + a1i(n - 1, proof_ins);
		stringstream ss;
		for (size_t i = 0; i < m; i++)
			ss << slip_n_1_prefix;
		ss << arg1;
		return ss.str();
	};
	auto getRuleHelper = [&](const string& name, FFxExactProofReasonType type, size_t n, size_t* ruleVariant = nullptr) -> string {
		if (!n)
			throw logic_error("Called rule_" + name + "(0, ...).");
		map<FFxExactProofReasonType, string>::const_iterator searchResult = stringsForNdRuleHelpers.find(type);
		if (searchResult == stringsForNdRuleHelpers.end())
			throw domain_error("Called rule_" + name + "(" + to_string(n) + ", ...) when ND-rule helper unproven.");
		if (ruleVariant)
			*ruleVariant = ruleVariants[type];
		return searchResult->second;
	};
	// (IP-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CCNpOp><#1>:Ca₁…Caₙp, for 1 premise of schema Ca₁…CaₙCNpO
	auto rule_IP = [&](size_t n, const string& arg1) -> string {
		if (debug)
			cout << "[CALL] (IP-" << n << ")" << endl;
		string ruleHelper = getRuleHelper("IP", FFxExactProofReasonType::IndirectProof, n);
		stringstream ss;
		ss << s_mpd(n - 1) << a1i(n - 1, ruleHelper) << arg1;
		return ss.str();
	};
	// [17] (¬E-<n+1>) := (σ_mpd-<n>)²(D1)ⁿ<CNpCpO><#2><#1>:Ca₁…Caₙq, for 2 premises of schemas Ca₁…Caₙp,Ca₁…CaₙNp
	// [18] (¬E-<n+1>) := (σ_mpd-<n>)²(D1)ⁿ<CpCNpO><#1><#2>:Ca₁…Caₙq, for 2 premises of schemas Ca₁…Caₙp,Ca₁…CaₙNp
	auto rule_notE = [&](size_t n, const string& arg1, const string& arg2) -> string {
		if (debug)
			cout << "[CALL] (¬E-" << n << ")" << endl;
		size_t ruleVariant;
		string ruleHelper = getRuleHelper("notE", FFxExactProofReasonType::NegationElimination, n, &ruleVariant);
		stringstream ss;
		const string s_mpd_ = s_mpd(n - 1);
		ss << s_mpd_ << s_mpd_ << a1i(n - 1, ruleHelper);
		switch (ruleVariant) {
		case 17:
			ss << arg2 << arg1;
			break;
		case 18:
			ss << arg1 << arg2;
			break;
		default:
			throw logic_error("rule_notE(): ruleVariant == " + to_string(ruleVariant));
		}
		return ss.str();
	};
	// (¬I-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CCpONp><#1>:Ca₁…CaₙNp, for 1 premise of schema Ca₁…CaₙCpO
	auto rule_notI = [&](size_t n, const string& arg1) -> string {
		if (debug)
			cout << "[CALL] (¬I-" << n << ")" << endl;
		string ruleHelper = getRuleHelper("notI", FFxExactProofReasonType::NegationIntroduction, n);
		stringstream ss;
		ss << s_mpd(n - 1) << a1i(n - 1, ruleHelper) << arg1;
		return ss.str();
	};
	// (→E-<n+1>) := (mpd-<n>) = (σ_mpd-<n>)<#2><#1>:Ca₁…Caₙq, for 2 premises of schemas Ca₁…Caₙp,Ca₁…CaₙCpq
	auto rule_implyE = [&](size_t n, const string& arg1, const string& arg2) -> string {
		if (debug)
			cout << "[CALL] (→E-" << n << ")" << endl;
		if (!n)
			throw logic_error("Called rule_implyE(0, ...).");
		stringstream ss;
		ss << mpd(n - 1, arg1, arg2);
		return ss.str();
	};
	// (↔E-l-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CEpqCpq><#1>:Ca₁…CaₙCpq, for 1 premise of schema Ca₁…CaₙEpq
	// (↔E-r-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CEpqCqp><#1>:Ca₁…CaₙCqp, for 1 premise of schema Ca₁…CaₙEpq
	auto rule_equivE = [&](bool leftVariant, size_t n, const string& arg1) -> string {
		if (debug)
			cout << "[CALL] (↔E-" << (leftVariant ? "l-" : "r-") << n << ")" << endl;
		string ruleHelper = getRuleHelper("equivE", leftVariant ? FFxExactProofReasonType::BiconditionalElimination_l : FFxExactProofReasonType::BiconditionalElimination_r, n);
		stringstream ss;
		ss << s_mpd(n - 1) << a1i(n - 1, ruleHelper) << arg1;
		return ss.str();
	};
	// [12] (↔I-<n+1>) := (σ_mpd-<n>)²(D1)ⁿ<CCpqCCqpEpq><#1><#2>:Ca₁…CaₙEpq, for 2 premises of schemas Ca₁…CaₙCpq,Ca₁…CaₙCqp
	// [13] (↔I-<n+1>) := (σ_mpd-<n>)²(D1)ⁿ<CCpqCCqpEqp><#2><#1>:Ca₁…CaₙEpq, for 2 premises of schemas Ca₁…CaₙCpq,Ca₁…CaₙCqp
	auto rule_equivI = [&](size_t n, const string& arg1, const string& arg2) -> string {
		if (debug)
			cout << "[CALL] (↔I-" << n << ")" << endl;
		size_t ruleVariant;
		string ruleHelper = getRuleHelper("equivI", FFxExactProofReasonType::BiconditionalIntroduction, n, &ruleVariant);
		stringstream ss;
		const string s_mpd_ = s_mpd(n - 1);
		ss << s_mpd_ << s_mpd_ << a1i(n - 1, ruleHelper);
		switch (ruleVariant) {
		case 12:
			ss << arg1 << arg2;
			break;
		case 13:
			ss << arg2 << arg1;
			break;
		default:
			throw logic_error("rule_equivI(): ruleVariant == " + to_string(ruleVariant));
		}
		return ss.str();
	};
	// [ 6] (∨E-<n+1>) := (σ_mpd-<n>)³(D1)ⁿ<CApqCCprCCqrr><#1><#2><#3>:Ca₁…Caₙr, for 3 premises of schemas Ca₁…CaₙApq,Ca₁…CaₙCpr,Ca₁…CaₙCqr
	// [ 7] (∨E-<n+1>) := (σ_mpd-<n>)³(D1)ⁿ<CApqCCqrCCprr><#1><#3><#2>:Ca₁…Caₙr, for 3 premises of schemas Ca₁…CaₙApq,Ca₁…CaₙCpr,Ca₁…CaₙCqr
	// [ 8] (∨E-<n+1>) := (σ_mpd-<n>)³(D1)ⁿ<CCpqCAprCCrqq><#2><#1><#3>:Ca₁…Caₙr, for 3 premises of schemas Ca₁…CaₙApq,Ca₁…CaₙCpr,Ca₁…CaₙCqr
	// [ 9] (∨E-<n+1>) := (σ_mpd-<n>)³(D1)ⁿ<CCpqCCrqCAprq><#2><#3><#1>:Ca₁…Caₙr, for 3 premises of schemas Ca₁…CaₙApq,Ca₁…CaₙCpr,Ca₁…CaₙCqr
	// [10] (∨E-<n+1>) := (σ_mpd-<n>)³(D1)ⁿ<CCpqCArpCCrqq><#3><#1><#2>:Ca₁…Caₙr, for 3 premises of schemas Ca₁…CaₙApq,Ca₁…CaₙCpr,Ca₁…CaₙCqr
	// [11] (∨E-<n+1>) := (σ_mpd-<n>)³(D1)ⁿ<CCpqCCrqCArpq><#3><#2><#1>:Ca₁…Caₙr, for 3 premises of schemas Ca₁…CaₙApq,Ca₁…CaₙCpr,Ca₁…CaₙCqr
	auto rule_orE = [&](size_t n, const string& arg1, const string& arg2, const string& arg3) -> string {
		if (debug)
			cout << "[CALL] (∨E-" << n << ")" << endl;
		size_t ruleVariant;
		string ruleHelper = getRuleHelper("orE", FFxExactProofReasonType::DisjunctionElimination, n, &ruleVariant);
		stringstream ss;
		const string s_mpd_ = s_mpd(n - 1);
		ss << s_mpd_ << s_mpd_ << s_mpd_ << a1i(n - 1, ruleHelper);
		switch (ruleVariant) {
		case 6:
			ss << arg1 << arg2 << arg3;
			break;
		case 7:
			ss << arg1 << arg3 << arg2;
			break;
		case 8:
			ss << arg2 << arg1 << arg3;
			break;
		case 9:
			ss << arg2 << arg3 << arg1;
			break;
		case 10:
			ss << arg3 << arg1 << arg2;
			break;
		case 11:
			ss << arg3 << arg2 << arg1;
			break;
		default:
			throw logic_error("rule_orE(): ruleVariant == " + to_string(ruleVariant));
		}
		return ss.str();
	};
	// (∨I-l-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CpApq><#1>:Ca₁…CaₙCNpq, for 1 premise of schema Ca₁…Caₙp
	// (∨I-r-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CpAqp><#1>:Ca₁…CaₙCNqp, for 1 premise of schema Ca₁…Caₙp
	auto rule_orI = [&](bool leftVariant, size_t n, const string& arg1) -> string {
		if (debug)
			cout << "[CALL] (∨I-" << (leftVariant ? "l-" : "r-") << n << ")" << endl;
		string ruleHelper = getRuleHelper("orI", leftVariant ? FFxExactProofReasonType::DisjunctionIntroduction_l : FFxExactProofReasonType::DisjunctionIntroduction_r, n);
		stringstream ss;
		ss << s_mpd(n - 1) << a1i(n - 1, ruleHelper) << arg1;
		return ss.str();
	};
	// (∧E-l-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CKpqp><#1>:Ca₁…Caₙp, for 1 premise of schema Ca₁…CaₙKpq
	// (∧E-r-<n+1>) := (σ_mpd-<n>)(D1)ⁿ<CKpqq><#1>:Ca₁…Caₙq, for 1 premise of schema Ca₁…CaₙKpq
	auto rule_andE = [&](bool leftVariant, size_t n, const string& arg1) -> string {
		if (debug)
			cout << "[CALL] (∧E-" << (leftVariant ? "l-" : "r-") << n << ")" << endl;
		string ruleHelper = getRuleHelper("andE", leftVariant ? FFxExactProofReasonType::ConjunctionElimination_l : FFxExactProofReasonType::ConjunctionElimination_r, n);
		stringstream ss;
		ss << s_mpd(n - 1) << a1i(n - 1, ruleHelper) << arg1;
		return ss.str();
	};
	// [0] (∧I-<n+1>) := (σ_mpd-<n>)²(D1)ⁿ<CpCqKpq><#1><#2>:Ca₁…CaₙKpq, for 2 premises of schemas Ca₁…Caₙp,Ca₁…Caₙq
	// [1] (∧I-<n+1>) := (σ_mpd-<n>)²(D1)ⁿ<CpCqKqp><#2><#1>:Ca₁…CaₙKpq, for 2 premises of schemas Ca₁…Caₙp,Ca₁…Caₙq
	auto rule_andI = [&](size_t n, const string& arg1, const string& arg2) -> string {
		if (debug)
			cout << "[CALL] (∧I-" << n << ")" << endl;
		size_t ruleVariant;
		string ruleHelper = getRuleHelper("andI", FFxExactProofReasonType::ConjunctionIntroduction, n, &ruleVariant);
		stringstream ss;
		const string s_mpd_ = s_mpd(n - 1);
		ss << s_mpd_ << s_mpd_ << a1i(n - 1, ruleHelper);
		switch (ruleVariant) {
		case 0:
			ss << arg1 << arg2;
			break;
		case 1:
			ss << arg2 << arg1;
			break;
		default:
			throw logic_error("rule_andI(): ruleVariant == " + to_string(ruleVariant));
		}
		return ss.str();
	};
#if 0 // TEST
	for (size_t i = 1; i < 5; i++)
		cout << "(a1-" << i << ") = " << a1(i) << endl;
	for (size_t i = 0; i < 5; i++)
		cout << "(a1i-" << i << ") = " << a1i(i, "<#1>") << endl;
	for (size_t i = 0; i < 5; i++)
		for (size_t j = 0; j < 4; j++)
			cout << "(a1-" << i << "-a1i-" << j << ") = " << a1_a1i(i, j) << endl;
	for (size_t i = 0; i < 5; i++)
		cout << "(mpd-" << i << ") = " << mpd(i, "<#1>", "<#2>") << endl;
	for (size_t i = 0; i < 5; i++)
		for (size_t j = 0; j < 5; j++)
			cout << "(slip-" << i << "-" << j << ") = " << slip(i, j, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(IP-" << i << ") = " << rule_IP(i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(¬E-" << i << ") = " << rule_notE(i, "<#1>", "<#2>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(¬I-" << i << ") = " << rule_notI(i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(↔E-l-" << i << ") = " << rule_equivE(true, i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(↔E-r-" << i << ") = " << rule_equivE(false, i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(↔I-" << i << ") = " << rule_equivI(i, "<#1>", "<#2>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(∨E-" << i << ") = " << rule_orE(i, "<#1>", "<#2>", "<#3>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(∨I-l-" << i << ") = " << rule_orI(true, i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(∨I-r-" << i << ") = " << rule_orI(false, i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(∧E-l-" << i << ") = " << rule_andE(true, i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(∧E-r-" << i << ") = " << rule_andE(false, i, "<#1>") << endl;
	for (size_t i = 1; i < 5; i++)
		cout << "(∧I-" << i << ") = " << rule_andI(i, "<#1>", "<#2>") << endl;
#endif

	// 9. Construct D-proof from ND-proof.
	shared_ptr<DlFormula> f_bot = make_shared<DlFormula>(make_shared<String>(DlCore::terminalStr_bot()));
	const NdParser::FFxProofLine& finalNdProofLine = ndProof.lineAt(ndProof.size());
	shared_ptr<DlFormula> targetTheorem = pure ? DlCore::toBasicDlFormula(finalNdProofLine.formula, nullptr, nullptr, nullptr, false) : finalNdProofLine.formula;
	if (debug)
		cout << "To prove: " << DlCore::toPolishNotation(targetTheorem) << ", i.e. " << DlCore::formulaRepresentation_traverse(targetTheorem) << endl;
	auto translateNdProof = [&](const NdParser::FFxProofLine& line, size_t targetDepth, const auto& me) -> string {
		const size_t myDepth = line.depth;
		auto callLine = [&](const NdParser::FFxProofLine& nextLine) -> string {
			const size_t nextDepth = nextLine.depth; // this is also the number of known antecedents
			if (nextLine.reason.type != NdParser::FFxProofReasonType::Assumption && myDepth > nextDepth) { // caller is up higher than non-trivial callee
				string s = me(nextLine, nextDepth, me); // prepare from callee's perspective
				return slip(nextDepth, targetDepth - nextDepth, s); // slip in 'targetDepth - nextDepth' new antecedents after 'nextDepth' known antecedents for a known conclusion
			} else
				return me(nextLine, targetDepth, me);
		};
		const size_t depthDiff = targetDepth - myDepth;
		auto callBlock = [&](const NdParser::FFxProofLine& nextLine) -> string {
			// Eliminates block => only references from the block's immediate container are allowed ; Act like depth was 1 higher (to introduce antecedent for eliminated assumption).
			return me(nextLine, myDepth + 1, me);
		};
		const shared_ptr<DlFormula>& f = line.formula;
		const vector<shared_ptr<DlFormula>>& f_children = f->getChildren();
		const NdParser::FFxProofReason& r = line.reason;
		const vector<size_t>& metadata = r.metadata;
		switch (r.type) {
		case NdParser::FFxProofReasonType::Assumption:
			return a1_a1i(depthDiff, myDepth - 1);
		case NdParser::FFxProofReasonType::IndirectProof: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			const vector<shared_ptr<DlFormula>>& f0_children = f0->getChildren();
			if (f0->getValue()->value != DlCore::terminalStr_not() || f0_children.size() != 1 || *f != *f0_children[0] || *f1 != *f_bot)
				throw invalid_argument("NdConverter(): Invalid reason 'IP  " + to_string(metadata[0]) + "-" + to_string(metadata[1]) + "'.");
			return rule_IP(targetDepth + 1, callBlock(ndProof.lineAt(metadata[1])));
		}
		case NdParser::FFxProofReasonType::NegationIntroduction: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			if (f->getValue()->value != DlCore::terminalStr_not() || f_children.size() != 1 || *f0 != *f_children[0] || *f1 != *f_bot)
				throw invalid_argument("NdConverter(): Invalid reason '~I  " + to_string(metadata[0]) + "-" + to_string(metadata[1]) + "'.");
			return rule_notI(targetDepth + 1, callBlock(ndProof.lineAt(metadata[1])));
		}
		case NdParser::FFxProofReasonType::NegationElimination: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			const vector<shared_ptr<DlFormula>>& f0_children = f0->getChildren();
			const vector<shared_ptr<DlFormula>>& f1_children = f1->getChildren();
			bool firstNegated;
			if (*f != *f_bot || ((firstNegated = (f1->getValue()->value != DlCore::terminalStr_not() || f1_children.size() != 1 || *f1_children[0] != *f0)) && (f0->getValue()->value != DlCore::terminalStr_not() || f0_children.size() != 1 || *f0_children[0] != *f1)))
				throw invalid_argument("NdConverter(): Invalid reason '~E  " + to_string(metadata[0]) + "," + to_string(metadata[1]) + "'.");
			return rule_notE(targetDepth + 1, callLine(ndProof.lineAt(metadata[firstNegated ? 1 : 0])), callLine(ndProof.lineAt(metadata[firstNegated ? 0 : 1])));
		}
		case NdParser::FFxProofReasonType::ConditionalIntroduction:
			if (f->getValue()->value != DlCore::terminalStr_imply() || f_children.size() != 2 || *ndProof.formulaAt(metadata[0]) != *f_children[0] || *ndProof.formulaAt(metadata[1]) != *f_children[1])
				throw invalid_argument("NdConverter(): Invalid reason '>I  " + to_string(metadata[0]) + "-" + to_string(metadata[1]) + "'.");
			return callBlock(ndProof.lineAt(metadata[1]));
		case NdParser::FFxProofReasonType::ConditionalElimination: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			const vector<shared_ptr<DlFormula>>& f0_children = f0->getChildren();
			const vector<shared_ptr<DlFormula>>& f1_children = f1->getChildren();
			bool firstIsConditional;
			if ((firstIsConditional = (f1->getValue()->value != DlCore::terminalStr_imply() || f1_children.size() != 2 || *f1_children[0] != *f0 || *f1_children[1] != *f)) && (f0->getValue()->value != DlCore::terminalStr_imply() || f0_children.size() != 2 || *f0_children[0] != *f1 || *f0_children[1] != *f))
				throw invalid_argument("NdConverter(): Invalid reason '>E  " + to_string(metadata[0]) + "," + to_string(metadata[1]) + "'.");
			return rule_implyE(targetDepth + 1, callLine(ndProof.lineAt(metadata[firstIsConditional ? 1 : 0])), callLine(ndProof.lineAt(metadata[firstIsConditional ? 0 : 1])));
		}
		case NdParser::FFxProofReasonType::ConjunctionIntroduction: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			bool firstIsLeft;
			if (f->getValue()->value != DlCore::terminalStr_and() || f_children.size() != 2 || ((firstIsLeft = (*f_children[0] != *f1 || *f_children[1] != *f0)) && (*f_children[0] != *f0 || *f_children[1] != *f1)))
				throw invalid_argument("NdConverter(): Invalid reason '&I  " + to_string(metadata[0]) + "," + to_string(metadata[1]) + "'.");
			return rule_andI(targetDepth + 1, callLine(ndProof.lineAt(metadata[firstIsLeft ? 0 : 1])), callLine(ndProof.lineAt(metadata[firstIsLeft ? 1 : 0])));
		}
		case NdParser::FFxProofReasonType::ConjunctionElimination: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const vector<shared_ptr<DlFormula>>& f0_children = f0->getChildren();
			bool firstIsOutput;
			if (f0->getValue()->value != DlCore::terminalStr_and() || f0_children.size() != 2 || ((firstIsOutput = *f0_children[1] != *f) && *f0_children[0] != *f))
				throw invalid_argument("NdConverter(): Invalid reason '&E  " + to_string(metadata[0]) + "'.");
			return rule_andE(firstIsOutput, targetDepth + 1, callLine(ndProof.lineAt(metadata[0])));
		}
		case NdParser::FFxProofReasonType::DisjunctionIntroduction: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			bool firstIsInput;
			if (f->getValue()->value != DlCore::terminalStr_or() || f_children.size() != 2 || ((firstIsInput = *f_children[1] != *f0) && *f_children[0] != *f0))
				throw invalid_argument("NdConverter(): Invalid reason 'vI  " + to_string(metadata[0]) + "'.");
			return rule_orI(firstIsInput, targetDepth + 1, callLine(ndProof.lineAt(metadata[0])));
		}
		case NdParser::FFxProofReasonType::DisjunctionElimination: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			const shared_ptr<DlFormula>& f2 = ndProof.formulaAt(metadata[2]);
			const shared_ptr<DlFormula>& f3 = ndProof.formulaAt(metadata[3]);
			const shared_ptr<DlFormula>& f4 = ndProof.formulaAt(metadata[4]);
			const vector<shared_ptr<DlFormula>>& f0_children = f0->getChildren();
			bool firstIsLeft;
			if (f0->getValue()->value != DlCore::terminalStr_or() || f0_children.size() != 2 || *f != *f2 || *f != *f4 || ((firstIsLeft = (*f0_children[0] != *f3 || *f0_children[1] != *f1)) && (*f0_children[0] != *f1 || *f0_children[1] != *f3)))
				throw invalid_argument("NdConverter(): Invalid reason 'vE  " + to_string(metadata[0]) + "," + to_string(metadata[1]) + "-" + to_string(metadata[2]) + "," + to_string(metadata[3]) + "-" + to_string(metadata[4]) + "'.");
			return rule_orE(targetDepth + 1, callLine(ndProof.lineAt(metadata[0])), callBlock(ndProof.lineAt(metadata[firstIsLeft ? 2 : 4])), callBlock(ndProof.lineAt(metadata[firstIsLeft ? 4 : 2])));
		}
		case NdParser::FFxProofReasonType::BiconditionalIntroduction: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			const shared_ptr<DlFormula>& f2 = ndProof.formulaAt(metadata[2]);
			const shared_ptr<DlFormula>& f3 = ndProof.formulaAt(metadata[3]);
			bool firstIsLeft;
			if (f->getValue()->value != DlCore::terminalStr_equiv() || f_children.size() != 2 || *f0 != *f3 || *f1 != *f2 || ((firstIsLeft = (*f_children[0] != *f1 || *f_children[1] != *f0)) && (*f_children[0] != *f0 || *f_children[1] != *f1)))
				throw invalid_argument("NdConverter(): Invalid reason '<>I  " + to_string(metadata[0]) + "-" + to_string(metadata[1]) + "," + to_string(metadata[2]) + "-" + to_string(metadata[3]) + "'.");
			return rule_equivI(targetDepth + 1, callBlock(ndProof.lineAt(metadata[firstIsLeft ? 1 : 3])), callBlock(ndProof.lineAt(metadata[firstIsLeft ? 3 : 1])));
		}
		case NdParser::FFxProofReasonType::BiconditionalElimination: {
			const shared_ptr<DlFormula>& f0 = ndProof.formulaAt(metadata[0]);
			const shared_ptr<DlFormula>& f1 = ndProof.formulaAt(metadata[1]);
			const vector<shared_ptr<DlFormula>>& f0_children = f0->getChildren();
			const vector<shared_ptr<DlFormula>>& f1_children = f1->getChildren();
			bool firstIsBiconditional;
			bool implyToRight = true;
			if ((firstIsBiconditional = (f1->getValue()->value != DlCore::terminalStr_equiv() || f1_children.size() != 2 || *f1_children[0] != *f0 || *f1_children[1] != *f)) && (f0->getValue()->value != DlCore::terminalStr_equiv() || f0_children.size() != 2 || *f0_children[0] != *f1 || *f0_children[1] != *f)) {
				implyToRight = false;
				if ((firstIsBiconditional = (f1->getValue()->value != DlCore::terminalStr_equiv() || f1_children.size() != 2 || *f1_children[1] != *f0 || *f1_children[0] != *f)) && (f0->getValue()->value != DlCore::terminalStr_equiv() || f0_children.size() != 2 || *f0_children[1] != *f1 || *f0_children[0] != *f))
					throw invalid_argument("NdConverter(): Invalid reason '<>E  " + to_string(metadata[0]) + "," + to_string(metadata[1]) + "'.");
			}
			if (!firstIsBiconditional) // according to original FitchFX implementation
				throw logic_error("NdConverter(): Invalid reason '<>E  " + to_string(metadata[0]) + "," + to_string(metadata[1]) + "': The formula on the first rule line must be the biconditional.");
			return rule_implyE(targetDepth + 1, callLine(ndProof.lineAt(metadata[firstIsBiconditional ? 1 : 0])), rule_equivE(implyToRight, targetDepth + 1, callLine(ndProof.lineAt(metadata[firstIsBiconditional ? 0 : 1]))));
		}
		case NdParser::FFxProofReasonType::Reiteration: {
			return callLine(ndProof.lineAt(metadata[0]));
		}
		default:
			throw logic_error("r.type == " + to_string(static_cast<unsigned>(r.type)));
		}
	};
	long double dur_translate = 0;
	if (debug)
		startTime = chrono::steady_clock::now();
	string translatedProof = translateNdProof(finalNdProofLine, 0, translateNdProof);
	if (debug)
		dur_translate = static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0;
	size_t resultIndex = abstractDProof.size();
	vector<string> abstractDProof_test = abstractDProof;
	abstractDProof_test.push_back(translatedProof);
	vector<shared_ptr<DlFormula>> conclusions_test;
	vector<string> helperRules_test;
	vector<shared_ptr<DlFormula>> helperRulesConclusions_test;
	DRuleParser::parseAbstractDProof(abstractDProof_test, conclusions_test, &targetAxioms, &helperRules_test, &helperRulesConclusions_test, nullptr, debug);
	size_t resultFunLen = DRuleParser::measureFundamentalLengthsInAbstractDProof( { resultIndex }, abstractDProof_test, conclusions_test, helperRules_test, helperRulesConclusions_test)[resultIndex];
	if (debug)
		cout << "Translation resulted in D-proof of fundamental length " << resultFunLen << " after " << FctHelper::round(dur_translate, 2) << " ms." << endl;
	string resultingConclusion_PN = DlCore::toPolishNotation(conclusions_test.back());
	cout << "Resulting conclusion is " << resultingConclusion_PN << ", i.e. " << DlCore::formulaRepresentation_traverse(conclusions_test.back()) << "." << endl;
	map<string, shared_ptr<DlFormula>> substitutions;
	if (!DlCore::isSchemaOf(conclusions_test.back(), targetTheorem, &substitutions))
		throw logic_error("NdConverter(): The resulting conclusion is not a schema of " + DlCore::formulaRepresentation_traverse(targetTheorem) + ".");
	cout << "Proved " + DlCore::formulaRepresentation_traverse(targetTheorem) + " via " << DlCore::substitutionRepresentation_traverse(substitutions) << "." << endl;

	// 10. Compose and print proof summary.
	abstractDProof.push_back(translatedProof);
	conclusions.push_back(conclusions_test.back());
	vector<DRuleParser::AxiomInfo> filterForTheorems = { DRuleParser::AxiomInfo(resultingConclusion_PN, conclusions_test.back()) };
	abstractDProof = DRuleParser::recombineAbstractDProof(abstractDProof, conclusions, &targetAxioms, targetEverything, targetEverything ? nullptr : &filterForTheorems, nullptr, targetEverything ? 1 : 2, nullptr, debug, SIZE_MAX - (targetEverything ? 0 : 1), true, SIZE_MAX, SIZE_MAX, true, false, 0, false, nullptr, false, false, false, !debug);
	if (debug)
		startTime = chrono::steady_clock::now();
	if (optIn_outputFile) { // Not using FctHelper::writeToFile() in order to write huge files without huge string acquisition.
		filesystem::path file = filesystem::u8path(*optIn_outputFile);
		while (!filesystem::exists(file) && !FctHelper::ensureDirExists(file.string()))
			cerr << "Failed to create file at \"" << file.string() << "\", trying again." << endl;
		string::size_type bytes;
		{
			ofstream fout(file, fstream::out | fstream::binary);
			bytes = DlProofEnumerator::printProofSummary(fout, targetAxioms, abstractDProof, conclusions, normalPolishNotation, printInfixUnicode);
		}
		if (debug)
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << bytes << " bytes to " << file.string() << "." << endl;
	} else {
		string::size_type bytes = DlProofEnumerator::printProofSummary(cout, targetAxioms, abstractDProof, conclusions, normalPolishNotation, printInfixUnicode);
		cout << flush;
		if (debug)
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print " << bytes << " bytes." << endl;
	}
}

}
}
