#include "DRuleParser.h"

#include "../helper/FctHelper.h"
#include "../tree/TreeNode.h"
#include "../logic/DlCore.h"
#include "../logic/DlFormula.h"

#include <boost/algorithm/string.hpp>

#include <tbb/parallel_for_each.h>

#include <iostream>
#include <numeric>

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::tree;
using namespace xamidi::logic;

namespace xamidi {
namespace metamath {

vector<string> DRuleParser::readFromMmsolitaireFile(const string& file, vector<string>* optOut_dProofNamesInFile, bool debug) {
	vector<string> dProofsInFile;
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	string s;
	if (!FctHelper::readFile(file, s))
		throw invalid_argument("DRuleParser(): Could not read file \"" + file + "\".");
	string::size_type index = s.find(';');
	if (index == string::npos)
		throw invalid_argument("DRuleParser(): Could not find ';' in file \"" + file + "\".");
	index = s.rfind('\n', index);
	if (index != string::npos)
		s = s.substr(index); // skip comment section

	string temp;
	stringstream ss(s);
	string dProofName;
	string dProof;
	bool readingName = true;
	bool skippingResult = false;
	bool eof = ss.eof();
	while (getline(ss, temp) || !eof) { // read every line, _including_ the last line
		if (readingName) {
			dProofName += temp;
			if (temp.find(';') != string::npos) { // usually "; ! <reference name>"
				readingName = false;
				skippingResult = true;
			}
		} else if (skippingResult) {
			if (temp.find(';') != string::npos) // usually "; ! Result of proof"
				skippingResult = false;
		} else if (temp.empty()) { // read actual D-proof
			readingName = true; // done reading D-proof
			index = dProof.rfind(';');
			if (index == string::npos)
				throw invalid_argument("DRuleParser(): Could not find ';' after D-proof '" + dProofName + "'.");
			if (optOut_dProofNamesInFile)
				optOut_dProofNamesInFile->push_back(dProofName);
			dProofsInFile.push_back(dProof.substr(0, index));
			dProofName.clear();
			dProof.clear();
		} else
			dProof += temp;
		eof = ss.eof();
	}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to read " << dProofsInFile.size() << " condensed detachment proof" << (dProofsInFile.size() == 1 ? "" : "s") << " from file \"" << file << "\"." << endl;
	//#size_t i = 0; cout << "D-proofs: " << FctHelper::vectorStringF(dProofsInFile, [&](const string& s) { return (optOut_dProofNamesInFile ? (*optOut_dProofNamesInFile)[i++] + ": " : "") + s; }, "{\n\t", "\n}", "\n\t") << endl;
	return dProofsInFile;
}

map<size_t, set<string>> DRuleParser::prepareDProofsByLength(const string& file, const vector<AxiomInfo>* customAxioms, unsigned minUseAmountToCreateHelperProof, vector<string>* optOut_dProofsInFile, vector<string>* optOut_dProofNamesInFile, bool debug) {
	vector<string> dProofsInFile = readFromMmsolitaireFile(file, optOut_dProofNamesInFile, debug);
	map<size_t, set<string>> knownDProofsByLength;
	parseDProofs_raw(dProofsInFile, customAxioms, minUseAmountToCreateHelperProof, &knownDProofsByLength, debug, false, true, true);
	if (optOut_dProofsInFile)
		*optOut_dProofsInFile = dProofsInFile;
	return knownDProofsByLength;
}

void DRuleParser::modifyingSubstitute(shared_ptr<DlFormula>& formula, const map<string, shared_ptr<DlFormula>>& substitutions, unordered_set<shared_ptr<DlFormula>>* alreadyModified) {
	if (alreadyModified)
		_modifyingSubstitute(formula, substitutions, *alreadyModified);
	else {
		unordered_set<shared_ptr<DlFormula>> myAlreadyModified;
		_modifyingSubstitute(formula, substitutions, myAlreadyModified);
	}
}

void DRuleParser::_modifyingSubstitute(shared_ptr<DlFormula>& formula, const map<string, shared_ptr<DlFormula>>& substitutions, unordered_set<shared_ptr<DlFormula>>& alreadyModified) {
	if (formula->getChildren().empty()) { // Substitutions can only happen in leaves.
		map<string, shared_ptr<DlFormula>>::const_iterator searchResult = substitutions.find(formula->getValue()->value);
		if (searchResult != substitutions.end())
			formula = searchResult->second; // modify formula (which is a primitive)
	} else if (alreadyModified.emplace(formula).second) // Children not already handled? (Avoid to substitute multiple times on the same subtrees.)
		for (shared_ptr<DlFormula>& subformula : formula->children())
			_modifyingSubstitute(subformula, substitutions, alreadyModified);
}

const shared_ptr<String>& DRuleParser::_and() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_and());
	return _;
}
const shared_ptr<String>& DRuleParser::_or() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_or());
	return _;
}
const shared_ptr<String>& DRuleParser::_nand() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_nand());
	return _;
}
const shared_ptr<String>& DRuleParser::_nor() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_nor());
	return _;
}
const shared_ptr<String>& DRuleParser::_imply() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_imply());
	return _;
}
const shared_ptr<String>& DRuleParser::_implied() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_implied());
	return _;
}
const shared_ptr<String>& DRuleParser::_nimply() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_nimply());
	return _;
}
const shared_ptr<String>& DRuleParser::_nimplied() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_nimplied());
	return _;
}
const shared_ptr<String>& DRuleParser::_equiv() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_equiv());
	return _;
}
const shared_ptr<String>& DRuleParser::_xor() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_xor());
	return _;
}
const shared_ptr<String>& DRuleParser::_com() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_com());
	return _;
}
const shared_ptr<String>& DRuleParser::_app() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_app());
	return _;
}
const shared_ptr<String>& DRuleParser::_not() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_not());
	return _;
}
const shared_ptr<String>& DRuleParser::_nece() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_nece());
	return _;
}
const shared_ptr<String>& DRuleParser::_poss() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_poss());
	return _;
}
const shared_ptr<String>& DRuleParser::_obli() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_obli());
	return _;
}
const shared_ptr<String>& DRuleParser::_perm() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_perm());
	return _;
}
const shared_ptr<String>& DRuleParser::_top() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_top());
	return _;
}
const shared_ptr<String>& DRuleParser::_bot() {
	static const shared_ptr<String> _ = make_shared<String>(DlCore::terminalStr_bot());
	return _;
}

DRuleParser::AxiomInfo::AxiomInfo(const string& name, const shared_ptr<DlFormula>& axiom) :
		AxiomInfo(_refineAxiom(name, axiom)) {
}

DRuleParser::AxiomInfo& DRuleParser::AxiomInfo::operator=(const AxiomInfo& other) {
	refinedAxiom = other.refinedAxiom->cloneSharedPtr();
	primitivesCount = other.primitivesCount;
	name = other.name;
	return *this;
}

DRuleParser::AxiomInfo::AxiomInfo(const tuple<shared_ptr<DlFormula>, unsigned, string>& refinedData) :
		refinedAxiom(get<0>(refinedData)), primitivesCount(get<1>(refinedData)), name(get<2>(refinedData)) {
}

tuple<shared_ptr<DlFormula>, unsigned, string> DRuleParser::AxiomInfo::_refineAxiom(const string& name, const shared_ptr<DlFormula>& axiom) {
	vector<string> primitives = DlCore::primitivesOfFormula_ordered(axiom);
	map<string, shared_ptr<DlFormula>> substitutions;
	unsigned primitivesIndex = 0;
	for (const string& s : primitives)
		substitutions.emplace(s, make_shared<DlFormula>(make_shared<String>(to_string(primitivesIndex++))));
	// Basically does what DlCore::substitute() would do, but additionally primitives are assigned to a new unique reference, non-primitives use built-in symbols, and does not copy meanings.
	auto substitute_withUniquePrimitivesAndUseBuiltinSymbols = [&](const shared_ptr<DlFormula>& formula) {
		auto recurse = [&](shared_ptr<DlFormula>& destinationNode, const shared_ptr<DlFormula>& formula, const auto& me) -> void {
			const string& value = formula->getValue()->value;
			if (formula->getChildren().empty()) { // Substitutions can only happen in leaves.
				map<string, shared_ptr<DlFormula>>::const_iterator searchResult = substitutions.find(value);
				if (searchResult != substitutions.end())
					destinationNode = searchResult->second; // substitute by using the newly created primitive pointer (so that all occurrences of just one primitive point to the same formula)
				else if (value == DlCore::terminalStr_top())
					destinationNode->value() = _top(); // use built-in symbol pointer
				else if (value == DlCore::terminalStr_bot())
					destinationNode->value() = _bot(); // use built-in symbol pointer
				else
					throw domain_error("DRuleParser::AxiomInfo::refineAxiom(): Unknown operator \"" + value + "\".");
			} else {
				for (const shared_ptr<DlFormula>& subformula : formula->getChildren()) {
					shared_ptr<DlFormula> childNode = make_shared<DlFormula>(make_shared<String>());
					me(childNode, subformula, me);
					destinationNode->addChild(childNode); // NOTE: Must add child after recursive call, since it might be overwritten (in case it is a primitive).
				}
				// use built-in symbol pointer
				if (value == DlCore::terminalStr_and())
					destinationNode->value() = _and();
				else if (value == DlCore::terminalStr_or())
					destinationNode->value() = _or();
				else if (value == DlCore::terminalStr_nand())
					destinationNode->value() = _nand();
				else if (value == DlCore::terminalStr_nor())
					destinationNode->value() = _nor();
				else if (value == DlCore::terminalStr_imply())
					destinationNode->value() = _imply();
				else if (value == DlCore::terminalStr_implied())
					destinationNode->value() = _implied();
				else if (value == DlCore::terminalStr_nimply())
					destinationNode->value() = _nimply();
				else if (value == DlCore::terminalStr_nimplied())
					destinationNode->value() = _nimplied();
				else if (value == DlCore::terminalStr_equiv())
					destinationNode->value() = _equiv();
				else if (value == DlCore::terminalStr_xor())
					destinationNode->value() = _xor();
				else if (value == DlCore::terminalStr_com())
					destinationNode->value() = _com();
				else if (value == DlCore::terminalStr_app())
					destinationNode->value() = _app();
				else if (value == DlCore::terminalStr_not())
					destinationNode->value() = _not();
				else if (value == DlCore::terminalStr_nece())
					destinationNode->value() = _nece();
				else if (value == DlCore::terminalStr_poss())
					destinationNode->value() = _poss();
				else if (value == DlCore::terminalStr_obli())
					destinationNode->value() = _obli();
				else if (value == DlCore::terminalStr_perm())
					destinationNode->value() = _perm();
				else
					throw domain_error("DRuleParser::AxiomInfo::refineAxiom(): Unknown operator \"" + value + "\".");
			}
		};
		shared_ptr<DlFormula> rootNode = make_shared<DlFormula>(make_shared<String>());
		recurse(rootNode, formula, recurse);
		return rootNode;
	};
	return tuple<shared_ptr<DlFormula>, unsigned, string>(substitute_withUniquePrimitivesAndUseBuiltinSymbols(axiom), substitutions.size(), name);
}

shared_ptr<DlFormula> DRuleParser::_ax(unsigned axiomIndex, const vector<shared_ptr<DlFormula>>& primitives, const vector<AxiomInfo>& axioms) {
	// Basically does what DlFormula::cloneSharedPtr() would do, but additionally primitives are assigned to a new unique reference, and does not copy meanings.
	// NOTE: We want the same primitives for equal strings, which is accomplished by 'axioms[·].refinedAxiom' containing only one formula for each primitive symbol.
	//       Extremely fast, since primitives are simply addressed by a counting index in 'primitives' (i.e. no string lookup and no extra (hash) map is required).
	unsigned primitivesIndex = 0;
	auto cloneSharedPtr_withRefinedPrimitives = [&](const shared_ptr<DlFormula>& node, DlFormula::CloneMap& knownClones, const auto& me) -> shared_ptr<DlFormula> {
		DlFormula::CloneMap::iterator searchResult = knownClones.find(static_cast<const DlFormula*>(node.get()));
		if (searchResult != knownClones.end()) {
			const shared_ptr<DlFormula>& knownCloneEntry = searchResult->second;
			if (knownCloneEntry)
				return knownCloneEntry; // We can return the known clone itself (by reference).
		}
		const vector<shared_ptr<DlFormula>>& children = node->getChildren();
		const string& value = node->getValue()->value;
		if (!children.empty() || value == DlCore::terminalStr_top() || value == DlCore::terminalStr_bot()) {
			shared_ptr<DlFormula> clone = make_shared<DlFormula>(node->getValue());
			for (const shared_ptr<DlFormula>& child : children)
				clone->addChild(child ? me(child, knownClones, me) : nullptr);
			knownClones[static_cast<const DlFormula*>(node.get())] = clone; // Remember the shared address of the clone (for referencing).
			return clone;
		} else { // at a primitive that was not already registered (since 'axioms[·].refinedAxiom' and thereby 'node' does not contain the same primitive value in two different nodes)
			//#if (primitivesIndex >= primitives.size())
			//#	throw logic_error("DRuleParser::_ax(): primitivesIndex = " + to_string(primitivesIndex) + " >= |primitives| = " + to_string(primitives.size()) + ". (" + to_string(axiomIndex + 1) + "): " + DlCore::formulaRepresentation_traverse(axioms[axiomIndex].refinedAxiom));
			const shared_ptr<DlFormula>& primitive = primitives[primitivesIndex++];
			knownClones[static_cast<const DlFormula*>(node.get())] = primitive; // Remember the shared address of the primitive (for referencing).
			return primitive;
		}
	};
	DlFormula::CloneMap cloneMap;
	return cloneSharedPtr_withRefinedPrimitives(axioms[axiomIndex].refinedAxiom, cloneMap, cloneSharedPtr_withRefinedPrimitives); // partial cloning
}

shared_ptr<DlFormula> DRuleParser::_ax1(const shared_ptr<DlFormula>& psi, const shared_ptr<DlFormula>& phi) {
	return make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
		psi,
		make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
			phi,
			psi
		})
	});
}

shared_ptr<DlFormula> DRuleParser::_ax2(const shared_ptr<DlFormula>& psi, const shared_ptr<DlFormula>& phi, const shared_ptr<DlFormula>& chi) {
	return make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
		make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
			psi,
			make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
				phi,
				chi
			})
		}),
		make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
			make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
				psi,
				phi
			}),
			make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
				psi,
				chi
			})
		})
	});
}

shared_ptr<DlFormula> DRuleParser::_ax3(const shared_ptr<DlFormula>& psi, const shared_ptr<DlFormula>& phi) {
	return make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
		make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
			make_shared<DlFormula>(_not(), vector<shared_ptr<DlFormula>> {
				phi
			}),
			make_shared<DlFormula>(_not(), vector<shared_ptr<DlFormula>> {
				psi
			})
		}),
		make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> {
			psi,
			phi
		})
	});
}

vector<DProofInfo> DRuleParser::parseDProof_raw(const string& dProof, const vector<AxiomInfo>* customAxioms, unsigned minUseAmountToCreateHelperProof, bool debug, bool calculateMeanings, bool exceptionOnUnificationFailure, bool reversedAbstractProofStrings) {
	return parseDProofs_raw( { dProof }, customAxioms, minUseAmountToCreateHelperProof, nullptr, debug, calculateMeanings, exceptionOnUnificationFailure, false, reversedAbstractProofStrings);
}

vector<DProofInfo> DRuleParser::parseDProof_raw_permissive(const string& dProof, const vector<AxiomInfo>* customAxioms, unsigned minUseAmountToCreateHelperProof, bool debug, bool calculateMeanings, bool reversedAbstractProofStrings) {
	return parseDProof_raw(dProof, customAxioms, minUseAmountToCreateHelperProof, debug, calculateMeanings, false, reversedAbstractProofStrings);
}

vector<DProofInfo> DRuleParser::parseDProofs_raw(const vector<string>& dProofs, const vector<AxiomInfo>* customAxioms, unsigned minUseAmountToCreateHelperProof, map<size_t, set<string>>* optOut_knownDProofsByLength, bool debug, bool calculateMeanings, bool exceptionOnUnificationFailure, bool prepareOnly, bool reversedAbstractProofStrings, vector<size_t>* optOut_indexTranslation, unordered_map<size_t, size_t>* optOut_indexOrigins, map<size_t, size_t>* optOut_duplicates, vector<string>* optOut_otherProofStrings) { // NOTE: Detailed debug code available at https://github.com/deontic-logic/proof-tool/commit/c25e82b6c239fe33fa2b0823fcd17244a62f4a20
	// 1. Group and order the (in D-notation) given proofs by their length, and create a context lookup table
	map<size_t, set<string>> knownDProofsByLength; // length -> set of condensed detachment proofs of that length
	if (optOut_indexTranslation)
		*optOut_indexTranslation = vector<size_t>(dProofs.size());
	unordered_map<string, size_t> originalIndices;
	bool needDuplicates = optOut_indexTranslation || optOut_duplicates;
	bool needOriginalIndices = optOut_indexOrigins || needDuplicates;
	bool translateIndices = optOut_indexTranslation || optOut_indexOrigins;
	map<size_t, size_t> _duplicates;
	map<size_t, size_t>& duplicates = optOut_duplicates ? *optOut_duplicates : _duplicates;
	for (size_t i = 0; i < dProofs.size(); i++) {
		const string& concreteDProof = dProofs[i];
		if (concreteDProof.empty())
			throw invalid_argument("DRuleParser::parseDProofs(): dProofs[" + to_string(i) + "] is empty.");
		pair<set<string>::iterator, bool> empResult = knownDProofsByLength[concreteDProof.length()].emplace(concreteDProof);
		if (needOriginalIndices) {
			if (empResult.second)
				originalIndices.emplace(concreteDProof, i);
			else if (needDuplicates)
				duplicates[i] = originalIndices.at(*empResult.first);
		}
	}

	// 2. Replace all the redundancies in dProofs by references to other proofs in dProofs, to obtain pairs with such referencing proofs and their concrete variants.
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	vector<pair<string, string>> referencingDProofs; // refined condensed detachment proof (with references) -> extended condensed detachment proof (without references)
	for (const pair<const size_t, set<string>>& p : knownDProofsByLength) // register predefined references
		for (const string& concreteDProof : p.second) {
			string abstractDProof(concreteDProof);
			size_t pos = 1;
			for (vector<pair<string, string>>::const_reverse_iterator it = referencingDProofs.rbegin(); it != referencingDProofs.rend(); ++it) {
				if (it->second.length() > 1)
					boost::replace_all(abstractDProof, it->second, "[" + to_string(referencingDProofs.size() - pos) + "]");
				pos++;
			}
			referencingDProofs.push_back(make_pair(abstractDProof, concreteDProof));
		}

	// 3. Obtain the minimal set of referencing proofs that would be required to accomplish that each given proof can be retracted to a single rule with inputs.
	vector<pair<string, string>> helperProofCandidates;
	map<string, string> recentCandidates;
	do { // register all references, building up on existing references
		recentCandidates.clear();
		auto sufficientLen = [](const string& s) {
			// Nα: To contain proofs of fundamental length greater than 1, the containing proof requires length >= 3, e.g. NN1.
			// Dα: To contain proofs of fundamental length greater than 1, the containing proof requires length >= 4, e.g. D4N1.
			if (s.length() < 3 || (s[0] == 'D' && s.length() < 4))
				return false;
			// Since references may increase string length (but not proof length), it is fastest to look for a second rule occurrence.
			bool first = true;
			for (char c : s) {
				switch (c) {
				case 'D':
				case 'N':
					if (first)
						first = false;
					else
						return true;
					break;
				}
			}
			return false;
		};
		for (const pair<string, string>& p : referencingDProofs) {
			const string& abstractDProof = p.first;
			if (sufficientLen(abstractDProof)) {
				if (abstractDProof[0] != 'D' && abstractDProof[0] != 'N')
					throw invalid_argument("DRuleParser::parseDProofs(): A D-N-proof of length greater 1 must start with 'D' or 'N'.");
				string::size_type lastDNIndex = 0;
				bool lastOpN = false;
				bool inReference = false;
				unsigned nonDs = 0;
				string::size_type i;
				array<int, 2> referenceIndices = { -1, -1 }; // referenceIndices[i] = -n < 0 means that a reference index for i doesn't exist, i.e. argument[i] is an axiom (An), not a reference
				unsigned refIndex = 0;
				for (i = 1; i < abstractDProof.length(); i++) {
					char c = abstractDProof[i];
					switch (c) {
					case 'D':
						nonDs = 0;
						lastDNIndex = i;
						lastOpN = false;
						referenceIndices = { -1, -1 };
						break;
					case 'N': {
						nonDs = 0;
						lastDNIndex = i;
						lastOpN = true;
						referenceIndices[0] = -1;
						break;
					}
					case '[':
						inReference = true;
						refIndex = 0;
						break;
					case ']':
						if (lastDNIndex) {
							referenceIndices[nonDs] = refIndex;
							nonDs++;
						}
						inReference = false;
						break;
					case '0':
						if (inReference)
							refIndex = 10 * refIndex;
						else
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '0': Not a proof step.");
						break;
					case '1':
					case '2':
					case '3':
					case '4':
					case '5':
					case '6':
					case '7':
					case '8':
					case '9':
						if (inReference)
							refIndex = 10 * refIndex + (c - '0');
						else if ((!customAxioms && c > '3') || (customAxioms && static_cast<unsigned>(c) - '0' > customAxioms->size()))
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
						else if (lastDNIndex) {
							referenceIndices[nonDs] = '0' - c;
							nonDs++;
						}
						break;
					case 'a':
					case 'b':
					case 'c':
					case 'd':
					case 'e':
					case 'f':
					case 'g':
					case 'h':
					case 'i':
					case 'j':
					case 'k':
					case 'l':
					case 'm':
					case 'n':
					case 'o':
					case 'p':
					case 'q':
					case 'r':
					case 's':
					case 't':
					case 'u':
					case 'v':
					case 'w':
					case 'x':
					case 'y':
					case 'z':
						if (!customAxioms || 10u + c - 'a' > customAxioms->size())
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
						else if (lastDNIndex) {
							referenceIndices[nonDs] = 'a' - c - 10;
							nonDs++;
						}
						break;
					default:
						throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
					}
					auto appendByRefIndex = [&](string& concreteSubproof, int referenceIndex) {
						if (referenceIndex >= 0) { // a reference
							if (static_cast<unsigned>(referenceIndex) >= referencingDProofs.size() + helperProofCandidates.size())
								throw logic_error("DRuleParser::parseDProofs(): Impossible reference index " + to_string(referenceIndex) + ".");
							const string& concretePart = static_cast<unsigned>(referenceIndex) < referencingDProofs.size() ? referencingDProofs[referenceIndex].second : helperProofCandidates[referenceIndex - referencingDProofs.size()].second;
							concreteSubproof += concretePart;
						} else if (customAxioms) { // an axiom ; custom axioms
							unsigned axiomNumber = -referenceIndex;
							if (!axiomNumber || axiomNumber > customAxioms->size())
								throw logic_error("DRuleParser::parseDProofs(): Impossible pseudo reference index for axiom: " + to_string(referenceIndex));
							else if (axiomNumber <= 9)
								concreteSubproof += string { static_cast<char>('0' + axiomNumber) };
							else if (axiomNumber <= 36)
								concreteSubproof += string { static_cast<char>('a' + axiomNumber - 10) };
							else
								throw logic_error("DRuleParser::parseDProofs(): Impossible pseudo reference index for axiom: " + to_string(referenceIndex));
						} else // an axiom ; default axioms
							switch (referenceIndex) {
							case -1:
								concreteSubproof += "1";
								break;
							case -2:
								concreteSubproof += "2";
								break;
							case -3:
								concreteSubproof += "3";
								break;
							default:
								throw logic_error("DRuleParser::parseDProofs(): Impossible pseudo reference index for axiom: " + to_string(referenceIndex));
							}
					};
					if (lastOpN && nonDs == 1) { // Every "N<non-D>" that we read is a new subproof. Each "<non-D>" can be either an axiom, or a reference.
						string subProof(abstractDProof.begin() + lastDNIndex, abstractDProof.begin() + i + 1);
						pair<map<string, string>::iterator, bool> emplaceResult = recentCandidates.emplace(subProof, string { });
						if (emplaceResult.second) { // actually inserted => we still need to calculate the concrete subproof
							string& concreteSubproof = emplaceResult.first->second;
							concreteSubproof = "N";
							appendByRefIndex(concreteSubproof, referenceIndices[0]);
						}
						nonDs = 0;
						lastDNIndex = 0;
					} else if (nonDs == 2) { // Every "D<non-D><non-D>" that we read is a new subproof. Each "<non-D>" can be either an axiom, or a reference.
						string subProof(abstractDProof.begin() + lastDNIndex, abstractDProof.begin() + i + 1);
						pair<map<string, string>::iterator, bool> emplaceResult = recentCandidates.emplace(subProof, string { });
						if (emplaceResult.second) { // actually inserted => we still need to calculate the concrete subproof
							string& concreteSubproof = emplaceResult.first->second;
							concreteSubproof = "D";
							for (int referenceIndex : referenceIndices)
								appendByRefIndex(concreteSubproof, referenceIndex);
						}
						nonDs = 0;
						lastDNIndex = 0;
					}
				}
			}
		}
		size_t proofIndex = helperProofCandidates.size() + referencingDProofs.size(); // starting index of the new stuff
		for (const pair<const string, string>& p : recentCandidates) {
			const string& recentExtraProof = p.first;
			// Replacements in existing basic proofs
			for (vector<pair<string, string>>::iterator itDProof = referencingDProofs.begin(); itDProof != referencingDProofs.end(); ++itDProof)
				if (sufficientLen(itDProof->first))
					boost::replace_all(itDProof->first, recentExtraProof, "[" + to_string(proofIndex) + "]");
			// NOTE: Extra proofs are created bottom-up, i.e. they only contain a single rule (D-rule: length 3, N-rule: length 2) thus are too small for being added new references.
			proofIndex++;
		}
		// Registration of new extra proofs
		helperProofCandidates.insert(helperProofCandidates.end(), recentCandidates.begin(), recentCandidates.end());
	} while (!recentCandidates.empty());
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to obtain " << helperProofCandidates.size() << " helper proof candidate" << (helperProofCandidates.size() == 1 ? "" : "s") << ", i.e. the minimal set of referenced proofs such that each proof contains only a single rule with inputs." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 4. Keep only those helper proof candidates which are referenced at least 'minUseAmountToCreateHelperProof' times. The concrete variants of the accepted
	//    candidates are -- grouped by concrete lengths -- inserted into 'knownDProofsByLength', which already contains the given proofs in the same manner.
	map<size_t, unsigned> referenceAmounts; // index of proof -> amount of references to proof
	auto findReferences = [&](const string& dProof) {
		bool inReference = false;
		unsigned refIndex = 0;
		for (char c : dProof)
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
					if (refIndex >= referencingDProofs.size())
						referenceAmounts[refIndex]++; // Only test the extra references, since only they are optional.
					refIndex = 0;
					inReference = false;
					break;
				default:
					throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not part of a proof reference.");
				}
			else if (c == '[')
				inReference = true;
	};
	for (const pair<string, string>& p : referencingDProofs) {
		const string& referencingDProof = p.first;
		findReferences(referencingDProof);
	}
	for (const pair<string, string>& p : helperProofCandidates) {
		const string& extraProof = p.first;
		findReferences(extraProof);
	}
	unsigned extraCounter = 0;
	{
		size_t containerIndex = referencingDProofs.size();
		for (const pair<string, string>& p : helperProofCandidates) {
			if (referenceAmounts[containerIndex] >= minUseAmountToCreateHelperProof) {
				const string& extraProof = p.second; // concrete variant to be applied a correct index according to its length
				knownDProofsByLength[extraProof.length()].emplace(extraProof);
				extraCounter++;
			}
			containerIndex++;
		}
	}
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to reduce to " << extraCounter << " helper proof" << (extraCounter == 1 ? "" : "s") << "." << endl;
		startTime = chrono::steady_clock::now();
	}
	if (optOut_knownDProofsByLength)
		*optOut_knownDProofsByLength = knownDProofsByLength;
	//#cout << FctHelper::mapStringF(knownDProofsByLength, [](const pair<const size_t, set<string>>& p) { return to_string(p.first) + " : " + FctHelper::setString(p.second); }, "{\n\t", "\n}", "\n\t") << endl;
	if (prepareOnly) {
		if (debug) {
			size_t proofCounter = 0;
			for (const pair<const size_t, set<string>>& p : knownDProofsByLength)
				proofCounter += p.second.size();
			cout << proofCounter << " condensed detachment proof" << (proofCounter == 1 ? "" : "s") << " prepared." << endl;
		}
		return {};
	}

	// 5. Create requested condensed detachment proofs with references ("refined D-proofs"), ordered by their concrete length.
	vector<string> proofStrings;
	vector<string> reversedDProofs;
	vector<string> refinedDProofs;
	for (const pair<const size_t, set<string>>& p : knownDProofsByLength)
		for (const string& concreteDProof : p.second) {
			string refinedDProof(concreteDProof);
			reverse(refinedDProof.begin(), refinedDProof.end());
			string reversedDProof(refinedDProof);
			size_t pos = 1;
			for (vector<string>::const_reverse_iterator it = reversedDProofs.rbegin(); it != reversedDProofs.rend(); ++it) {
				if (it->length() > 1)
					boost::replace_all(refinedDProof, *it, "[" + to_string(reversedDProofs.size() - pos) + "]");
				pos++;
			}
			reversedDProofs.push_back(reversedDProof); // Add after inserting references, to avoid self-referencing.
			refinedDProofs.push_back(refinedDProof);
			proofStrings.push_back(concreteDProof);
		}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to refine " << proofStrings.size() << " condensed detachment proof" << (proofStrings.size() == 1 ? "" : "s") << "." << endl;
	//#cout << FctHelper::vectorString(refinedDProofs, "{\n\t", "\n}", "\n\t") << endl;

	// 6. Convert refined D Proof to DL-proofs.
	if (debug)
		startTime = chrono::steady_clock::now();
	uint64_t counter = 0;
	vector<string> primitiveStrings;
	auto getPrimitiveString = [&](unsigned index) -> string {
		if (index == primitiveStrings.size()) {
			string result = to_string(index);
			primitiveStrings.push_back(result);
			return result;
		} else
			return primitiveStrings[index];
	};
	vector<DProofInfo> rawProofData;
	vector<pair<vector<shared_ptr<DlFormula>>, vector<string>>> modProofs(refinedDProofs.size());
	for (const string& refinedDProof : refinedDProofs) {
		set<shared_ptr<DlFormula>> freePrimitives; // need to have unique pointers for each condensed detachment proof
		unsigned primitiveStringsIndex = 0;
		set<shared_ptr<DlFormula>> usedPrimitives;

		vector<shared_ptr<DlFormula>>& formulas = modProofs[counter].first;
		vector<string>& dReasons = modProofs[counter].second;
		map<size_t, vector<unsigned>> metadata; // metadata[pos] := metadata for DlProof
		vector<bool> used;

		// Helper lambdas
		auto registerFreshPrimitives = [&](unsigned num) -> vector<shared_ptr<DlFormula>> {
			vector<shared_ptr<DlFormula>> newPtrs;
			for (unsigned i = 0; i < num; i++) {
				shared_ptr<DlFormula> primitive;
				if (freePrimitives.empty())
					primitive = make_shared<DlFormula>(make_shared<String>(getPrimitiveString(primitiveStringsIndex++)));
				else {
					primitive = *freePrimitives.begin();
					freePrimitives.erase(freePrimitives.begin());
				}
				usedPrimitives.emplace(primitive);
				newPtrs.push_back(primitive);
			}
			return newPtrs;
		};
		auto updatePrimitives = [&]() {
			for (set<shared_ptr<DlFormula>>::iterator it = usedPrimitives.begin(); it != usedPrimitives.end();)
				if (it->use_count() == 1) {
					freePrimitives.emplace(*it);
					it = usedPrimitives.erase(it);
				} else
					++it;
		};

		// Iterate the instructions of the condensed detachment proof (which, additionally, has references).
		bool atRef = false;
		unsigned refIndex = 0;
		for (char c : refinedDProof)
			if (atRef)
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
				case ']': {
					// Store formula and reason
					formulas.push_back(modProofs[refIndex].first.back());
					dReasons.push_back("R");
					used.push_back(false);

					// Store lookup data (referenced proof index)
					metadata[formulas.size()] = { refIndex };

					// Insert fresh primitives into formula
					shared_ptr<DlFormula>& formula = formulas.back();

					// Basically does what DlFormula::cloneSharedPtr() would do, but additionally primitives are assigned to a new unique reference, and does not copy meanings.
					// NOTE: Using DlFormula::cloneSharedPtr(true, &cloneMap) may enrich cloneMap by further primitive entries which we DON'T WANT! We want the same primitives for equal strings.
					auto cloneSharedPtr_withUniquePrimitives = [&](const shared_ptr<DlFormula>& node, DlFormula::CloneMap& knownClones, unordered_map<string, shared_ptr<DlFormula>>& primitiveReferences, const auto& me) -> shared_ptr<DlFormula> {
						DlFormula::CloneMap::iterator searchResult = knownClones.find(static_cast<const DlFormula*>(node.get()));
						if (searchResult != knownClones.end()) {
							const shared_ptr<DlFormula>& knownCloneEntry = searchResult->second;
							if (knownCloneEntry)
								return knownCloneEntry; // We can return the known clone itself (by reference).
						}
						const vector<shared_ptr<DlFormula>>& children = node->getChildren();
						const string& value = node->getValue()->value;
						if (!children.empty() || value == DlCore::terminalStr_top() || value == DlCore::terminalStr_bot()) {
							shared_ptr<DlFormula> clone = make_shared<DlFormula>(node->getValue());
							for (const shared_ptr<DlFormula>& child : children)
								clone->addChild(child ? me(child, knownClones, primitiveReferences, me) : nullptr);
							knownClones[static_cast<const DlFormula*>(node.get())] = clone; // Remember the shared address of the clone (for referencing).
							return clone;
						} else {
							unordered_map<string, shared_ptr<DlFormula>>::iterator searchResult = primitiveReferences.find(value);
							if (searchResult == primitiveReferences.end()) {
								shared_ptr<DlFormula> primitive = registerFreshPrimitives(1)[0];
								primitiveReferences[value] = primitive;
								return primitive;
							} else
								return searchResult->second;
						}
					};
					DlFormula::CloneMap cloneMap;
					unordered_map<string, shared_ptr<DlFormula>> primitiveReferences; // to assign primitives by strings
					formula = cloneSharedPtr_withUniquePrimitives(formula, cloneMap, primitiveReferences, cloneSharedPtr_withUniquePrimitives); // partial cloning

					atRef = false;
					refIndex = 0;
					break;
				}
				default:
					throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not part of a proof reference.");
				}
			else
				switch (c) {
				default:
					if (customAxioms)
						switch (c) {
						case '1':
						case '2':
						case '3':
						case '4':
						case '5':
						case '6':
						case '7':
						case '8':
						case '9': {
							unsigned i = c - '1';
							const vector<AxiomInfo>& ax = *customAxioms;
							if (i >= ax.size())
								throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
							formulas.push_back(_ax(i, registerFreshPrimitives(ax[i].primitivesCount), ax));
							dReasons.push_back(string { c });
							used.push_back(false);
							break;
						}
						case 'a':
						case 'b':
						case 'c':
						case 'd':
						case 'e':
						case 'f':
						case 'g':
						case 'h':
						case 'i':
						case 'j':
						case 'k':
						case 'l':
						case 'm':
						case 'n':
						case 'o':
						case 'p':
						case 'q':
						case 'r':
						case 's':
						case 't':
						case 'u':
						case 'v':
						case 'w':
						case 'x':
						case 'y':
						case 'z': {
							unsigned i = 10 + c - 'a' - 1;
							const vector<AxiomInfo>& ax = *customAxioms;
							if (i >= ax.size())
								throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
							formulas.push_back(_ax(i, registerFreshPrimitives(ax[i].primitivesCount), ax));
							dReasons.push_back(string { c });
							used.push_back(false);
							break;
						}
						default:
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
						}
					else
						switch (c) {
						case '1': {
							vector<shared_ptr<DlFormula>> freshPrimitives = registerFreshPrimitives(2);
							shared_ptr<DlFormula> ax1 = _ax1(freshPrimitives[0], freshPrimitives[1]);
							formulas.push_back(ax1);
							dReasons.push_back("1");
							used.push_back(false);
							break;
						}
						case '2': {
							vector<shared_ptr<DlFormula>> freshPrimitives = registerFreshPrimitives(3);
							shared_ptr<DlFormula> ax2 = _ax2(freshPrimitives[0], freshPrimitives[1], freshPrimitives[2]);
							formulas.push_back(ax2);
							dReasons.push_back("2");
							used.push_back(false);
							break;
						}
						case '3': {
							vector<shared_ptr<DlFormula>> freshPrimitives = registerFreshPrimitives(2);
							shared_ptr<DlFormula> ax3 = _ax3(freshPrimitives[0], freshPrimitives[1]);
							formulas.push_back(ax3);
							dReasons.push_back("3");
							used.push_back(false);
							break;
						}
						default:
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
						}
					break;
				case 'N': {
					if (formulas.empty())
						throw invalid_argument("DRuleParser::parseDProofs(): Invalid N-rule for condensed detachment proof '" + proofStrings[counter] + "'.");
					used.back() = true;
					metadata[formulas.size() + 1] = { static_cast<unsigned>(formulas.size()) };
					formulas.push_back(make_shared<DlFormula>(_nece(), vector<shared_ptr<DlFormula>> { formulas.back() }));
					dReasons.push_back("N");
					used.push_back(false);
					break;
				}
				case 'D': {
					if (formulas.size() < 2)
						throw invalid_argument("DRuleParser::parseDProofs(): Invalid D-rule for condensed detachment proof '" + proofStrings[counter] + "'.");
					// 1. Determine antecedent and conditional
					//    NOTE: The D-rule is basically (MP):n,x for a current length of n, i.e. x: A->B, n: A => n+1: B, where x is the last position before n that has not yet been used.
					shared_ptr<DlFormula>& conditional = formulas.back();
					used.back() = true;
					const vector<shared_ptr<DlFormula>>& conditional_children = conditional->getChildren();
					if (conditional_children.size() != 2 || conditional->getValue()->value != DlCore::terminalStr_imply()) {
						if (exceptionOnUnificationFailure) // The form is correct, but the formulas don't match to be antecedent and conditional. Thus, this is actually a unification failure.
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid conditional for condensed detachment proof '" + proofStrings[counter] + "'.");
						else
							return {};
					}
					int lastTodo;
					for (lastTodo = static_cast<int>(used.size()) - 2; lastTodo >= 0; lastTodo--)
						if (!used[lastTodo])
							break;
					if (lastTodo < 0)
						throw invalid_argument("DRuleParser::parseDProofs(): Cannot find antecedent for condensed detachment proof '" + proofStrings[counter] + "'.");
					shared_ptr<DlFormula>& antecedent = formulas[lastTodo];
					used[lastTodo] = true;
					metadata[formulas.size() + 1] = { static_cast<unsigned>(lastTodo) + 1, static_cast<unsigned>(formulas.size()) };

					{ // NOTE: Need these braces so that the use counts are correct for updatePrimitives().

						// 2. Obtain substitutions via unification and partial cloning
						map<string, shared_ptr<DlFormula>> substitutions;
						if (!DlCore::tryUnifyTrees(antecedent, conditional_children[0], &substitutions)) {
							//#cerr << formulas.size() << ". " << DlCore::formulaRepresentation_traverse(formulas.back()) << "\t\t" << dReasons.back() << endl;
							if (exceptionOnUnificationFailure)
								throw invalid_argument("DRuleParser::parseDProofs(): Failed to find unification for " + DlCore::formulaRepresentation_traverse(antecedent) + " and " + DlCore::formulaRepresentation_traverse(conditional_children[0]) + ".");
							else
								return {};
						}

						// Basically does what DlFormula::cloneSharedPtr() would do, except that primitives are not cloned but changed to a unique reference, and meanings are not copied.
						// NOTE: Using DlFormula::cloneSharedPtr(true, &cloneMap) may enrich cloneMap by further primitive entries which we DON'T WANT! We want the same primitives for equal strings.
						auto cloneSharedPtr_makePrimitivesUnique = [](const shared_ptr<DlFormula>& node, DlFormula::CloneMap& knownClones, unordered_map<string, shared_ptr<DlFormula>>& primitiveReferences, const auto& me) -> shared_ptr<DlFormula> {
							DlFormula::CloneMap::iterator searchResult = knownClones.find(static_cast<const DlFormula*>(node.get()));
							if (searchResult != knownClones.end()) {
								const shared_ptr<DlFormula>& knownCloneEntry = searchResult->second;
								if (knownCloneEntry)
									return knownCloneEntry; // We can return the known clone itself (by reference).
							}
							const vector<shared_ptr<DlFormula>>& children = node->getChildren();
							const string& value = node->getValue()->value;
							if (!children.empty() || value == DlCore::terminalStr_top() || value == DlCore::terminalStr_bot()) {
								shared_ptr<DlFormula> clone = make_shared<DlFormula>(node->getValue());
								for (const shared_ptr<DlFormula>& child : children)
									clone->addChild(child ? me(child, knownClones, primitiveReferences, me) : nullptr);
								knownClones[static_cast<const DlFormula*>(node.get())] = clone; // Remember the shared address of the clone (for referencing).
								return clone;
							} else
								return primitiveReferences.at(value);
						};

						// The output of DlCore::tryUnifyTrees() shall be safely used with modifyingSubstitute(), therefore the substitution entries must be cloned unless they are primitives.
						// NOTE: The cloning part could be removed in case DlCore::tryUnifyTrees()'s behavior would be modified in this way (but a variant that doesn't clone should be kept since it is faster this way).
						DlFormula::CloneMap baseCloneMap; // to assign non-primitives by pointers ; unordered_map<const DlFormula*, shared_ptr<DlFormula>> of predefined 'clone' assignments
						for (const shared_ptr<DlFormula>& primitive : usedPrimitives)
							baseCloneMap.emplace(primitive.get(), primitive);
						unordered_map<string, shared_ptr<DlFormula>> primitiveReferences; // to assign primitives by strings
						for (const shared_ptr<DlFormula>& primitive : usedPrimitives)
							primitiveReferences.emplace(primitive->getValue()->value, primitive);
						for (pair<const string, shared_ptr<DlFormula>>& p : substitutions) {
							DlFormula::CloneMap cloneMap = baseCloneMap;
							p.second = cloneSharedPtr_makePrimitivesUnique(p.second, cloneMap, primitiveReferences, cloneSharedPtr_makePrimitivesUnique); // partial cloning
						}

						// 3. Update all the formulas
						unordered_set<shared_ptr<DlFormula>> alreadyModified; // avoid to substitute multiple times on the same subtrees
						for (shared_ptr<DlFormula>& f : formulas)
							modifyingSubstitute(f, substitutions, &alreadyModified);
					}

					// 4. Remove primitives that are not used anymore
					updatePrimitives();

					// 5. Update proof
					const shared_ptr<DlFormula>& consequent = conditional->getChildren()[1];
					formulas.push_back(consequent);
					dReasons.push_back("D");
					used.push_back(false);
					break;
				}
				case '[':
					atRef = true;
					break;
				}
		if (used.size() > 1 && !used[0]) // the first formula was not used ; prevents parsing strings like "11" or "D123"
			throw invalid_argument("DRuleParser::parseDProofs(): Condensed detachment proof '" + proofStrings[counter] + "' has unused formulas.");

		// The order of variables shall first respect occurrences in the conclusion and second occurrences in the proof.
		vector<DlFormula*> primitivesSequence;
		if (!formulas.empty()) {
			unordered_set<DlFormula*> alreadyProcessedPrimitives;
			auto appendNewPrimitivesOfFormula = [&](const shared_ptr<DlFormula>& formula) {
				auto recurse = [&](const shared_ptr<DlFormula>& formula, const auto& me) {
					if (primitivesSequence.size() == usedPrimitives.size())
						return; // All used primitives have been found, so we are done.
					const string& value = formula->getValue()->value;
					if (formula->getChildren().empty()) {
						if (value != DlCore::terminalStr_bot() && value != DlCore::terminalStr_top() && alreadyProcessedPrimitives.emplace(formula.get()).second)
							primitivesSequence.push_back(formula.get());
					} else
						for (const shared_ptr<DlFormula>& subformula : formula->getChildren())
							me(subformula, me);
				};
				recurse(formula, recurse);
			};
			appendNewPrimitivesOfFormula(formulas.back());
			for (size_t i = 0; i + 1 < formulas.size(); i++) {
				appendNewPrimitivesOfFormula(formulas[i]);
				if (primitivesSequence.size() == usedPrimitives.size())
					break; // All used primitives have been found, so we are done.
			}
		}
		if (primitivesSequence.size() != usedPrimitives.size())
			throw logic_error("DRuleParser::parseDProofs(): |primitivesSequence| = " + to_string(primitivesSequence.size()) + " != " + to_string(usedPrimitives.size()) + " = |usedPrimitives|");
		unsigned primitiveCounter = 0;
		for (DlFormula* primitive : primitivesSequence)
			primitive->getValue()->value = to_string(primitiveCounter++);

		// Calculate meanings if requested
		if (calculateMeanings)
			for (const shared_ptr<DlFormula>& f : formulas)
				DlCore::calculateEmptyMeanings(f); // NOTE: It must be ensured that all meanings are empty or correct until leaves for this to work. Otherwise, DlCore::reduceFormulaMeaning_modifying(f) must be used.

		if (translateIndices) {
			unordered_map<string, size_t>::iterator searchResult = originalIndices.find(proofStrings[counter]);
			if (searchResult != originalIndices.end()) {
				if (optOut_indexTranslation)
					(*optOut_indexTranslation)[searchResult->second] = rawProofData.size();
				if (optOut_indexOrigins)
					optOut_indexOrigins->emplace(rawProofData.size(), searchResult->second);
			}
		}
		if (optOut_otherProofStrings) {
			if (reversedAbstractProofStrings) {
				rawProofData.push_back(make_pair(refinedDProofs[counter], make_tuple(formulas, dReasons, metadata)));
				optOut_otherProofStrings->push_back(proofStrings[counter]);
			} else {
				rawProofData.push_back(make_pair(proofStrings[counter], make_tuple(formulas, dReasons, metadata)));
				optOut_otherProofStrings->push_back(refinedDProofs[counter]);
			}
		} else
			rawProofData.push_back(make_pair(reversedAbstractProofStrings ? refinedDProofs[counter] : proofStrings[counter], make_tuple(formulas, dReasons, metadata)));
		counter++;
	}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to convert " << proofStrings.size() << " condensed detachment proof" << (proofStrings.size() == 1 ? " to a formula-based proof" : "s to formula-based proofs") << "." << endl;
	if (optOut_indexTranslation)
		for (const pair<const size_t, size_t>& duplicate : duplicates)
			(*optOut_indexTranslation)[duplicate.first] = (*optOut_indexTranslation)[duplicate.second];
	return rawProofData;
}

void DRuleParser::reverseAbstractProofString(string& abstractDProof) {
	reverse(abstractDProof.begin(), abstractDProof.end());
	string::size_type pos = 0;
	string::size_type a;
	string::size_type b;
	while ((a = abstractDProof.find(']', pos)) != string::npos) {
		if ((b = abstractDProof.find('[', a + 2)) == string::npos) {
			reverse(abstractDProof.begin() + a, abstractDProof.end());
			break;
		} else if (b - a > 2) {
			reverse(abstractDProof.begin() + a, abstractDProof.begin() + b + 1);
		} else {
			abstractDProof[a] = '[';
			abstractDProof[b] = ']';
		}
		pos = b + 1;
	}
}

shared_ptr<DlFormula> DRuleParser::parseMmConsequent(const string& strConsequent, bool calculateMeanings) {
	if (strConsequent.empty())
		throw invalid_argument("DRuleParser::parseConsequent(): Input is empty.");
#ifdef PARSEMMPL_STORED
	static unordered_map<string, shared_ptr<DlFormula>> formulaBackups;
	unordered_map<string, shared_ptr<DlFormula>>::iterator backupResult = formulaBackups.find(strConsequent);
	if (backupResult != formulaBackups.end())
		return backupResult->second;
#endif
	string::const_iterator consBegin = strConsequent.begin();
	int depth = 0;
	vector<string::size_type> openings;
	map<string::size_type, pair<string::size_type, shared_ptr<DlFormula>>> subformulas; // first -> ( last, formula ) ; Using ordering by first index for fast subformula detection.
	bool ended = false;
	for (string::size_type i = 0; i < strConsequent.length(); i++)
		switch (strConsequent[i]) {
		case '(':
			if (ended)
				throw invalid_argument("DRuleParser::parseConsequent(): Invalid input \"" + strConsequent + "\" has more than one top-level subformulas.");
			openings.push_back(i);
			depth++;
			break;
		case ')':
			if (depth == 0)
				throw invalid_argument("DRuleParser::parseConsequent(): Invalid input \"" + strConsequent + "\" has too many ')'.");
			const string::size_type& currentSubformulaIndex = openings.back();
#ifdef PARSEMMPL_STORED
			shared_ptr<DlFormula> subformula = _parseEnclosedMmFormula(formulaBackups, strConsequent, currentSubformulaIndex, i, subformulas, consBegin);
#else
			shared_ptr<DlFormula> subformula = _parseEnclosedMmFormula(strConsequent, currentSubformulaIndex, i, subformulas, consBegin);
#endif
			subformulas.insert(make_pair(currentSubformulaIndex, make_pair(i, subformula)));
			openings.pop_back();
			depth--;
			if (depth == 0)
				ended = true;
			break;
		}
	if (depth > 0)
		throw invalid_argument("DRuleParser::parseConsequent(): Invalid input \"" + strConsequent + "\" has too few ')'.");

	if (subformulas.empty())
		throw invalid_argument("DRuleParser::parseConsequent(): Invalid input \"" + strConsequent + "\" has no subformulas.");
	const pair<string::size_type, pair<string::size_type, shared_ptr<DlFormula>>>& topLevelResult = *subformulas.begin();
	string::size_type topLevelOpening = topLevelResult.first;
	if (topLevelResult.second.first + 1 != strConsequent.length())
		throw invalid_argument("DRuleParser::parseConsequent(): Invalid input \"" + strConsequent + "\" has non-enclosed postfix.");
	if (topLevelOpening) { // Is there something in the beginning not processed yet?
		if (strConsequent[topLevelOpening - 1] != ' ')
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid input \"" + strConsequent + "\" has non-enclosed prefix without separation.");
		string_view unaryOperatorSequence(consBegin, consBegin + topLevelOpening);
		vector<DlOperator> unaryOperators;
		string_view::iterator unopsEnd = _obtainUnaryOperatorSequence(unaryOperatorSequence, unaryOperators);
		if (unopsEnd < unaryOperatorSequence.end())
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid unary operator sequence \"" + string(unaryOperatorSequence) + "\" for input \"" + strConsequent + "\".");
		shared_ptr<DlFormula> result = topLevelResult.second.second;
		string currentPrefix;
		for (vector<DlOperator>::const_reverse_iterator it = unaryOperators.rbegin(); it != unaryOperators.rend(); ++it) { // apply unary operators in reverse order
			DlOperator op = *it;
			switch (op) {
			case DlOperator::Not:
				currentPrefix = "~ " + currentPrefix;
				result = make_shared<DlFormula>(_not(), vector<shared_ptr<DlFormula>> { result });
				break;
			case DlOperator::Nece:
				currentPrefix = "□ " + currentPrefix;
				result = make_shared<DlFormula>(_nece(), vector<shared_ptr<DlFormula>> { result });
				break;
			case DlOperator::Poss:
				currentPrefix = "◇ " + currentPrefix;
				result = make_shared<DlFormula>(_poss(), vector<shared_ptr<DlFormula>> { result });
				break;
			default:
				throw logic_error("DRuleParser::parseConsequent(): Input \"" + strConsequent + "\" resulted in invalid unary operator (DlOperator)" + to_string(static_cast<unsigned>(op)) + ".");
			}
			string currentFormula = currentPrefix + strConsequent.substr(topLevelOpening);
#ifdef PARSEMMPL_STORED
			formulaBackups.emplace(make_pair(currentFormula, result)); // try to store result for backups
#endif
		}
		if (calculateMeanings)
			DlCore::calculateEmptyMeanings(result);
		return result;
	} else {
		shared_ptr<DlFormula> result = topLevelResult.second.second;
		if (calculateMeanings)
			DlCore::calculateEmptyMeanings(result);
		return result;
	}
}

string DRuleParser::toDBProof(const string& dProof, const vector<AxiomInfo>* customAxioms, const string& name, const string& theorem, bool normalPolishNotation) { // also checks for valid schema (if theorem is given)
	stringstream ss;

	// Parse proof (or throw exception).
	vector<DProofInfo> rawParseData = parseDProof_raw(dProof, customAxioms, 1);
	const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();

	// Obtain result from conclusion.
	static const map<string, shared_ptr<DlFormula>> resultSubstitutions { { { "0", make_shared<DlFormula>(make_shared<String>("P")) }, { "1", make_shared<DlFormula>(make_shared<String>("Q")) }, { "2", make_shared<DlFormula>(make_shared<String>("R")) }, { "3", make_shared<DlFormula>(make_shared<String>("S")) }, { "4", make_shared<DlFormula>(make_shared<String>("T")) }, { "5", make_shared<DlFormula>(make_shared<String>("U")) }, { "6", make_shared<DlFormula>(make_shared<String>("V")) }, { "7", make_shared<DlFormula>(make_shared<String>("W")) }, { "8", make_shared<DlFormula>(make_shared<String>("X")) }, { "9", make_shared<DlFormula>(make_shared<String>("Y")) }, { "10", make_shared<DlFormula>(make_shared<String>("Z")) }, { "11", make_shared<DlFormula>(make_shared<String>("A")) }, { "12", make_shared<DlFormula>(make_shared<String>("B")) }, { "13", make_shared<DlFormula>(make_shared<String>("C")) }, { "14", make_shared<DlFormula>(make_shared<String>("D")) }, { "15", make_shared<DlFormula>(make_shared<String>("E")) }, { "16", make_shared<DlFormula>(make_shared<String>("F")) }, { "17", make_shared<DlFormula>(make_shared<String>("G")) }, { "18", make_shared<DlFormula>(make_shared<String>("H")) }, { "19", make_shared<DlFormula>(make_shared<String>("I")) }, { "20", make_shared<DlFormula>(make_shared<String>("J")) }, { "21", make_shared<DlFormula>(make_shared<String>("K")) }, { "22", make_shared<DlFormula>(make_shared<String>("L")) }, { "23", make_shared<DlFormula>(make_shared<String>("M")) }, { "24", make_shared<DlFormula>(make_shared<String>("N")) }, { "25", make_shared<DlFormula>(make_shared<String>("O")) } } };
	shared_ptr<DlFormula> result = DlCore::substitute(conclusion, resultSubstitutions);
	string f = DlCore::standardFormulaRepresentation(result);
	boost::replace_all(f, DlCore::terminalStr_not(), "~ ");
	boost::replace_all(f, DlCore::terminalStr_nece(), "□ ");
	boost::replace_all(f, DlCore::terminalStr_imply(), " -> ");

	// Obtain desired consequent.
	shared_ptr<DlFormula> consequent;
	if (!theorem.empty()) {
		if (normalPolishNotation) {
			if (!DlCore::fromPolishNotation(consequent, theorem))
				throw invalid_argument("Cannot parse \"" + theorem + "\" as a formula in normal Polish notation.");
		} else if (!DlCore::fromPolishNotation_noRename(consequent, theorem))
			throw invalid_argument("Cannot parse \"" + theorem + "\" as a formula in dotted Polish notation.");

		// Check if we can substitute to desired consequent.
		shared_ptr<DlFormula> reference = DlCore::toBasicDlFormula(consequent, nullptr, nullptr, nullptr, false);
		if (!DlCore::isSchemaOf(conclusion, reference))
			throw invalid_argument("DRuleReducer::applyReplacements(): (" + theorem + ") " + DlCore::formulaRepresentation_traverse(conclusion) + " is not a schema of BasicDL(consequent) " + DlCore::formulaRepresentation_traverse(reference) + ".");

		map<string, shared_ptr<DlFormula>> substitutions;
		vector<string> primitives = DlCore::primitivesOfFormula_ordered(consequent);
		for (size_t i = 0; i < primitives.size(); i++) {
			string var;
			size_t x = i;
			bool first = true;
			do {
				if (first)
					first = false;
				else
					x--;
				size_t m = x % 26;
				var = string { char(m + (m < 11 ? 'P' : 'A' - 11)) } + var; // 0:P, ..., 10:Z, 11:A, ..., 25:O
				x -= m;
				x /= 26;
			} while (x);
			substitutions.emplace(primitives[i], make_shared<DlFormula>(make_shared<String>(var)));
		}
		consequent = DlCore::substitute(consequent, substitutions);
		string f = DlCore::standardFormulaRepresentation(consequent);
		boost::replace_all(f, DlCore::terminalStr_not(), "~ ");
		boost::replace_all(f, DlCore::terminalStr_nece(), "□ ");
		boost::replace_all(f, DlCore::terminalStr_poss(), "◇ ");
		boost::replace_all(f, DlCore::terminalStr_imply(), " -> ");
		boost::replace_all(f, DlCore::terminalStr_and(), " ^ ");
		boost::replace_all(f, DlCore::terminalStr_or(), " v ");
		boost::replace_all(f, DlCore::terminalStr_equiv(), " <-> ");
		ss << f << "; ! ";
	} else
		ss << f << "; ! ";

	// Obtain desired name.
	if (!name.empty())
		ss << name << "\n";
	else
		ss << DlCore::toPolishNotation(theorem.empty() ? conclusion : consequent) << "\n";
	ss << f << "; ! Result of proof\n";
	ss << dProof << "; ! " << dProof.length() << " step" << (dProof.length() == 1 ? "" : "s") << "\n";
	return ss.str();
}

void DRuleParser::parseAbstractDProof(vector<string>& inOut_abstractDProof, vector<shared_ptr<DlFormula>>& out_abstractDProofConclusions, const vector<AxiomInfo>* customAxioms, vector<string>* optOut_helperRules, vector<shared_ptr<DlFormula>>* optOut_helperRulesConclusions, vector<size_t>* optOut_indexEvalSequence, bool debug) {
	if (customAxioms && customAxioms->empty())
		throw invalid_argument("Axiom list given but empty.");

	// 1. Ensure full referencing (except that only higher indices can reference lower indices)
	//#cout << "\n[BEFORE]\n" << FctHelper::vectorString(inOut_abstractDProof, { }, { }, "\n") << endl;
	for (size_t i = 1; i < inOut_abstractDProof.size(); i++)
		for (size_t j = 0; j < i; j++)
			boost::replace_all(inOut_abstractDProof[i], inOut_abstractDProof[j], "[" + to_string(j) + "]");
	//#cout << "\n[AFTER]\n" << FctHelper::vectorString(inOut_abstractDProof, { }, { }, "\n") << endl;

	// 2. Obtain the minimal set of referencing proofs that would be required to accomplish that each given proof can be retracted to a single rule with inputs.
	//    Note: Similar to (3.) in parseDProofs_raw(), but without concrete proofs.
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	vector<string> helperRules;
	set<string> recentDRules;
	do { // register all references, building up on existing references
		recentDRules.clear();
		auto sufficientLen = [](const string& s) {
			// Nα: To contain proofs of fundamental length greater than 1, the containing proof requires length >= 3, e.g. NN1.
			// Dα: To contain proofs of fundamental length greater than 1, the containing proof requires length >= 4, e.g. D4N1.
			if (s.length() < 3 || (s[0] == 'D' && s.length() < 4))
				return false;
			// Since references may increase string length (but not proof length), it is fastest to look for a second rule occurrence.
			bool first = true;
			for (char c : s) {
				switch (c) {
				case 'D':
				case 'N':
					if (first)
						first = false;
					else
						return true;
					break;
				}
			}
			return false;
		};
		for (const string& abstractDProofEntry : inOut_abstractDProof) {
			if (sufficientLen(abstractDProofEntry)) {
				if (abstractDProofEntry[0] != 'D' && abstractDProofEntry[0] != 'N')
					throw invalid_argument("DRuleParser::parseAbstractDProof(): A D-N-proof of length greater 1 must start with 'D' or 'N'.");
				string::size_type lastDNIndex = 0;
				bool lastOpN = false;
				bool inReference = false;
				unsigned nonDs = 0;
				string::size_type i;
				array<int, 2> referenceIndices = { -1, -1 }; // referenceIndices[i] = -n < 0 means that a reference index for i doesn't exist, i.e. argument[i] is an axiom (An), not a reference
				unsigned refIndex = 0;
				for (i = 1; i < abstractDProofEntry.length(); i++) {
					char c = abstractDProofEntry[i];
					switch (c) {
					case 'D':
						nonDs = 0;
						lastDNIndex = i;
						lastOpN = false;
						referenceIndices = { -1, -1 };
						break;
					case 'N': {
						nonDs = 0;
						lastDNIndex = i;
						lastOpN = true;
						referenceIndices[0] = -1;
						break;
					}
					case '[':
						inReference = true;
						refIndex = 0;
						break;
					case ']':
						if (lastDNIndex) {
							referenceIndices[nonDs] = refIndex;
							nonDs++;
						}
						inReference = false;
						break;
					case '0':
						if (inReference)
							refIndex = 10 * refIndex;
						else
							throw invalid_argument("DRuleParser::parseAbstractDProof(): Invalid character '0': Not a proof step.");
						break;
					case '1':
					case '2':
					case '3':
					case '4':
					case '5':
					case '6':
					case '7':
					case '8':
					case '9':
						if (inReference)
							refIndex = 10 * refIndex + (c - '0');
						else if ((!customAxioms && c > '3') || (customAxioms && static_cast<unsigned>(c) - '0' > customAxioms->size()))
							throw invalid_argument("DRuleParser::parseAbstractDProof(): Invalid character '" + string { c } + "': Not a proof step.");
						else if (lastDNIndex) {
							referenceIndices[nonDs] = '0' - c;
							nonDs++;
						}
						break;
					case 'a':
					case 'b':
					case 'c':
					case 'd':
					case 'e':
					case 'f':
					case 'g':
					case 'h':
					case 'i':
					case 'j':
					case 'k':
					case 'l':
					case 'm':
					case 'n':
					case 'o':
					case 'p':
					case 'q':
					case 'r':
					case 's':
					case 't':
					case 'u':
					case 'v':
					case 'w':
					case 'x':
					case 'y':
					case 'z':
						if (!customAxioms || 10u + c - 'a' > customAxioms->size())
							throw invalid_argument("DRuleParser::parseAbstractDProof(): Invalid character '" + string { c } + "': Not a proof step.");
						else if (lastDNIndex) {
							referenceIndices[nonDs] = 'a' - c - 10;
							nonDs++;
						}
						break;
					default:
						throw invalid_argument("DRuleParser::parseAbstractDProof(): Invalid character '" + string { c } + "': Not a proof step.");
					}
					if (lastOpN && nonDs == 1) { // Every "N<non-D>" that we read is a new subproof. Each "<non-D>" can be either an axiom, or a reference.
						string subProof(abstractDProofEntry.begin() + lastDNIndex, abstractDProofEntry.begin() + i + 1);
						recentDRules.emplace(subProof);
						nonDs = 0;
						lastDNIndex = 0;
					} else if (nonDs == 2) { // Every "D<non-D><non-D>" that we read is a new subproof. Each "<non-D>" can be either an axiom, or a reference.
						string subProof(abstractDProofEntry.begin() + lastDNIndex, abstractDProofEntry.begin() + i + 1);
						recentDRules.emplace(subProof);
						nonDs = 0;
						lastDNIndex = 0;
					}
				}
			}
		}
		size_t proofIndex = helperRules.size() + inOut_abstractDProof.size(); // starting index of the new stuff
		for (const string& recentExtraProof : recentDRules) {
			// Replacements in existing basic proofs
			for (vector<string>::iterator itDProof = inOut_abstractDProof.begin(); itDProof != inOut_abstractDProof.end(); ++itDProof)
				if (sufficientLen(*itDProof))
					boost::replace_all(*itDProof, recentExtraProof, "[" + to_string(proofIndex) + "]");
			// NOTE: Extra proofs are created bottom-up, i.e. they only contain a single rule (D-rule: length 3, N-rule: length 2) thus are too small for being added new references.
			proofIndex++;
		}
		// Registration of new extra proofs
		helperRules.insert(helperRules.end(), recentDRules.begin(), recentDRules.end());
	} while (!recentDRules.empty());
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to obtain " << helperRules.size() << " helper proof candidate" << (helperRules.size() == 1 ? "" : "s") << ", i.e. the minimal set of referenced proofs such that each proof contains only a single rule with inputs." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 3. Use lazy evaluation in order to determine conclusions.
	//    NOTE: At this point, all (sub)proofs in 'inOut_abstractDProof' and 'helperRules' are only single D- or N-rules with inputs. Indices in 'helperRules' are offset by |inOut_abstractDProof|.
	//          However, there now might be cross-references back and forth between proofs of both sets.
	size_t extraIndex;
	string extraId;
	vector<AxiomInfo> axBase; // for use as (1, ..., n, extra) in case there are below 35 axioms, and as (1, ..., n-1, extra) in case there are 35 axioms.
	vector<AxiomInfo> axBaseN; // for use as (1, ..., n-2, extra, n) with n, in case there are 35 axioms.
	if (customAxioms) {
		size_t n = customAxioms->size();
		axBase = *customAxioms;
		if (n == 35) {
			extraIndex = 34;
			extraId = "z";
			axBaseN = *customAxioms; // to be used by extra conclusions that combine with axiom 'z'
		} else {
			extraIndex = n;
			extraId = n < 9 ? string { char(n + '1') } : string { char(n - 9 + 'a') };
			axBase.resize(n + 1, axBase[0]); // create single slot to be used by extra conclusions
		}
	} else {
		static const vector<AxiomInfo> defaultAxioms = []() { shared_ptr<DlFormula> v0 = make_shared<DlFormula>(make_shared<String>("0")); shared_ptr<DlFormula> v1 = make_shared<DlFormula>(make_shared<String>("1")); shared_ptr<DlFormula> v2 = make_shared<DlFormula>(make_shared<String>("2")); return vector<AxiomInfo> { AxiomInfo("1", _ax1(v0, v1)), AxiomInfo("2", _ax2(v0, v1, v2)), AxiomInfo("3", _ax3(v0, v1)) }; }();
		axBase = defaultAxioms;
		extraIndex = 3;
		extraId = "4";
		axBase.resize(4, axBase[0]); // create single slot to be used by extra conclusions
	}
	vector<AxiomInfo> refBase(2, axBase[0]); // two slots to be used by extra conclusions
	out_abstractDProofConclusions = vector<shared_ptr<DlFormula>>(inOut_abstractDProof.size());
	vector<shared_ptr<DlFormula>> helperRulesConclusions(helperRules.size());
	set<size_t> indexEvalSet; // to avoid duplicate evaluation indices in case lower indices use higher indices
	vector<size_t> indexEvalSequence;
	auto parse = [&](const string& rule, size_t i, const auto& me) -> shared_ptr<DlFormula> {
		vector<DProofInfo> rawParseData;
		string::size_type pos = rule.find('[');
		if (pos == string::npos) // no references => use original axioms
			rawParseData = parseDProof_raw(rule, customAxioms);
		else {
			string::size_type posEnd = rule.find(']', pos + 1);
			if (posEnd == string::npos)
				throw invalid_argument("Missing ']' in \"" + rule + "\".");
			size_t num;
			try {
				num = stoll(rule.substr(pos + 1, posEnd - pos - 1));
			} catch (...) {
				throw invalid_argument("Bad index number in \"" + rule + "\".");
			}
			if (rule[0] == '[') { // no rule, just a redundant reference => direct build
				if (posEnd != rule.size() - 1)
					throw logic_error("First ']' should be final character in \"" + rule + "\".");
				shared_ptr<DlFormula>& f = num < inOut_abstractDProof.size() ? out_abstractDProofConclusions[num] : helperRulesConclusions[num - inOut_abstractDProof.size()];
				if (!f) // still need to parse rule at 'num'?
					f = me(num < inOut_abstractDProof.size() ? inOut_abstractDProof[num] : helperRules[num - inOut_abstractDProof.size()], num, me);
				if (optOut_indexEvalSequence && !indexEvalSet.count(i)) {
					indexEvalSequence.push_back(i);
					indexEvalSet.emplace(i);
				}
				return f;
			} else if (rule[0] == 'N') { // N-rule with no axioms, one reference => direct build
				if (posEnd != rule.size() - 1)
					throw logic_error("First ']' should be final character in \"" + rule + "\".");
				shared_ptr<DlFormula>& f = num < inOut_abstractDProof.size() ? out_abstractDProofConclusions[num] : helperRulesConclusions[num - inOut_abstractDProof.size()];
				if (!f) // still need to parse rule at 'num'?
					f = me(num < inOut_abstractDProof.size() ? inOut_abstractDProof[num] : helperRules[num - inOut_abstractDProof.size()], num, me);
				if (optOut_indexEvalSequence && !indexEvalSet.count(i)) {
					indexEvalSequence.push_back(i);
					indexEvalSet.emplace(i);
				}
				return make_shared<DlFormula>(_nece(), vector<shared_ptr<DlFormula>> { f });
			} else {
				bool refLhs = pos == 1;
				pos = rule.find('[', posEnd + 1);
				if (pos == string::npos) { // D-rule with one axiom, one reference => use axBase or axBaseN
					shared_ptr<DlFormula>& f = num < inOut_abstractDProof.size() ? out_abstractDProofConclusions[num] : helperRulesConclusions[num - inOut_abstractDProof.size()];
					if (!f) // still need to parse rule at 'num'?
						f = me(num < inOut_abstractDProof.size() ? inOut_abstractDProof[num] : helperRules[num - inOut_abstractDProof.size()], num, me);
					char axSym = refLhs ? rule[posEnd + 1] : rule[1];
					if ((axSym < '1' || axSym > '9') && (axSym < 'a' || axSym > 'z'))
						throw invalid_argument("Invalid axiom name in \"" + rule + "\".");
					size_t ax = axSym >= '1' && axSym <= '9' ? axSym - '0' : 10 + axSym - 'a';
					string rule_copy = rule;
					if (ax < 35) {
						axBase[extraIndex] = AxiomInfo("", f);
						boost::replace_all(rule_copy, "[" + to_string(num) + "]", extraId);
						rawParseData = parseDProof_raw(rule_copy, &axBase);
					} else {
						axBaseN[33] = AxiomInfo("", f);
						boost::replace_all(rule_copy, "[" + to_string(num) + "]", "y");
						rawParseData = parseDProof_raw(rule_copy, &axBaseN);
					}
				} else { // D-rule with no axioms, two references => use refBase
					string::size_type posEnd = rule.find(']', pos + 1);
					if (posEnd == string::npos)
						throw invalid_argument("Missing ']' in \"" + rule + "\".");
					size_t num2;
					try {
						num2 = stoll(rule.substr(pos + 1, posEnd - pos - 1));
					} catch (...) {
						throw invalid_argument("Bad index number in \"" + rule + "\".");
					}
					if (posEnd != rule.size() - 1)
						throw logic_error("Second ']' should be final character in \"" + rule + "\".");
					shared_ptr<DlFormula>& f1 = num < inOut_abstractDProof.size() ? out_abstractDProofConclusions[num] : helperRulesConclusions[num - inOut_abstractDProof.size()];
					if (!f1) // still need to parse rule at 'num'?
						f1 = me(num < inOut_abstractDProof.size() ? inOut_abstractDProof[num] : helperRules[num - inOut_abstractDProof.size()], num, me);
					shared_ptr<DlFormula>& f2 = num2 < inOut_abstractDProof.size() ? out_abstractDProofConclusions[num2] : helperRulesConclusions[num2 - inOut_abstractDProof.size()];
					if (!f2) // still need to parse rule at 'num2'?
						f2 = me(num2 < inOut_abstractDProof.size() ? inOut_abstractDProof[num2] : helperRules[num2 - inOut_abstractDProof.size()], num2, me);
					refBase[0] = AxiomInfo("", f1);
					refBase[1] = AxiomInfo("", f2);
					string rule_copy = rule;
					boost::replace_all(rule_copy, "[" + to_string(num) + "]", "1");
					if (num != num2)
						boost::replace_all(rule_copy, "[" + to_string(num2) + "]", "2");
					rawParseData = parseDProof_raw(rule_copy, &refBase);
					//#cout << "[#2] " << DlCore::toPolishNotation(get<0>(rawParseData.back().second).back()) << " = D<" << DlCore::toPolishNotation(f1) << "><" << DlCore::toPolishNotation(f2) << ">" << endl;
				}
			}
		}
		if (optOut_indexEvalSequence && !indexEvalSet.count(i)) {
			indexEvalSequence.push_back(i);
			indexEvalSet.emplace(i);
		}
		return get<0>(rawParseData.back().second).back();
	};
	for (size_t i = 0; i < inOut_abstractDProof.size(); i++)
		out_abstractDProofConclusions[i] = parse(inOut_abstractDProof[i], i, parse);
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to morph and parse " << inOut_abstractDProof.size() + helperRules.size() << " abstract proof" << (inOut_abstractDProof.size() + helperRules.size() == 1 ? "" : "s") << "." << endl;
		startTime = chrono::steady_clock::now();
	}
	//#cout << "\n[AFTER]\n" << FctHelper::vectorString(inOut_abstractDProof, { }, { }, "\n") << endl;
	//#cout << "\n[HELPER]\n" << FctHelper::vectorString(helperRules, { }, { }, "\n") << endl;
	//#cout << "\n[AFTER-FORMULAS]\n" << FctHelper::vectorStringF(out_abstractDProofConclusions, [](const shared_ptr<DlFormula>& f) { return f ? DlCore::toPolishNotation(f) : "null"; }, { }, { }, "\n") << endl;
	//#cout << "\n[HELPER-FORMULAS]\n" << FctHelper::vectorStringF(helperRulesConclusions, [](const shared_ptr<DlFormula>& f) { return f ? DlCore::toPolishNotation(f) : "null"; }, { }, { }, "\n") << endl;
	//#cout << "indexEvalSequence = " << FctHelper::vectorString(indexEvalSequence) << endl;

	if (optOut_helperRules)
		*optOut_helperRules = helperRules;
	if (optOut_helperRulesConclusions)
		*optOut_helperRulesConclusions = helperRulesConclusions;
	if (optOut_indexEvalSequence)
		*optOut_indexEvalSequence = indexEvalSequence;
}

vector<size_t> DRuleParser::parseValidateAndFilterAbstractDProof(vector<string>& inOut_abstractDProof, vector<shared_ptr<DlFormula>>& out_abstractDProofConclusions, vector<string>& out_helperRules, vector<shared_ptr<DlFormula>>& out_helperRulesConclusions, const vector<AxiomInfo>* customAxioms, vector<AxiomInfo>* filterForTheorems, vector<AxiomInfo>* requiredIntermediateResults, vector<size_t>* optOut_indexEvalSequence, bool debug) {
	chrono::time_point<chrono::steady_clock> startTime;
	map<size_t, set<size_t>> targetIndices_orderedByTheorems;
	parseAbstractDProof(inOut_abstractDProof, out_abstractDProofConclusions, customAxioms, &out_helperRules, &out_helperRulesConclusions, optOut_indexEvalSequence, debug);
	if (requiredIntermediateResults) {
		if (debug)
			startTime = chrono::steady_clock::now();
		if (inOut_abstractDProof.size() != requiredIntermediateResults->size())
			throw invalid_argument("|inOut_abstractDProof| = " + to_string(inOut_abstractDProof.size()) + " != " + to_string(requiredIntermediateResults->size()) + " = |requiredIntermediateResults|");
		for (size_t i = 0; i < inOut_abstractDProof.size(); i++)
			if (*out_abstractDProofConclusions[i] != *(*requiredIntermediateResults)[i].refinedAxiom) {
				if (DlCore::isSchemaOf(out_abstractDProofConclusions[i], (*requiredIntermediateResults)[i].refinedAxiom)) {
					string properSchemaStr = DlCore::toPolishNotation_noRename(out_abstractDProofConclusions[i]);
					if (debug)
						cout << "[NOTE] Index " << i << ": Resulted in proper schema " << properSchemaStr << ", requested " << (*requiredIntermediateResults)[i].name << "." << endl;
					if (filterForTheorems) { // update 'filterForTheorems' if it contains (*requiredIntermediateResults)[i]
						size_t targetIndex = SIZE_MAX;
						for (size_t j = 0; j < filterForTheorems->size(); j++)
							if (*(*filterForTheorems)[j].refinedAxiom == *(*requiredIntermediateResults)[i].refinedAxiom) {
								targetIndex = j;
								break;
							}
						if (targetIndex < SIZE_MAX) {
							cout << "[NOTE] Requested target theorem " << (*requiredIntermediateResults)[i].name << " updated to its proper schema " << properSchemaStr << "." << endl;
							(*filterForTheorems)[targetIndex] = AxiomInfo(properSchemaStr, out_abstractDProofConclusions[i]);
						}
					}
				} else
					throw invalid_argument("Validation failed for index " + to_string(i) + ": Resulted in " + DlCore::toPolishNotation_noRename(out_abstractDProofConclusions[i]) + ", but requested " + (*requiredIntermediateResults)[i].name + ".");
			}
		if (debug)
			cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to validate " << inOut_abstractDProof.size() << " conclusion" << (inOut_abstractDProof.size() == 1 ? "" : "s") << "." << endl;
	}
	if (filterForTheorems) {
		if (debug)
			startTime = chrono::steady_clock::now();
		if (filterForTheorems->empty())
			throw invalid_argument("|filterForTheorems| = 0");
		size_t i = 0;
		size_t occurrences = 0; // including duplicates
		for (const shared_ptr<DlFormula>& f : out_abstractDProofConclusions) {
			for (size_t j = 0; j < filterForTheorems->size(); j++)
				if (*f == *(*filterForTheorems)[j].refinedAxiom) {
					targetIndices_orderedByTheorems[j].emplace(i);
					occurrences++;
				}
			i++;
		}
		for (const shared_ptr<DlFormula>& f : out_helperRulesConclusions) {
			for (size_t j = 0; j < filterForTheorems->size(); j++)
				if (*f == *(*filterForTheorems)[j].refinedAxiom) {
					targetIndices_orderedByTheorems[j].emplace(i);
					occurrences++;
				}
			i++;
		}
		if (debug)
			cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to find " << occurrences << " occurrence" << (occurrences == 1 ? "" : "s") << " of " << filterForTheorems->size() << " theorem" << (filterForTheorems->size() == 1 ? "" : "s") << "." << endl;
		if (targetIndices_orderedByTheorems.size() < filterForTheorems->size())
			for (size_t j = 0; j < filterForTheorems->size(); j++)
				if (!targetIndices_orderedByTheorems.count(j))
					throw invalid_argument("Cannot find theorem " + (*filterForTheorems)[j].name + " in given proof.");
	}
	set<size_t> knownTargetIndices;
	vector<size_t> targetIndices;
	for (const pair<const size_t, set<size_t>>& p : targetIndices_orderedByTheorems)
		for (size_t i : p.second)
			if (!knownTargetIndices.count(i)) {
				targetIndices.push_back(i);
				knownTargetIndices.emplace(i);
			}
	if (targetIndices.empty())
		targetIndices.push_back(inOut_abstractDProof.size() - 1);
	return targetIndices;
}

vector<size_t> DRuleParser::measureFundamentalLengthsInAbstractDProof(const vector<size_t>& targetIndices, const vector<string>& abstractDProof, const vector<shared_ptr<DlFormula>>& abstractDProofConclusions, const vector<string>& helperRules, const vector<shared_ptr<DlFormula>>& helperRulesConclusions, bool debug, size_t limit) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	auto switchRefs = [](char& c, bool& inReference, unsigned& refIndex, const auto& inRefAction, const auto& outRefAction) {
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
				throw invalid_argument("DRuleParser::measureFundamentalLengthsInAbstractDProof(): Invalid character '" + string { c } + "': Not part of a proof reference.");
			}
		else if (c == '[')
			inReference = true;
		else
			outRefAction();
	};
	vector<size_t> storedFundamentalLengths(abstractDProof.size() + helperRules.size(), SIZE_MAX);
	auto bounded_add = [&debug](size_t a, size_t b, size_t i) { // fundamental lengths above SIZE_MAX are realistic, so avoid overflows and treat SIZE_MAX as 'SIZE_MAX and above'
		if (b > SIZE_MAX - a) {
			if (debug)
				cerr << "[WARNING] SIZE_MAX (" << SIZE_MAX << ") surpassed for index " << i << " (via " << a << " + " << b << "). Counter cannot increase further." << endl;
			return SIZE_MAX;
		}
		return a + b;
	};
	auto fundamentalLength = [&](size_t i, const auto& me) -> size_t {
		if (storedFundamentalLengths[i] != SIZE_MAX)
			return storedFundamentalLengths[i];
		const string& dProof = i < abstractDProof.size() ? abstractDProof[i] : helperRules[i - abstractDProof.size()];
		bool inReference = false;
		size_t counter = 0;
		unsigned refIndex = 0;
		for (char c : dProof)
			switchRefs(c, inReference, refIndex, [&]() {
				counter = bounded_add(counter, me(refIndex, me), i);
			}, [&]() { counter = bounded_add(counter, 1, i); });
		if (inReference)
			throw invalid_argument("DRuleParser::measureFundamentalLengthsInAbstractDProof(): Missing character ']' after '['.");
		//#if (storedFundamentalLengths[i] != SIZE_MAX)
		//#	throw logic_error("DRuleParser::measureFundamentalLengthsInAbstractDProof(): Redundant computation of fundamental length for index " + to_string(i) + ".");
		storedFundamentalLengths[i] = counter;
		return counter;
	};
	size_t sumFundamentalLength = 0;
	vector<pair<size_t, size_t>> fundamentalLengths;
	for (size_t i : targetIndices) {
		size_t l = fundamentalLength(i, fundamentalLength);
		sumFundamentalLength += l;
		fundamentalLengths.emplace_back(i, l);
	}
	if (debug) {
		long double dur = static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0;
		for (const pair<size_t, size_t>& p : fundamentalLengths) {
			size_t i = p.first;
			size_t l = p.second;
			const shared_ptr<DlFormula>& f = i < abstractDProof.size() ? abstractDProofConclusions[i] : helperRulesConclusions[i - abstractDProof.size()];
			cout << "There " << (l == 1 ? "is " : "are ") << p.second << " step" << (l == 1 ? "" : "s") << " towards " << DlCore::toPolishNotation(f) << " / " << DlCore::toPolishNotation_noRename(f) << " (index " << i << ")." << endl;
		}
		cout << FctHelper::round(dur, 2) << " ms taken to count " << sumFundamentalLength << " relevant proof step" << (sumFundamentalLength == 1 ? "" : "s") << " in total." << endl;
	}
	if (sumFundamentalLength > limit)
		throw domain_error("Limit (" + to_string(limit) + ") exceed with " + to_string(sumFundamentalLength) + " proof step" + (sumFundamentalLength == 1 ? "" : "s") + ".");
	return storedFundamentalLengths;
}

vector<string> DRuleParser::unfoldRulesInAbstractDProof(const vector<size_t>& targetIndices, const vector<string>& abstractDProof, const vector<string>& helperRules, bool debug, vector<size_t>* storedFundamentalLengths, size_t storeIntermediateUnfoldingLimit) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	auto switchRefs = [](char& c, bool& inReference, unsigned& refIndex, const auto& inRefAction, const auto& outRefAction) {
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
				throw invalid_argument("DRuleParser::unfoldRulesInAbstractDProof(): Invalid character '" + string { c } + "': Not part of a proof reference.");
			}
		else if (c == '[')
			inReference = true;
		else
			outRefAction();
	};
	set<size_t> targetIndices_lookup(targetIndices.begin(), targetIndices.end());
	// NOTE: In order to save memory, concrete D-proofs are only stored for target indices, or in case they are no longer than 'storeIntermediateUnfoldingLimit' steps.
	vector<string> targetUnfoldedProofs(targetIndices.size());
	vector<string> storedUnfoldedProofs(abstractDProof.size() + helperRules.size());
	map<size_t, size_t> indexTranslation;
	for (size_t i = 0; i < targetIndices.size(); i++) {
		size_t targetIndex = targetIndices[i];
		indexTranslation.emplace(targetIndex, i);
	}
	auto unfoldedProof = [&](size_t i, const auto& me) -> string {
		map<size_t, size_t>::const_iterator it_targetIndex = indexTranslation.find(i);
		if (it_targetIndex != indexTranslation.end()) {
			if (!targetUnfoldedProofs[it_targetIndex->second].empty())
				return targetUnfoldedProofs[it_targetIndex->second];
		} else if (!storedUnfoldedProofs[i].empty())
			return storedUnfoldedProofs[i];
		const string& dProof = i < abstractDProof.size() ? abstractDProof[i] : helperRules[i - abstractDProof.size()];
		bool inReference = false;
		string result;
		unsigned refIndex = 0;
		for (char c : dProof)
			switchRefs(c, inReference, refIndex, [&]() {
				result += me(refIndex, me);
			}, [&]() { result += string { c }; });
		if (inReference)
			throw invalid_argument("DRuleParser::unfoldRulesInAbstractDProof(): Missing character ']' after '['.");
		//#if (it_targetIndex != indexTranslation.end()) {
		//#	if (!targetUnfoldedProofs[it_targetIndex->second].empty())
		//#		throw logic_error("DRuleParser::unfoldRulesInAbstractDProof(): Redundant computation of unfolded proof for index " + to_string(i) + ".");
		//#} else if (!storedUnfoldedProofs[i].empty())
		//#	throw logic_error("DRuleParser::unfoldRulesInAbstractDProof(): Redundant computation of unfolded proof for index " + to_string(i) + ".");
		if (it_targetIndex != indexTranslation.end())
			targetUnfoldedProofs[it_targetIndex->second] = result;
		else if (!storedFundamentalLengths || (*storedFundamentalLengths)[i] <= storeIntermediateUnfoldingLimit)
			storedUnfoldedProofs[i] = result;
		return result;
	};
	for (size_t i : targetIndices)
		unfoldedProof(i, unfoldedProof);
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to unfold " << targetUnfoldedProofs.size() << " proof" << (targetUnfoldedProofs.size() == 1 ? "" : "s") << " of fundamental length" << (targetUnfoldedProofs.size() == 1 ? " " : "s ") << FctHelper::vectorStringF(targetUnfoldedProofs, [](const string& s) { return to_string(s.length()); }, { }, { }, ",") << "." << endl;
	return targetUnfoldedProofs;
}

vector<string> DRuleParser::unfoldAbstractDProof(const vector<string>& abstractDProof, const vector<AxiomInfo>* customAxioms, vector<AxiomInfo>* filterForTheorems, vector<AxiomInfo>* requiredIntermediateResults, bool debug, size_t storeIntermediateUnfoldingLimit, size_t limit) {

	// 1. Parse abstract proof (and filter towards 'filterForTheorems', and validate 'requiredIntermediateResults' if requested), and obtain indices of target theorems.
	vector<string> retractedDProof = abstractDProof;
	vector<shared_ptr<DlFormula>> abstractDProofConclusions;
	vector<string> helperRules;
	vector<shared_ptr<DlFormula>> helperRulesConclusions;
	vector<size_t> targetIndices = parseValidateAndFilterAbstractDProof(retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, customAxioms, filterForTheorems, requiredIntermediateResults, nullptr, debug);

	// 2. Measure fundamental lengths of proofs of target theorems.
	vector<size_t> storedFundamentalLengths = measureFundamentalLengthsInAbstractDProof(targetIndices, retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, debug, limit);

	// 3. Unfold proofs of target theorems.
	return unfoldRulesInAbstractDProof(targetIndices, abstractDProof, helperRules, debug, &storedFundamentalLengths, storeIntermediateUnfoldingLimit);
}

void DRuleParser::compressAbstractDProof(vector<string>& retractedDProof, vector<shared_ptr<DlFormula>>& abstractDProofConclusions, vector<string>& helperRules, vector<shared_ptr<DlFormula>>& helperRulesConclusions, vector<size_t>& indexEvalSequence, const vector<AxiomInfo>* customAxioms, bool concurrentDRuleSearch) {
	auto switchRefs = [](char& c, bool& inReference, unsigned& refIndex, const auto& inRefAction, const auto& outRefAction) {
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
				throw invalid_argument("DRuleParser::recombineAbstractDProof(): Invalid character '" + string { c } + "': Not part of a proof reference.");
			}
		else if (c == '[')
			inReference = true;
		else
			outRefAction();
	};

	// 1. Parse and store axioms and elementary proof steps.
	struct ProofElement {
		char rule; // e.g. 'D' or 'N', but also 'A' for axiom number (which also have to be checked as potential replacements)
		shared_ptr<DlFormula> result;
		array<int64_t, 2> refs; // negative: axiom number, non-negative: reference index ; uninitialized elements
		ProofElement(char c, const shared_ptr<DlFormula>& f) {
			this->rule = c;
			this->result = f;
		}
	};
	vector<ProofElement> proofElements;
	size_t numRules = retractedDProof.size() + helperRules.size();
	for (size_t i = 0; i < numRules; i++) { // store proof steps such that their positions in 'proofElements' correspond to the parsed proof
		bool isMainStep = i < retractedDProof.size();
		const string& dProof = isMainStep ? retractedDProof[i] : helperRules[i - retractedDProof.size()];
		ProofElement& e = proofElements.emplace_back(dProof[0], isMainStep ? abstractDProofConclusions[i] : helperRulesConclusions[i - retractedDProof.size()]);
		array<int64_t, 2>& refs = e.refs;
		int64_t i_refs = 0;
		bool inReference = false;
		unsigned refIndex = 0;
		for (char c : dProof)
			switchRefs(c, inReference, refIndex, [&]() {
				refs[i_refs++] = refIndex;
			}, [&]() {
				switch (c) { // NOTE: Rule symbols are ignored here; refs[1] is irrelevant for unary rules.
				case '1':
				case '2':
				case '3':
				case '4':
				case '5':
				case '6':
				case '7':
				case '8':
				case '9':
					if ((!customAxioms && c > '3') || (customAxioms && static_cast<unsigned>(c) - '0' > customAxioms->size()))
						throw invalid_argument("DRuleParser::compressAbstractDProof(): Invalid character '" + string { c } + "': Not a proof step.");
					refs[i_refs++] = '0' - c;
					break;
				case 'a':
				case 'b':
				case 'c':
				case 'd':
				case 'e':
				case 'f':
				case 'g':
				case 'h':
				case 'i':
				case 'j':
				case 'k':
				case 'l':
				case 'm':
				case 'n':
				case 'o':
				case 'p':
				case 'q':
				case 'r':
				case 's':
				case 't':
				case 'u':
				case 'v':
				case 'w':
				case 'x':
				case 'y':
				case 'z':
					if (!customAxioms || 10u + c - 'a' > customAxioms->size())
						throw invalid_argument("DRuleParser::compressAbstractDProof(): Invalid character '" + string { c } + "': Not a proof step.");
					refs[i_refs++] = 'a' - c - 10;
					break;
				}
			});
		if (inReference)
			throw invalid_argument("DRuleParser::compressAbstractDProof(): Missing character ']' after '['.");
	}
	static const vector<AxiomInfo> defaultAxioms = []() { shared_ptr<DlFormula> v0 = make_shared<DlFormula>(make_shared<String>("0")); shared_ptr<DlFormula> v1 = make_shared<DlFormula>(make_shared<String>("1")); shared_ptr<DlFormula> v2 = make_shared<DlFormula>(make_shared<String>("2")); return vector<AxiomInfo> { AxiomInfo("1", _ax1(v0, v1)), AxiomInfo("2", _ax2(v0, v1, v2)), AxiomInfo("3", _ax3(v0, v1)) }; }();
	const vector<AxiomInfo>& axioms = customAxioms ? *customAxioms : defaultAxioms;
	for (size_t i = 0; i < axioms.size(); i++) { // store axioms behind proof steps
		ProofElement& e = proofElements.emplace_back('A', axioms[i].refinedAxiom);
		e.refs[0] = -static_cast<int64_t>(i + 1);
	}
	for (size_t i = 0; i < proofElements.size(); i++) { // let conclusions have pairwise different variables (for unification)
		ProofElement& e = proofElements[i];
		shared_ptr<DlFormula>& f = e.result;
		vector<string> vars = DlCore::primitivesOfFormula_ordered(f);
		map<string, shared_ptr<DlFormula>> substitutions;
		for (const string& v : vars)
			substitutions.emplace(v, make_shared<DlFormula>(make_shared<String>(to_string(i) + "_" + v)));
		f = DlCore::substitute(f, substitutions);
	}

	bool modified = false;
	size_t compressionRound = 1;
	size_t newImprovements = 0;
	do {
		newImprovements = 0;

		// 2. Collect fundamental lengths.
		vector<size_t> allIndices(numRules);
		iota(allIndices.begin(), allIndices.end(), 0);
		vector<size_t> fundamentalLengths = measureFundamentalLengthsInAbstractDProof(allIndices, retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions);
		//#cout << "fundamentalLengths = " << FctHelper::vectorString(fundamentalLengths) << endl;
		cout << "[Proof compression (rule search), round " << compressionRound << "] Started. There are " << accumulate(fundamentalLengths.begin(), fundamentalLengths.end(), 0uLL) << " proof steps in total." << (concurrentDRuleSearch ? " Using up to " + to_string(thread::hardware_concurrency()) + " hardware thread contexts for D-rule replacement search." : "") << endl;

		// 3. Group elements based on fundamental lengths.
		map<size_t, vector<size_t>> indicesByLen;
		for (size_t i = 0; i < fundamentalLengths.size(); i++)
			indicesByLen[fundamentalLengths[i]].push_back(i);
		for (size_t i = 0; i < axioms.size(); i++)
			indicesByLen[1].push_back(fundamentalLengths.size() + i);
		//#auto infixUnicode = [](const shared_ptr<DlFormula>& f) { string s = DlCore::formulaRepresentation_traverse(f); boost::replace_all(s, DlCore::terminalStr_and(), "∧"); boost::replace_all(s, DlCore::terminalStr_or(), "∨"); boost::replace_all(s, DlCore::terminalStr_nand(), "↑"); boost::replace_all(s, DlCore::terminalStr_nor(), "↓"); boost::replace_all(s, DlCore::terminalStr_imply(), "→"); boost::replace_all(s, DlCore::terminalStr_implied(), "←"); boost::replace_all(s, DlCore::terminalStr_nimply(), "↛"); boost::replace_all(s, DlCore::terminalStr_nimplied(), "↚"); boost::replace_all(s, DlCore::terminalStr_equiv(), "↔"); boost::replace_all(s, DlCore::terminalStr_xor(), "↮"); boost::replace_all(s, DlCore::terminalStr_com(), "↷"); boost::replace_all(s, DlCore::terminalStr_app(), "↝"); boost::replace_all(s, DlCore::terminalStr_not(), "¬"); boost::replace_all(s, DlCore::terminalStr_nece(), "□"); boost::replace_all(s, DlCore::terminalStr_poss(), "◇"); boost::replace_all(s, DlCore::terminalStr_obli(), "○"); boost::replace_all(s, DlCore::terminalStr_perm(), "⌔"); boost::replace_all(s, DlCore::terminalStr_top(), "⊤"); boost::replace_all(s, DlCore::terminalStr_bot(), "⊥"); return s; };
		//#cout << "\nelementsByLen:\n" << FctHelper::mapStringF(indicesByLen, [&](const pair<const size_t, vector<size_t>>& p) { return to_string(p.first) + ": " + FctHelper::vectorStringF(p.second, [&](size_t i) { ProofElement& e = proofElements[i]; return string { e.rule } + "(" + to_string(e.refs[0]) + (e.rule == 'D' ? "," + to_string(e.refs[1]) : "") + "):" + infixUnicode(e.result); }); }, { }, { }, "\n") << endl; // DlCore::formulaRepresentation_traverse(e.result); // DlCore::toPolishNotation(e.result);
		//#cout << "\nelementsByLen:\n" << FctHelper::mapStringF(indicesByLen, [&](const pair<const size_t, vector<size_t>>& p) { return to_string(p.first) + ": " + FctHelper::vectorStringF(p.second, [&](size_t i) { ProofElement& e = proofElements[i]; return string { e.rule } + "(" + to_string(e.refs[0]) + (e.rule == 'D' ? "," + to_string(e.refs[1]) : "") + ")"; }); }, { }, { }, "\n") << endl;

		auto iToId = [&](size_t i) { if (i < numRules) return static_cast<int64_t>(i); else return -static_cast<int64_t>(i + 1 - numRules); };
		auto printIndex = [&](size_t i) {
			auto printAxiom = [](int64_t n) { if (n <= 9) return string { static_cast<char>('0' + n) }; else return string { static_cast<char>('a' + n - 10) }; };
			auto printStep = [](size_t i) { return "[" + to_string(i) + "]"; };
			int64_t id = iToId(i);
			return id < 0 ? printAxiom(-id) : printStep(i);
		};
		auto idToLen = [&](int64_t id) -> size_t { if (id < 0) return 1; else return fundamentalLengths[id]; };

		// 4. Detect and apply improving replacements of elements within this proof summary.
		//     Only looks for rules, cannot eliminate rules that are axioms. These are reported in the next step, but should be handled by the user.
		size_t fundamentalLength;
		for (map<size_t, vector<size_t>>::reverse_iterator itRev = indicesByLen.rbegin(); (fundamentalLength = itRev->first) > 1; ++itRev) { // iterate longest to shortest rules (exclude axioms, which cannot be modified)
			const vector<size_t>& indices = itRev->second;
			for (size_t i : indices) {
				ProofElement& e = proofElements[i];
				array<int64_t, 2>& refs = e.refs;
				atomic<bool> found = false;
				bool dRule = e.rule == 'D';
				bool nonMinimalD = dRule && (refs[0] >= 0 || refs[1] >= 0);
				bool nonMinimalN = !dRule && refs[0] >= 0;

				// 4.1 Look for N-rules as replacements (if applicable).
				if (e.result->getChildren().size() == 1 && e.result->getValue()->value == DlCore::terminalStr_nece() && (dRule || nonMinimalN)) {
					const shared_ptr<DlFormula>& e_child = e.result->getChildren()[0];
					for (map<size_t, vector<size_t>>::iterator itFwdA = indicesByLen.begin(); itFwdA != indicesByLen.end(); ++itFwdA) {
						size_t candidateAFundamentalLength = itFwdA->first;
						if (candidateAFundamentalLength + 1 >= fundamentalLength) // only shorter alternatives are tested
							break;
						for (size_t iA : itFwdA->second) {
							ProofElement& eA = proofElements[iA];
							const shared_ptr<DlFormula>& input = eA.result;
							if (DlCore::isSchemaOf(input, e_child)) {
								bool isMainStep = i < retractedDProof.size();
								if (!DlCore::isSchemaOf(e_child, input)) { // 'e.result' needs to be modified
									shared_ptr<DlFormula> consequent;
									DlCore::fromPolishNotation_noRename(consequent, "L" + DlCore::toPolishNotation_numVars(input));
									(isMainStep ? abstractDProofConclusions[i] : helperRulesConclusions[i - retractedDProof.size()]) = consequent; // update 'abstractDProofConclusions' or 'helperRulesConclusions'
									vector<string> vars = DlCore::primitivesOfFormula_ordered(consequent);
									map<string, shared_ptr<DlFormula>> substitutions;
									for (const string& v : vars)
										substitutions.emplace(v, make_shared<DlFormula>(make_shared<String>(to_string(i) + "_" + v)));
									consequent = DlCore::substitute(consequent, substitutions);
									cout << "[Proof compression (rule search), round " << compressionRound << "] Step [" << i << "]'s consequent changed from " << DlCore::toPolishNotation(e.result) << " to " << DlCore::toPolishNotation(consequent) << "." << endl; //DlCore::formulaRepresentation_traverse(e.result)
									e.result = consequent;
								}
								string& dProof = isMainStep ? retractedDProof[i] : helperRules[i - retractedDProof.size()];
								string newDProof = "N" + printIndex(iA);
								if (dRule) {
									cout << "[Proof compression (rule search), round " << compressionRound << "] D-step [" << i << "] improved from " << dProof << " (1+" << idToLen(e.refs[0]) << "+" << idToLen(e.refs[1]) << " = " << fundamentalLength << " steps) to " << newDProof << " (1+" << candidateAFundamentalLength << " = " << candidateAFundamentalLength + 1 << " steps). [" << DlCore::toPolishNotation(e.result) << "]" << endl;
									e.rule = 'N';
								} else
									cout << "[Proof compression (rule search), round " << compressionRound << "] N-step [" << i << "] improved from " << dProof << " (1+" << idToLen(e.refs[0]) << " = " << fundamentalLength << " steps) to " << newDProof << " (1+" << candidateAFundamentalLength << " = " << candidateAFundamentalLength + 1 << " steps). [" << DlCore::toPolishNotation(e.result) << "]" << endl;
								e.refs[0] = iToId(iA);
								dProof = newDProof; // update 'retractedDProof' or 'helperRules'
								fundamentalLengths[i] = candidateAFundamentalLength + 1; // also update 'fundamentalLengths', so the rule can possibly still be used in this compression round
								modified = true;
								newImprovements++;
								found = true;
								break;
							}
						}
						if (found)
							break;
					}
					if (found)
						continue;
				}

				// 4.2 Look for D-rules as replacements. ; NOTE: When parallelized, the solution procedure is not deterministic anymore.
				mutex mtx;
				auto searchDRuleReplacement = [&](const pair<const size_t, vector<size_t>>& fwdA, const size_t candidateAFundamentalLength) {
					// Unmodified captures: &compressionRound, &dRule, &fundamentalLength, &i, &indicesByLen, &iToId, &idToLen, &printIndex, &proofElements
					// Modifiable captures: &abstractDProofConclusions, &e, &found, &fundamentalLengths, &helperRules, &helperRulesConclusions, &modified, &mtx, &newImprovements, &retractedDProof
					for (map<size_t, vector<size_t>>::iterator itFwdB = indicesByLen.begin(); itFwdB != indicesByLen.end(); ++itFwdB) {
						size_t candidateBFundamentalLength = itFwdB->first;
						if (candidateAFundamentalLength + candidateBFundamentalLength + 1 >= fundamentalLength) // only shorter alternatives are tested
							return;
						for (size_t iA : fwdA.second) {
							for (size_t iB : itFwdB->second) {
								const ProofElement& eB = proofElements[iB]; // NOTE: 'e' might be modified concurrently, but eB != e = proofElements[i], since 'e' is fundamentally longer than 'eB'.
								const shared_ptr<DlFormula>& conditional = eB.result;
								const vector<shared_ptr<DlFormula>>& conditional_children = conditional->getChildren();
								if (conditional_children.size() != 2 || conditional->getValue()->value != DlCore::terminalStr_imply())
									continue;
								const ProofElement& eA = proofElements[iA]; // NOTE: 'e' might be modified concurrently, but eA != e = proofElements[i], since 'e' is fundamentally longer than 'eA'.
								// For special case: When itFwdA == itFwdB and iA == iB, a formula is unified with itself, thus there needs to be an extra separation of variables.
								shared_ptr<DlFormula> _distinguishedFormula;
								auto distinguishVariables = [&](const shared_ptr<DlFormula>& f) -> const shared_ptr<DlFormula>& {
									vector<string> vars = DlCore::primitivesOfFormula_ordered(f);
									map<string, shared_ptr<DlFormula>> substitutions;
									for (const string& v : vars)
										substitutions.emplace(v, make_shared<DlFormula>(make_shared<String>(v + "_")));
									_distinguishedFormula = DlCore::substitute(f, substitutions);
									return _distinguishedFormula;
								};
								const shared_ptr<DlFormula>& antecedent = &fwdA == &*itFwdB && iA == iB ? distinguishVariables(eA.result) : eA.result;
								map<string, shared_ptr<DlFormula>> substitutions;
								if (!found && DlCore::tryUnifyTrees(antecedent, conditional_children[0], &substitutions)) {
									shared_ptr<DlFormula> consequent = DlCore::substitute(conditional_children[1], substitutions);
									if (!found && DlCore::isSchemaOf(consequent, e.result)) {
										if (!found) {
											lock_guard<mutex> lock(mtx);
											if (!found) {
												found = true;
												bool isMainStep = i < retractedDProof.size();
												if (!DlCore::isSchemaOf(e.result, consequent)) { // 'e.result' needs to be modified
													DlCore::fromPolishNotation_noRename(consequent, DlCore::toPolishNotation_numVars(consequent));
													(isMainStep ? abstractDProofConclusions[i] : helperRulesConclusions[i - retractedDProof.size()]) = consequent; // update 'abstractDProofConclusions' or 'helperRulesConclusions'
													vector<string> vars = DlCore::primitivesOfFormula_ordered(consequent);
													map<string, shared_ptr<DlFormula>> substitutions;
													for (const string& v : vars)
														substitutions.emplace(v, make_shared<DlFormula>(make_shared<String>(to_string(i) + "_" + v)));
													consequent = DlCore::substitute(consequent, substitutions);
													cout << "[Proof compression (rule search), round " << compressionRound << "] Step [" << i << "]'s consequent changed from " << DlCore::toPolishNotation(e.result) << " to " << DlCore::toPolishNotation(consequent) << "." << endl; //DlCore::formulaRepresentation_traverse(e.result)
													e.result = consequent;
												}
												string& dProof = isMainStep ? retractedDProof[i] : helperRules[i - retractedDProof.size()];
												string newDProof = "D" + printIndex(iB) + printIndex(iA);
												if (dRule)
													cout << "[Proof compression (rule search), round " << compressionRound << "] D-step [" << i << "] improved from " << dProof << " (1+" << idToLen(e.refs[0]) << "+" << idToLen(e.refs[1]) << " = " << fundamentalLength << " steps) to " << newDProof << " (1+" << candidateBFundamentalLength << "+" << candidateAFundamentalLength << " = " << candidateAFundamentalLength + candidateBFundamentalLength + 1 << " steps). [" << DlCore::toPolishNotation(e.result) << "]" << endl;
												else {
													cout << "[Proof compression (rule search), round " << compressionRound << "] N-step [" << i << "] improved from " << dProof << " (1+" << idToLen(e.refs[0]) << " = " << fundamentalLength << " steps) to " << newDProof << " (1+" << candidateBFundamentalLength << "+" << candidateAFundamentalLength << " = " << candidateAFundamentalLength + candidateBFundamentalLength + 1 << " steps). [" << DlCore::toPolishNotation(e.result) << "]" << endl;
													e.rule = 'D';
												}
												e.refs[0] = iToId(iB);
												e.refs[1] = iToId(iA);
												dProof = newDProof; // update 'retractedDProof' or 'helperRules'
												fundamentalLengths[i] = candidateAFundamentalLength + candidateBFundamentalLength + 1; // also update 'fundamentalLengths', so the rule can possibly still be used in this compression round
												modified = true;
												newImprovements++;
												return;
											}
										} else
											return;
									}
								}
								if (found)
									return;
							}
							if (found)
								return;
						}
						if (found)
							return;
					}
				};
				if (nonMinimalD || nonMinimalN) { // NOTE: Even an axiom should be replaced when the other input is a rule no shorter than two alternative inputs combined).
					if (concurrentDRuleSearch)
						tbb::parallel_for_each(indicesByLen.begin(), indicesByLen.end(), [&](const pair<const size_t, vector<size_t>>& fwdA) {
							if (found)
								return;
							size_t candidateAFundamentalLength = fwdA.first;
							if (candidateAFundamentalLength + 2 >= fundamentalLength) // only shorter alternatives are tested
								return;
							searchDRuleReplacement(fwdA, candidateAFundamentalLength);
						});
					else
						for (map<size_t, vector<size_t>>::iterator itFwdA = indicesByLen.begin(); itFwdA != indicesByLen.end(); ++itFwdA) {
							size_t candidateAFundamentalLength = itFwdA->first;
							if (candidateAFundamentalLength + 2 >= fundamentalLength) // only shorter alternatives are tested
								break;
							searchDRuleReplacement(*itFwdA, candidateAFundamentalLength);
							if (found)
								break;
						}
				}
			}
		}

		// 5. Detect and report trivial rules.
		for (size_t i = 0; i < numRules; i++) {
			ProofElement& rule = proofElements[i];
			for (size_t a = 0; a < axioms.size(); a++) {
				ProofElement& axiom = proofElements[numRules + a];
				if (DlCore::isSchemaOf(axiom.result, rule.result))
					cout << "[Proof compression (axiom search), round " << compressionRound << "] NOTE: [" << i << "]:" << DlCore::toPolishNotation(rule.result) << " is an instance of axiom number " << a << ". [" << DlCore::toPolishNotation(axiom.result) << "]" << endl;
			}
		}

		cout << "[Proof compression (rule search), round " << compressionRound << "] Complete. Applied " << newImprovements << " shortening replacement" << (newImprovements == 1 ? "" : "s") << "." << endl;
		compressionRound++;
	} while (newImprovements);

	// 6. Rebuild 'indexEvalSequence' (if some rules changed).
	if (modified) {
		vector<size_t> newIndexEvalSequence;
		set<size_t> registered;
		set<size_t> explored;

		// Similar to 'auto parse' in DRuleParser::parseAbstractDProof(), but everything is parsed already.
		// Additionally, need to avoid duplicate registration of evaluation indices, which here could occur due to non-orderliness of the input.
		auto explore = [&](const string& rule, size_t i, const auto& me) -> void {
			vector<DProofInfo> rawParseData;
			string::size_type pos = rule.find('[');
			if (pos != string::npos) {
				string::size_type posEnd = rule.find(']', pos + 1);
				if (posEnd == string::npos)
					throw invalid_argument("Missing ']' in \"" + rule + "\".");
				size_t num;
				try {
					num = stoll(rule.substr(pos + 1, posEnd - pos - 1));
				} catch (...) {
					throw invalid_argument("Bad index number in \"" + rule + "\".");
				}
				if (rule[0] == 'N') { // N-rule with no axioms, one reference
					if (posEnd != rule.size() - 1)
						throw logic_error("First ']' should be final character in \"" + rule + "\".");
					if (!explored.count(num)) { // still need to explore rule at 'num'?
						me(num < retractedDProof.size() ? retractedDProof[num] : helperRules[num - retractedDProof.size()], num, me);
						explored.emplace(num);
					}
					if (!registered.count(i)) {
						newIndexEvalSequence.push_back(i);
						registered.emplace(i);
					}
					return;
				} else {
					bool refLhs = pos == 1;
					pos = rule.find('[', posEnd + 1);
					if (pos == string::npos) { // D-rule with one axiom, one reference
						if (!explored.count(num)) { // still need to explore rule at 'num'?
							me(num < retractedDProof.size() ? retractedDProof[num] : helperRules[num - retractedDProof.size()], num, me);
							explored.emplace(num);
						}
						char axSym = refLhs ? rule[posEnd + 1] : rule[1];
						if ((axSym < '1' || axSym > '9') && (axSym < 'a' || axSym > 'z'))
							throw invalid_argument("Invalid axiom name in \"" + rule + "\".");
					} else { // D-rule with no axioms, two references
						string::size_type posEnd = rule.find(']', pos + 1);
						if (posEnd == string::npos)
							throw invalid_argument("Missing ']' in \"" + rule + "\".");
						size_t num2;
						try {
							num2 = stoll(rule.substr(pos + 1, posEnd - pos - 1));
						} catch (...) {
							throw invalid_argument("Bad index number in \"" + rule + "\".");
						}
						if (posEnd != rule.size() - 1)
							throw logic_error("Second ']' should be final character in \"" + rule + "\".");
						if (!explored.count(num)) { // still need to explore rule at 'num'?
							me(num < retractedDProof.size() ? retractedDProof[num] : helperRules[num - retractedDProof.size()], num, me);
							explored.emplace(num);
						}
						if (!explored.count(num2)) { // still need to explore rule at 'num2'?
							me(num2 < retractedDProof.size() ? retractedDProof[num2] : helperRules[num2 - retractedDProof.size()], num2, me);
							explored.emplace(num2);
						}
					}
				}
			}
			if (!registered.count(i)) {
				newIndexEvalSequence.push_back(i);
				registered.emplace(i);
			}
		};
		for (size_t i = 0; i < retractedDProof.size(); i++)
			explore(retractedDProof[i], i, explore);
		indexEvalSequence = newIndexEvalSequence;
	}
}

vector<string> DRuleParser::recombineAbstractDProof(const vector<string>& abstractDProof, vector<shared_ptr<DlFormula>>& out_conclusions, const vector<AxiomInfo>* customAxioms, vector<AxiomInfo>* filterForTheorems, const vector<AxiomInfo>* conclusionsWithHelperProofs, unsigned minUseAmountToCreateHelperProof, vector<AxiomInfo>* requiredIntermediateResults, bool debug, size_t maxLengthToKeepProof, bool abstractProofStrings, size_t storeIntermediateUnfoldingLimit, size_t limit, bool removeDuplicateConclusions, bool compress, bool compress_concurrentDRuleSearch) {
	chrono::time_point<chrono::steady_clock> startTime;
	auto switchRefs = [](char& c, bool& inReference, unsigned& refIndex, const auto& inRefAction, const auto& outRefAction) {
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
				throw invalid_argument("DRuleParser::recombineAbstractDProof(): Invalid character '" + string { c } + "': Not part of a proof reference.");
			}
		else if (c == '[')
			inReference = true;
		else
			outRefAction();
	};

	// 1. Parse abstract proof (and filter towards 'filterForTheorems', and validate 'requiredIntermediateResults' if requested), and obtain indices of target theorems.
	vector<string> retractedDProof = abstractDProof;
	vector<shared_ptr<DlFormula>> abstractDProofConclusions;
	vector<string> helperRules;
	vector<shared_ptr<DlFormula>> helperRulesConclusions;
	vector<size_t> indexEvalSequence;
	vector<size_t> targetIndices = parseValidateAndFilterAbstractDProof(retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, customAxioms, filterForTheorems, requiredIntermediateResults, &indexEvalSequence, debug);
	{
		// Duplicates in and order of 'filterForTheorems' are irrelevant for recombination => Order indices and remove duplicates.
		set<size_t> targetIndices_noDuplicates(targetIndices.begin(), targetIndices.end());
		targetIndices = vector<size_t>(targetIndices_noDuplicates.begin(), targetIndices_noDuplicates.end());
	}

#if 0 //###
	{
		size_t index = 0;
		cout << "\nretractedDProof:\n" << FctHelper::vectorStringF(retractedDProof, [&](const string& s) { return "[" + to_string(index++) + "] " + s; }, { }, { }, "\n") << endl;
		cout << "\nhelperRules:\n" << FctHelper::vectorStringF(helperRules, [&](const string& s) { return "[" + to_string(index++) + "] " + s; }, { }, { }, "\n") << endl;
		index = 0;
		cout << "\nabstractDProofConclusions:\n" << FctHelper::vectorStringF(abstractDProofConclusions, [&](const shared_ptr<DlFormula>& f) { return "[" + to_string(index++) + "] " + (f ? DlCore::toPolishNotation(f) : "null"); }, { }, { }, "\n") << endl;
		cout << "\nhelperRulesConclusions:\n" << FctHelper::vectorStringF(helperRulesConclusions, [&](const shared_ptr<DlFormula>& f) { return "[" + to_string(index++) + "] " + (f ? DlCore::toPolishNotation(f) : "null"); }, { }, { }, "\n") << endl;
		cout << "indexEvalSequence = " << FctHelper::vectorString(indexEvalSequence) << endl;
		cout << "targetIndices = " << FctHelper::vectorString(targetIndices) << endl;
	}
#endif //###

	// 2. Remove duplicate conclusions from the input (if requested).
	if (removeDuplicateConclusions) {

		// 2.1 Remove duplicates from target theorem list (if available).
		vector<AxiomInfo>* newFilterForTheorems = filterForTheorems;
		vector<AxiomInfo> _newFilterForTheorems;
		if (filterForTheorems) { // NOTE: Do not modify 'filterForTheorems', since it may share its address with 'requiredIntermediateResults'.
			if (debug)
				startTime = chrono::steady_clock::now();
			map<string, size_t, cmpStringGrow> formulaAmounts;
			set<size_t> duplicateIndices;
			size_t duplicateCounter = 0;
			for (size_t i = 0; i < filterForTheorems->size(); i++)
				if (formulaAmounts[DlCore::toPolishNotation_noRename((*filterForTheorems)[i].refinedAxiom)]++) {
					duplicateCounter++;
					duplicateIndices.emplace(i);
				}
			if (!duplicateIndices.empty()) {
				for (size_t i = 0; i < filterForTheorems->size(); i++)
					if (!duplicateIndices.count(i))
						_newFilterForTheorems.push_back((*filterForTheorems)[i]);
				newFilterForTheorems = &_newFilterForTheorems;
				if (debug)
					cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to detect and remove " << duplicateIndices.size() << " duplicate" << (duplicateIndices.size() == 1 ? "" : "s") << " from list of target theorems." << endl;
			}

		}

		// 2.2 Find duplicate conclusions of D-proofs.
		vector<set<size_t>> duplicateIndexSets;
		{
			if (debug)
				startTime = chrono::steady_clock::now();
			map<string, set<size_t>, cmpStringGrow> formulaOccurrences;
			size_t duplicateCounter = 0;
			for (size_t i = 0; i < abstractDProofConclusions.size(); i++) {
				set<size_t>& entry = formulaOccurrences[DlCore::toPolishNotation_noRename(abstractDProofConclusions[i])];
				entry.emplace(i);
				if (entry.size() > 1)
					duplicateCounter++;
			}
			for (size_t i = 0; i < helperRulesConclusions.size(); i++) {
				set<size_t>& entry = formulaOccurrences[DlCore::toPolishNotation_noRename(helperRulesConclusions[i])];
				entry.emplace(abstractDProofConclusions.size() + i);
				if (entry.size() > 1)
					duplicateCounter++;
			}
			if (debug)
				cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to detect " << duplicateCounter << " duplicate conclusion" << (duplicateCounter == 1 ? "" : "s") << " in extended proof summary." << endl;
			for (const pair<const string, set<size_t>>& p : formulaOccurrences)
				if (p.second.size() > 1)
					duplicateIndexSets.push_back(p.second);
		}
		//#cout << "duplicateIndexSets = " << FctHelper::vectorStringF(duplicateIndexSets, [](const set<size_t>& s) { return FctHelper::setString(s); }) << endl;
		vector<size_t> duplicateIndices;
		for (const set<size_t>& s : duplicateIndexSets)
			duplicateIndices.insert(duplicateIndices.end(), s.begin(), s.end());
		vector<size_t> storedFundamentalLengths = measureFundamentalLengthsInAbstractDProof(duplicateIndices, retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, debug);

		if (!duplicateIndexSets.empty()) { // filter only if there are duplicates
			if (debug)
				startTime = chrono::steady_clock::now();

			// 2.3 Find index translation and indices to skip.
			map<size_t, size_t> indexTranslation;
			unordered_set<size_t> obsoleteIndices;
			{
				// 2.3.1 Find indices to remove and their replacements.
				map<size_t, size_t> replacements;
				for (const set<size_t>& s : duplicateIndexSets) {
					size_t bestIndex = *s.begin();
					size_t minLen = storedFundamentalLengths[bestIndex];
					for (set<size_t>::const_iterator it = next(s.begin()); it != s.end(); ++it) {
						size_t len = storedFundamentalLengths[*it];
						if (len < minLen) {
							bestIndex = *it;
							minLen = len;
						}
					}
					for (size_t i : s)
						if (i != bestIndex) {
							replacements.emplace(i, bestIndex);
							obsoleteIndices.emplace(i);
						}
				}

				// 2.3.2 Build index translation based on removals and replacements.
				bool shift = false;
				size_t offset = 0;
				for (size_t i = 0; i < retractedDProof.size() + helperRules.size(); i++)
					if (obsoleteIndices.count(i))
						shift = true;
					else if (shift)
						indexTranslation.emplace(i, indexTranslation.size() + offset);
					else
						offset++;
				for (size_t i = 0; i < retractedDProof.size() + helperRules.size(); i++) {
					map<size_t, size_t>::const_iterator itReplacement = replacements.find(i);
					if (itReplacement != replacements.end()) {
						size_t replacingIndex = itReplacement->second;
						map<size_t, size_t>::const_iterator itShift = indexTranslation.find(replacingIndex);
						indexTranslation.emplace(i, itShift == indexTranslation.end() ? replacingIndex : itShift->second);
					}
				}
			}

			// 2.4 Update proof.
			vector<AxiomInfo>* newRequiredIntermediateResults = requiredIntermediateResults;
			vector<AxiomInfo> _newRequiredIntermediateResults;
			{
				// 2.4.1 Build new abstract proof.
				vector<string> newAbstractDProof;
				for (size_t i = 0; i < retractedDProof.size() + helperRules.size(); i++)
					if (!obsoleteIndices.count(i)) {
						const string& dProof = i < retractedDProof.size() ? retractedDProof[i] : helperRules[i - retractedDProof.size()];
						bool inReference = false;
						string result;
						unsigned refIndex = 0;
						for (char c : dProof)
							switchRefs(c, inReference, refIndex, [&]() {
								map<size_t, size_t>::const_iterator itShift = indexTranslation.find(refIndex);
								result += "[" + to_string(itShift == indexTranslation.end() ? refIndex : itShift->second) + "]";
							}, [&]() { result += string { c }; });
						if (inReference)
							throw invalid_argument("DRuleParser::recombineAbstractDProof(): Missing character ']' after '['.");
						newAbstractDProof.push_back(result);
					}
				retractedDProof = newAbstractDProof;

				// 2.4.2 Update conclusions for validation (if available).
				if (requiredIntermediateResults) { // NOTE: Do not modify 'requiredIntermediateResults', since it may share its address with 'filterForTheorems'.
					for (size_t i = 0; i < requiredIntermediateResults->size(); i++)
						if (!obsoleteIndices.count(i))
							_newRequiredIntermediateResults.push_back((*requiredIntermediateResults)[i]);
					for (size_t i = 0; i < helperRulesConclusions.size(); i++) // add missing helper conclusions
						if (!obsoleteIndices.count(abstractDProofConclusions.size() + i)) {
							const shared_ptr<DlFormula>& f = helperRulesConclusions[i];
							_newRequiredIntermediateResults.push_back(DRuleParser::AxiomInfo(DlCore::toPolishNotation_noRename(f), f));
						}
					newRequiredIntermediateResults = &_newRequiredIntermediateResults;
				}
			}
			if (debug)
				cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to morph proof summary such that subproofs with redundant conclusions (except first shortest subproofs) are removed." << endl;
			cout << "Going to parse modified proof summary with " << obsoleteIndices.size() << " removed duplicate conclusion" << (obsoleteIndices.size() == 1 ? "" : "s") << "." << endl;

			// 2.4.3 Parse and verify new abstract proof (and update all the extra information).
			// NOTE: Essentially parseAbstractDProof(retractedDProof, abstractDProofConclusions, customAxioms, &helperRules, &helperRulesConclusions, &indexEvalSequence, debug)
			//                   with validation, target theorem checks and index updates.
			targetIndices = parseValidateAndFilterAbstractDProof(retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, customAxioms, newFilterForTheorems, newRequiredIntermediateResults, &indexEvalSequence, debug);
			{
				// Order of 'newFilterForTheorems' is irrelevant for recombination => Order indices and remove duplicates.
				set<size_t> targetIndices_noDuplicates(targetIndices.begin(), targetIndices.end());
				targetIndices = vector<size_t>(targetIndices_noDuplicates.begin(), targetIndices_noDuplicates.end());
			}
		}

#if 0 //###
		size_t index = 0;
		cout << "\nretractedDProof:\n" << FctHelper::vectorStringF(retractedDProof, [&](const string& s) { return "[" + to_string(index++) + "] " + s; }, { }, { }, "\n") << endl;
		cout << "\nhelperRules:\n" << FctHelper::vectorStringF(helperRules, [&](const string& s) { return "[" + to_string(index++) + "] " + s; }, { }, { }, "\n") << endl;
		index = 0;
		cout << "\nabstractDProofConclusions:\n" << FctHelper::vectorStringF(abstractDProofConclusions, [&](const shared_ptr<DlFormula>& f) { return "[" + to_string(index++) + "] " + (f ? DlCore::toPolishNotation(f) : "null"); }, { }, { }, "\n") << endl;
		cout << "\nhelperRulesConclusions:\n" << FctHelper::vectorStringF(helperRulesConclusions, [&](const shared_ptr<DlFormula>& f) { return "[" + to_string(index++) + "] " + (f ? DlCore::toPolishNotation(f) : "null"); }, { }, { }, "\n") << endl;
		cout << "indexEvalSequence = " << FctHelper::vectorString(indexEvalSequence) << endl;
		cout << "targetIndices = " << FctHelper::vectorString(targetIndices) << endl;
#endif //###

	}

	// 3. Compress proof summary (if requested).
	if (compress) {
		// NOTE: At this point, the variables 'retractedDProof', 'helperRules', 'abstractDProofConclusions', 'helperRulesConclusions', and 'indexEvalSequence' encode a fully detailed
		//       proof summary (as if '-j 1'), where ('retractedDProof', 'abstractDProofConclusions') contain rules and conclusions of the proof summary provided by the user,
		//       ('helperRules', 'helperRulesConclusions') contain rules and conclusions that have been extracted from steps with more than one rule,
		//       and 'indexEvalSequence' provides a rule evaluation sequence respecting dependencies between the rules.
		//       For proof compression, we can now operate over this fully detailed proof summary in order to remove the kind of internal redundancy where other parts
		//       of the summary provide a shorter alternative subproof at any position.
		compressAbstractDProof(retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, indexEvalSequence, customAxioms, compress_concurrentDRuleSearch);
	}

	// 4. Recombine abstract proof (bounded by 'targetIndices'), w.r.t. 'conclusionsWithHelperProofs', 'minUseAmountToCreateHelperProof', and 'maxLengthToKeepProof'.
	set<size_t> dedicatedIndices;
	{
		// 4.1 Remove proofs with fundamental lengths above 'maxLengthToKeepProof' (if requested).
		if (maxLengthToKeepProof < SIZE_MAX) {
			vector<size_t> storedFundamentalLengths = measureFundamentalLengthsInAbstractDProof(targetIndices, retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, debug);
			set<size_t> toRemove;
			for (size_t i = 0; i < targetIndices.size(); i++) {
				size_t targetIndex = targetIndices[i];
				if (storedFundamentalLengths[targetIndex] > maxLengthToKeepProof)
					toRemove.emplace(i);
			}
			for (set<size_t>::reverse_iterator it = toRemove.rbegin(); it != toRemove.rend(); ++it)
				targetIndices.erase(targetIndices.begin() + *it);
			if (!toRemove.empty()) {
				if (debug)
					cout << "Removed " << toRemove.size() << " target theorem" << (toRemove.size() == 1 ? "" : "s") << " due to having " << (toRemove.size() == 1 ? "a proof" : "proofs") << " longer than " << maxLengthToKeepProof << " step" << (maxLengthToKeepProof == 1 ? "" : "s") << ". Still relevant: " << FctHelper::vectorString(targetIndices) << endl;
				if (targetIndices.empty())
					throw domain_error("None of the specified theorems are proven in at most " + to_string(maxLengthToKeepProof) + " step" + (maxLengthToKeepProof == 1 ? "" : "s") + ".");
			}
		}

		// 4.2 Collect indices that are referenced by relevant indices.
		if (debug)
			startTime = chrono::steady_clock::now();
		set<size_t> referencedIndices;
		auto collectRefIndices = [&](size_t i, const auto& me) {
			if (referencedIndices.count(i))
				return;
			const string& dProof = i < retractedDProof.size() ? retractedDProof[i] : helperRules[i - retractedDProof.size()];
			bool inReference = false;
			unsigned refIndex = 0;
			for (char c : dProof)
				switchRefs(c, inReference, refIndex, [&]() {
					me(refIndex, me);
				}, [&]() { });
			if (inReference)
				throw invalid_argument("DRuleParser::recombineAbstractDProof(): Missing character ']' after '['.");
			//#if (referencedIndices.count(i))
			//#	throw logic_error("DRuleParser::recombineAbstractDProof(): Redundant collection of index " + to_string(i) + ".");
			referencedIndices.emplace(i);
		};
		for (size_t i : targetIndices)
			collectRefIndices(i, collectRefIndices);
		if (debug) {
			cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to obtain " << referencedIndices.size() << " referenced " << (referencedIndices.size() == 1 ? "index" : "indices") << "." << endl;
			startTime = chrono::steady_clock::now();
		}

		// 4.3 Determine which referenced indices should obtain their own lines according to targetIndices', 'minUseAmountToCreateHelperProof' and 'conclusionsWithHelperProofs'.
		if (minUseAmountToCreateHelperProof > 1) {

			// 4.3.1 Add 'targetIndices' (i.e. according to 'filterForTheorems' if requested, final conclusion otherwise) and indices according to 'conclusionsWithHelperProofs' (if requested).
			dedicatedIndices = set<size_t>(targetIndices.begin(), targetIndices.end());
			if (conclusionsWithHelperProofs) {
				for (size_t i : referencedIndices) {
					const shared_ptr<DlFormula>& f = i < retractedDProof.size() ? abstractDProofConclusions[i] : helperRulesConclusions[i - retractedDProof.size()];
					for (const AxiomInfo& info : *conclusionsWithHelperProofs)
						if (*f == *info.refinedAxiom) {
							dedicatedIndices.emplace(i);
							break;
						}
				}
			}

			// 4.3.2 Add indices which are referenced at least 'minUseAmountToCreateHelperProof' times.
			if (minUseAmountToCreateHelperProof != UINT_MAX) {
				map<size_t, unsigned> referenceAmounts; // index of proof -> amount of references to proof
				auto findReferences = [&](const string& dProof) {
					bool inReference = false;
					unsigned refIndex = 0;
					for (char c : dProof)
						switchRefs(c, inReference, refIndex, [&]() {
							referenceAmounts[refIndex]++;
						}, []() { });
				};
				for (size_t i : referencedIndices)
					findReferences(i < retractedDProof.size() ? retractedDProof[i] : helperRules[i - retractedDProof.size()]);
				for (const pair<const size_t, unsigned>& p : referenceAmounts)
					if (p.second >= minUseAmountToCreateHelperProof)
						dedicatedIndices.emplace(p.first);
			}
		} else
			dedicatedIndices = referencedIndices;
		if (debug) {
			cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to obtain " << dedicatedIndices.size() << " dedicated " << (dedicatedIndices.size() == 1 ? "index" : "indices") << "." << endl;
			startTime = chrono::steady_clock::now();
		}
	}

	// 5. Build new abstract proof
	vector<size_t> indicesForNewProof;
	map<size_t, size_t> indexTranslation;
	for (size_t i : indexEvalSequence)
		if (dedicatedIndices.count(i)) {
			indexTranslation.emplace(i, indicesForNewProof.size());
			indicesForNewProof.push_back(i);
		}
	vector<string> newAbstractDProof;
	if (!out_conclusions.empty())
		out_conclusions.clear();
	if (abstractProofStrings && indicesForNewProof.size() > 1) {

		// 5.1 Extend rules for referenced indices that are not dedicated, and translate referenced indices that are dedicated.
		set<size_t> extendedIndices;
		size_t sumCharLength = 0;
		auto extendAndTranslateProof = [&](size_t i, const auto& me) -> const string& {
			string& dProof = i < retractedDProof.size() ? retractedDProof[i] : helperRules[i - retractedDProof.size()];
			if (extendedIndices.count(i))
				return dProof;
			bool inReference = false;
			string result;
			unsigned refIndex = 0;
			for (char c : dProof)
				switchRefs(c, inReference, refIndex, [&]() {
					if (dedicatedIndices.count(refIndex))
						result += "[" + to_string(indexTranslation[refIndex]) + "]";
					else
						result += me(refIndex, me);
				}, [&]() { result += string { c }; });
			if (inReference)
				throw invalid_argument("DRuleParser::recombineAbstractDProof(): Missing character ']' after '['.");
			//#if (extendedIndices.count(i))
			//#	throw logic_error("DRuleParser::recombineAbstractDProof(): Redundant computation of extended proof for index " + to_string(i) + ".");
			if (dedicatedIndices.count(i))
				sumCharLength += result.length();
			if (sumCharLength > limit)
				throw domain_error("Limit (" + to_string(limit) + ") exceed with at least " + to_string(sumCharLength) + " byte" + (sumCharLength == 1 ? "" : "s") + " in abstract proofs.");
			extendedIndices.emplace(i);
			dProof = result;
			return dProof;
		};
		for (size_t i : dedicatedIndices)
			extendAndTranslateProof(i, extendAndTranslateProof);

		// 5.2 Add transformed rules to new proof.
		for (size_t i : indicesForNewProof) {
			string& dProof = i < retractedDProof.size() ? retractedDProof[i] : helperRules[i - retractedDProof.size()];
			newAbstractDProof.push_back(dProof);
			dProof.clear();
			const shared_ptr<DlFormula>& f = i < retractedDProof.size() ? abstractDProofConclusions[i] : helperRulesConclusions[i - retractedDProof.size()];
			out_conclusions.push_back(f);
		}
	} else {

		// 5.3 Obtain unfolded proof.
		vector<size_t> storedFundamentalLengths = measureFundamentalLengthsInAbstractDProof(indicesForNewProof, retractedDProof, abstractDProofConclusions, helperRules, helperRulesConclusions, debug, limit);
		newAbstractDProof = unfoldRulesInAbstractDProof(indicesForNewProof, retractedDProof, helperRules, debug, &storedFundamentalLengths, storeIntermediateUnfoldingLimit);
		for (size_t i : indicesForNewProof) {
			const shared_ptr<DlFormula>& f = i < retractedDProof.size() ? abstractDProofConclusions[i] : helperRulesConclusions[i - retractedDProof.size()];
			out_conclusions.push_back(f);
		}
	}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to build transformed proof." << endl;

	//#for (size_t i = 0; i < newAbstractDProof.size(); i++)
	//#	cout << "[" << i << "] " << DlCore::toPolishNotation(out_conclusions[i]) << " = " << newAbstractDProof[i] << endl;
	return newAbstractDProof;
}

#ifdef PARSEMMPL_STORED
shared_ptr<DlFormula> DRuleParser::_parseEnclosedMmFormula(unordered_map<string, shared_ptr<DlFormula>>& formulaBackups, const string& strConsequent, string::size_type myFirst, string::size_type myLast, const map<string::size_type, pair<string::size_type, shared_ptr<DlFormula>>>& potentialSubformulas, const string::const_iterator& consBegin) {
#else
shared_ptr<DlFormula> DRuleParser::_parseEnclosedMmFormula(const string& strConsequent, string::size_type myFirst, string::size_type myLast, const map<string::size_type, pair<string::size_type, shared_ptr<DlFormula>>>& potentialSubformulas, const string::const_iterator& consBegin) {
#endif
	// 1. Try to restore from backup
	string::size_type formulaOffset = myFirst + 1;
	const string myFormula = strConsequent.substr(formulaOffset, myLast - formulaOffset); // formula without first '(' and last ')', for backups
#ifdef PARSEMMPL_STORED
	unordered_map<string, shared_ptr<DlFormula>>::const_iterator backupResult = formulaBackups.find(myFormula);
	if (backupResult != formulaBackups.end())
		return backupResult->second;
#endif
	// 2. Determine relevant subformulas
	string::size_type myLastReserved = 0;
	vector<pair<string::size_type, string::size_type>> foundSubformulaBounds;
	shared_ptr<DlFormula> firstSubformula;
	shared_ptr<DlFormula> secondSubformula;
	bool myFirstPassed = false;
	for (const pair<const string::size_type, pair<string::size_type, shared_ptr<DlFormula>>>& p : potentialSubformulas) {
		string::size_type currentFirst = p.first;
		string::size_type currentLast = p.second.first;
		if (currentFirst > myLast)
			break;
		if (!myFirstPassed)
			myFirstPassed = currentFirst > myFirst;
		if (myFirstPassed && currentFirst > myLastReserved) {
			if (foundSubformulaBounds.size() > 1)
				throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\" has more than two top-level subformulas.");
			foundSubformulaBounds.push_back(make_pair(currentFirst, currentLast));
			myLastReserved = currentLast;
			if (foundSubformulaBounds.size() == 1)
				firstSubformula = p.second.second;
			else
				secondSubformula = p.second.second;
		}
	}

	// 3. Extract binary operator and construct both children
	//    NOTE: Since myFormula is surrounded by '(' and ')', we are looking for a binary operator (i.e. unary only cannot happen). Also there are no constants (i.e. nullary cannot happen).
	shared_ptr<DlFormula> lhs;
	shared_ptr<DlFormula> rhs;
	string binOp;
	auto obtainBinaryOperator = [&](const string_view& source, string_view::size_type opBeginOffset) -> string_view::size_type {
		string_view::size_type opEndOffset = source.find(' ', opBeginOffset);
		if (opEndOffset == string_view::npos)
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". There should be a binary operator ending with ' '.");
		binOp = string(source.data() + opBeginOffset, opEndOffset - opBeginOffset);
		return opEndOffset;
	};
	auto applyUnaryOperators = [&](shared_ptr<DlFormula>& target, const vector<DlOperator>& unaryOperators) -> void {
		for (vector<DlOperator>::const_reverse_iterator it = unaryOperators.rbegin(); it != unaryOperators.rend(); ++it) {
			// Apply unary operators in reverse order
			DlOperator op = *it;
			switch (op) {
			case DlOperator::Not:
				target = make_shared<DlFormula>(_not(), vector<shared_ptr<DlFormula>> { target });
				break;
			case DlOperator::Nece:
				target = make_shared<DlFormula>(_nece(), vector<shared_ptr<DlFormula>> { target });
				break;
			case DlOperator::Poss:
				target = make_shared<DlFormula>(_poss(), vector<shared_ptr<DlFormula>> { target });
				break;
			default:
				throw logic_error("DRuleParser::parseConsequent(): Input \"" + strConsequent + "\" resulted in invalid unary operator (DlOperator)" + to_string(static_cast<unsigned>(op)) + ".");
			}
		}
	};
	auto assignVariableTerm = [&](shared_ptr<DlFormula>& target, const string& var, const vector<DlOperator>& unaryOperators) -> void {
		if (var.empty())
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". A variable name shall not be empty.");
		target = make_shared<DlFormula>(make_shared<String>(var));
		applyUnaryOperators(target, unaryOperators);
	};
	auto readAndAssignIntermediateVariableTerm = [&](const string_view& source, shared_ptr<DlFormula>& target) -> string_view::size_type {
		vector<DlOperator> unaryOperators;
		string_view::iterator varBegin = _obtainUnaryOperatorSequence(source, unaryOperators);
		if (varBegin >= source.end())
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". Source should contain more symbols after the unary operator sequence.");
		string_view::size_type varBeginOffset = varBegin - source.begin();
		string_view::size_type varEndOffset = source.find(' ', varBeginOffset);
		if (varEndOffset == string_view::npos)
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". Source should contain a variable ending with ' '.");
		assignVariableTerm(target, string(&*varBegin, varEndOffset - varBeginOffset), unaryOperators);
		return varEndOffset;
	};
	auto readAndAssignEndingVariableTerm = [&](const string_view& source, shared_ptr<DlFormula>& target) -> void {
		vector<DlOperator> unaryOperators;
		string_view::iterator varBegin = _obtainUnaryOperatorSequence(source, unaryOperators);
		if (varBegin >= source.end())
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". Source should contain more symbols after the unary operator sequence.");
		string_view::size_type varBeginOffset = varBegin - source.begin();
		string_view::size_type varEndOffset = source.find(' ', varBeginOffset);
		if (varEndOffset != string_view::npos)
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". Source should end with a single variable after the unary operator sequence (and contain no further ' ').");
		assignVariableTerm(target, string(varBegin, source.end()), unaryOperators);
	};
	auto readAndApplySubformula = [&](const string_view& source, shared_ptr<DlFormula>& target, const shared_ptr<DlFormula>& subformula) -> void {
		vector<DlOperator> unaryOperators;
		string_view::iterator unopsEnd = _obtainUnaryOperatorSequence(source, unaryOperators);
		if (unopsEnd < source.end())
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". Source should end with a unary operator sequence.");
		target = subformula;
		applyUnaryOperators(target, unaryOperators);
	};
	string::const_iterator consBeginPlusOne = consBegin + 1;
	string::const_iterator formulaBegin = consBegin + formulaOffset;
	switch (foundSubformulaBounds.size()) {
	case 0: { // e.g. "~ P -> ~ ~ Q" => binary operator is first symbol in prefix
		string_view prefix(myFormula);
		string_view::size_type varEndOffsetLhs = readAndAssignIntermediateVariableTerm(prefix, lhs);
		string_view::size_type opEndOffset = obtainBinaryOperator(prefix, varEndOffsetLhs + 1);
		readAndAssignEndingVariableTerm(prefix.substr(opEndOffset + 1), rhs);
		break;
	}
	case 1: {
		string_view prefix(formulaBegin, consBegin + foundSubformulaBounds[0].first); // i.e. myFormula.substr(0, foundSubformulaBounds[0].first - formulaOffset)
		string_view postfix(consBeginPlusOne + foundSubformulaBounds[0].second, consBegin + myLast); // i.e. myFormula.substr(foundSubformulaBounds[0].second - myFirst)
		if (postfix.empty()) { // e.g. "~ P -> ~ <#1>" => binary operator is first symbol after the first symbol that is not a unary operator in prefix
			string_view::size_type varEndOffset = readAndAssignIntermediateVariableTerm(prefix, lhs);
			string_view::size_type opEndOffset = obtainBinaryOperator(prefix, varEndOffset + 1);
			readAndApplySubformula(prefix.substr(opEndOffset + 1), rhs, firstSubformula);
		} else { // e.g. "~ <#1> -> ~ Q" => binary operator is first symbol in postfix
			readAndApplySubformula(prefix, lhs, firstSubformula);
			if (postfix[0] != ' ')
				throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". Given a single left argument, postfix should begin with ' '.");
			string_view::size_type opEndOffset = obtainBinaryOperator(postfix, 1);
			readAndAssignEndingVariableTerm(postfix.substr(opEndOffset + 1), rhs);
		}
		break;
	}
	case 2: { // e.g. "~ <#1> -> ~ <#2>" => binary operator is first symbol in infix
		string_view prefix(formulaBegin, consBegin + foundSubformulaBounds[0].first); // i.e. myFormula.substr(0, foundSubformulaBounds[0].first - formulaOffset)
		string_view infix(consBeginPlusOne + foundSubformulaBounds[0].second, consBegin + foundSubformulaBounds[1].first); // i.e. myFormula.substr(foundSubformulaBounds[0].second - myFirst, foundSubformulaBounds[1].first - foundSubformulaBounds[0].second - 1)
		if (foundSubformulaBounds[1].second + 1 != myLast)
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\" has non-enclosed postfix.");
		readAndApplySubformula(prefix, lhs, firstSubformula);
		if (infix[0] != ' ')
			throw invalid_argument("DRuleParser::parseConsequent(): Invalid formula \"" + myFormula + "\". Given both arguments, infix should begin with ' '.");
		string_view::size_type opEndOffset = obtainBinaryOperator(infix, 1);
		readAndApplySubformula(infix.substr(opEndOffset + 1), rhs, secondSubformula);
		break;
	}
	default:
		throw logic_error("DRuleParser::parseConsequent(): Formula \"" + myFormula + "\" led to " + to_string(foundSubformulaBounds.size()) + " argument reservations.");
	}

	// 4. Construct tree from binary operator
	if (binOp.length() > 4)
		throw logic_error("DRuleParser::parseConsequent(): Unknown binary operator \"" + binOp + "\" for input \"" + strConsequent + "\".");
	uint32_t binOp_id = FOURCC(!binOp.empty() ? binOp[0] : 0, binOp.length() > 1 ? binOp[1] : 0, binOp.length() > 2 ? binOp[2] : 0, binOp.length() > 3 ? binOp[3] : 0);
	shared_ptr<DlFormula> result;
	switch (binOp_id) {
	case MMID_IMPLY: {
		result = make_shared<DlFormula>(_imply(), vector<shared_ptr<DlFormula>> { lhs, rhs });
		break;
	}
	case MMID_EQUIV: {
		result = make_shared<DlFormula>(_equiv(), vector<shared_ptr<DlFormula>> { lhs, rhs });
		break;
	}
	case FOURCC('v', 0, 0, 0): { // NOTE: MMID_OR -- i.e. \/ -- is not used by these formulas.
		result = make_shared<DlFormula>(_or(), vector<shared_ptr<DlFormula>> { lhs, rhs });
		break;
	}
	case FOURCC('^', 0, 0, 0): { // NOTE: MMID_AND -- i.e. /\ -- is not used by these formulas.
		result = make_shared<DlFormula>(_and(), vector<shared_ptr<DlFormula>> { lhs, rhs });
		break;
	}
	default:
		throw logic_error("DRuleParser::parseConsequent(): Unknown binary operator \"" + binOp + "\" for input \"" + strConsequent + "\".");
	}

	// 5. Store result to backups and return
#ifdef PARSEMMPL_STORED
	formulaBackups.emplace(make_pair(myFormula, result));
#endif
	return result;
}

string_view::iterator DRuleParser::_obtainUnaryOperatorSequence(const string_view& unaryOperatorSequence, vector<DlOperator>& unaryOperators) {
	string_view::size_type begin = 0;
	string_view::size_type end = string_view::npos;
	for (string_view::size_type i = 0; i < unaryOperatorSequence.length(); i++)
		if (unaryOperatorSequence[i] == ' ') {
			end = i;
			string op(unaryOperatorSequence.substr(begin, end - begin));
			// Add unary operator to process queue (so it can be processed before earlier occurring operators).
			if (op == "~")
				unaryOperators.push_back(DlOperator::Not);
			else if (op == "□")
				unaryOperators.push_back(DlOperator::Nece);
			else if (op == "◇")
				unaryOperators.push_back(DlOperator::Poss);
			else
				return unaryOperatorSequence.begin() + begin; // return current pos when reaching a symbol that is not a unary operator
		} else if (end + 1 == i)
			begin = i;
	return end == string_view::npos ? unaryOperatorSequence.begin() : unaryOperatorSequence.begin() + end + 1;
};

}
}
