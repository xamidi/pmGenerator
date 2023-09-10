#include "DRuleParser.h"

#include "../helper/FctHelper.h"
#include "../tree/TreeNode.h"
#include "../logic/DlCore.h"
#include "../logic/DlFormula.h"

#include <boost/algorithm/string.hpp>

#include <iostream>

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::tree;
using namespace xamidi::logic;

namespace xamidi {
namespace metamath {

vector<pair<string, string>> DRuleParser::readFromMmsolitaireFile(const string& file, bool debug) {
	vector<pair<string, string>> dProofsInFile;
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
	while (getline(ss, temp, '\n') || !eof) { // read every line, _including_ the last line
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
			dProofsInFile.push_back(make_pair(dProofName, dProof.substr(0, index)));
			dProofName.clear();
			dProof.clear();
		} else
			dProof += temp;
		eof = ss.eof();
	}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to read " << dProofsInFile.size() << " condensed detachment proofs from file \"" << file << "\"." << endl;
	//#cout << "D-proofs: " << FctHelper::vectorStringF(dProofsInFile, [](const pair<string, string>& p) { return p.first + ": " + p.second; }, "{\n\t", "\n}", "\n\t") << endl;
	return dProofsInFile;
}

map<size_t, set<string>> DRuleParser::prepareDProofsByLength(const string& file, unsigned minUseAmountToCreateHelperProof, vector<pair<string, string>>* optOut_dProofsInFile, bool debug) {
	vector<pair<string, string>> dProofsInFile = readFromMmsolitaireFile(file, debug);
	map<size_t, set<string>> knownDProofsByLength;
	parseDProofs_raw(dProofsInFile, minUseAmountToCreateHelperProof, nullptr, &knownDProofsByLength, false, debug, true, true, nullptr, true);
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

vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> DRuleParser::parseDProof_raw(const string& dProof, unsigned minUseAmountToCreateHelperProof, bool verifyingConstruct, bool debug, bool calculateMeanings, bool exceptionOnUnificationFailure) {
	const vector<string> dProofsWithoutContexts = { { dProof } };
	vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> rawParseData = parseDProofs_raw( { }, minUseAmountToCreateHelperProof, nullptr, nullptr, verifyingConstruct, debug, calculateMeanings, exceptionOnUnificationFailure, &dProofsWithoutContexts);
	return rawParseData;
}

vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> DRuleParser::parseDProof_raw_permissive(const string& dProof, unsigned minUseAmountToCreateHelperProof, bool verifyingConstruct, bool debug, bool calculateMeanings) {
	return parseDProof_raw(dProof, minUseAmountToCreateHelperProof, verifyingConstruct, debug, calculateMeanings, false);
}

vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> DRuleParser::parseDProofs_raw(const vector<pair<string, string>>& dProofs, unsigned minUseAmountToCreateHelperProof, map<string, string>* optOut_duplicates, map<size_t, set<string>>* optOut_knownDProofsByLength, bool verifyingConstruct, bool debug, bool calculateMeanings, bool exceptionOnUnificationFailure, const vector<string>* altIn_dProofsWithoutContexts, bool prepareOnly) { // NOTE: Detailed debug code available at https://github.com/deontic-logic/proof-tool/commit/c25e82b6c239fe33fa2b0823fcd17244a62f4a20
	// 1. Group and order the (in D-notation) given proofs by their length, and create a context lookup table
	map<size_t, set<string>> knownDProofsByLength; // length -> set of condensed detachment proofs of that length
	unordered_map<string, string> knownDProofsToContext; // condensed detachment proof (e.g. "DD211") -> context (e.g. "(P -> P); ! *2.08 Id")
	if (altIn_dProofsWithoutContexts) {
		size_t i = 0;
		for (const string& concreteDProof : *altIn_dProofsWithoutContexts) {
			pair<unordered_map<string, string>::iterator, bool> empResult = knownDProofsToContext.emplace(concreteDProof, to_string(i)); // for used theorems, their original indices will be stored
			if (empResult.second)
				knownDProofsByLength[concreteDProof.length()].emplace(concreteDProof);
			i++;
		}
	} else
		for (const pair<string, string>& p : dProofs) {
			const string& concreteDProof = p.second;
			pair<unordered_map<string, string>::iterator, bool> empResult = knownDProofsToContext.emplace(concreteDProof, p.first);
			if (empResult.second)
				knownDProofsByLength[concreteDProof.length()].emplace(concreteDProof);
			else if (optOut_duplicates)
				(*optOut_duplicates)[p.first] = empResult.first->second;
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
					boost::replace_all(abstractDProof, it->second, "(" + to_string(referencingDProofs.size() - pos) + ")");
				pos++;
			}
			referencingDProofs.push_back(make_pair(abstractDProof, concreteDProof));
		}

	// 3. Obtain the minimal set of referencing proofs of size 3 that would be required to accomplish that all given proofs can be retracted to a length of at most 3.
	vector<pair<string, string>> helperProofCandidates;
	map<string, string> recentCandidates;
	do { // register all references, building up on existing references
		recentCandidates.clear();
		for (const pair<string, string>& p : referencingDProofs) {
			const string& abstractDProof = p.first;
			if (abstractDProof.length() >= 5) { // To contain proofs of fundamental length greater than 1, the containing proof requires length >= 5. ; NOTE: D11, D12, D13, D21, D22, D23 are all minimal non-trivial proofs under { (A1), (A2), (A3), (MP) }. D31, D32, D33 are impossible.
				if (abstractDProof[0] != 'D')
					throw invalid_argument("DRuleParser::parseDProofs(): A D-proof of length greater 1 must start with 'D'.");
				string::size_type lastDIndex = 0;
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
						lastDIndex = i;
						referenceIndices = { -1, -1 };
						break;
					case '(':
						inReference = true;
						refIndex = 0;
						break;
					case ')':
						if (lastDIndex) {
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
						else if (c > '3')
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
						else if (lastDIndex) {
							referenceIndices[nonDs] = '0' - c;
							nonDs++;
						}
						break;
					default:
						throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not a proof step.");
					}
					if (nonDs == 2) { // Every "D<non-D><non-D>" that we read is a new subproof. Each "<non-D>" can be either an axiom, or a reference.
						string subProof(abstractDProof.begin() + lastDIndex, abstractDProof.begin() + i + 1);
						pair<map<string, string>::iterator, bool> emplaceResult = recentCandidates.emplace(subProof, string { });
						if (emplaceResult.second) { // actually inserted => we still need to calculate the concrete subproof
							string& concreteSubproof = emplaceResult.first->second;
							concreteSubproof = "D";
							for (int referenceIndex : referenceIndices)
								if (referenceIndex >= 0) { // a reference
									if (static_cast<unsigned>(referenceIndex) >= referencingDProofs.size() + helperProofCandidates.size())
										throw logic_error("DRuleParser::parseDProofs(): Impossible reference index " + to_string(referenceIndex) + ".");
									const string& concretePart = static_cast<unsigned>(referenceIndex) < referencingDProofs.size() ? referencingDProofs[referenceIndex].second : helperProofCandidates[referenceIndex - referencingDProofs.size()].second;
									concreteSubproof += concretePart;
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
						}
						nonDs = 0;
						lastDIndex = 0;
					}
				}
			}
		}
		size_t proofIndex = helperProofCandidates.size() + referencingDProofs.size(); // starting index of the new stuff
		for (const pair<const string, string>& p : recentCandidates) {
			const string& recentExtraProof = p.first;
			// Replacements in existing basic proofs
			for (vector<pair<string, string>>::iterator itDProof = referencingDProofs.begin(); itDProof != referencingDProofs.end(); ++itDProof)
				if (itDProof->first.length() >= 5)
					boost::replace_all(itDProof->first, recentExtraProof, "(" + to_string(proofIndex) + ")");
			// Replacements in existing extra proofs
			for (vector<pair<string, string>>::iterator itDProof = helperProofCandidates.begin(); itDProof != helperProofCandidates.end(); ++itDProof)
				if (itDProof->first.length() >= 5)
					boost::replace_all(itDProof->first, recentExtraProof, "(" + to_string(proofIndex) + ")");
			proofIndex++;
		}
		// Registration of new extra proofs
		helperProofCandidates.insert(helperProofCandidates.end(), recentCandidates.begin(), recentCandidates.end());
	} while (!recentCandidates.empty());
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to obtain " << helperProofCandidates.size() << " helper proof candidates, i.e. the minimal set of referenced proofs such that all proofs have a length of at most 3." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 4. Keep only those helper proof candidates which are referenced at least 'minUseAmountToCreateHelperProof' times. The concrete variants of the accepted
	//    candidates are -- grouped by concrete lengths -- inserted into 'knownDProofsByLength', which already contains the given proofs in the same manner.
	map<size_t, unsigned> referenceAmounts; // index of proof -> amount of references to proof
	auto findReferences = [&](const string& dProof, unsigned containerIndex) {
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
				case ')':
					if (refIndex >= referencingDProofs.size())
						referenceAmounts[refIndex]++; // Only test the extra references, since only them are optional.
					refIndex = 0;
					inReference = false;
					break;
				default:
					throw invalid_argument("DRuleParser::parseDProofs(): Invalid character '" + string { c } + "': Not part of a proof reference.");
				}
			else if (c == '(')
				inReference = true;
	};
	{
		unsigned containerIndex = 0;
		for (const pair<string, string>& p : referencingDProofs) {
			const string& referencingDProof = p.first;
			findReferences(referencingDProof, containerIndex++);
		}
		for (const pair<string, string>& p : helperProofCandidates) {
			const string& extraProof = p.first;
			findReferences(extraProof, containerIndex++);
		}
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
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to reduce to " << extraCounter << " helper proofs." << endl;
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
			cout << proofCounter << " condensed detachment proofs prepared." << endl;
		}
		return {};
	}

	// 5. Create requested condensed detachment proofs with references ("refined D-proofs"), ordered by their concrete length.
	vector<string> proofNames;
	vector<string> usedDProofs;
	vector<string> proofContexts;
	vector<string> revertedDProofs;
	vector<string> refinedDProofs;
	unsigned helperCounter = 0;
	unsigned theoremCounter = 0;
	for (const pair<const size_t, set<string>>& p : knownDProofsByLength)
		for (const string& concreteDProof : p.second) {
			string refinedDProof(concreteDProof);
			reverse(refinedDProof.begin(), refinedDProof.end());
			string revertedDProof(refinedDProof);
			size_t pos = 1;
			for (vector<string>::const_reverse_iterator it = revertedDProofs.rbegin(); it != revertedDProofs.rend(); ++it) {
				if (it->length() > 1)
					boost::replace_all(refinedDProof, *it, "(" + to_string(revertedDProofs.size() - pos) + ")");
				pos++;
			}
			revertedDProofs.push_back(revertedDProof); // Add after inserting references, to avoid self-referencing.
			refinedDProofs.push_back(refinedDProof);
			unordered_map<string, string>::iterator searchResult = knownDProofsToContext.find(concreteDProof);
			if (searchResult != knownDProofsToContext.end()) {
				++theoremCounter;
				proofNames.push_back("T" + to_string(theoremCounter));
			} else
				proofNames.push_back("H" + to_string(++helperCounter));
		}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to refine " << proofNames.size() << " condensed detachment proofs." << endl;
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
	vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> rawProofData;
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
				case ')': {
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
				case 'D': {
					if (formulas.size() < 2)
						throw invalid_argument("DRuleParser::parseDProofs(): Invalid D rule for condensed detachment proof '" + proofNames[counter] + "'.");
					// 1. Determine antecedent and conditional
					//    NOTE: The D rule is basically (MP):n,x for a current length of n, i.e. x: A->B, n: A => n+1: B, where x is the last position lower n that has not yet been used.
					shared_ptr<DlFormula>& conditional = formulas.back();
					used.back() = true;
					const vector<shared_ptr<DlFormula>>& conditional_children = conditional->getChildren();
					if (conditional_children.size() != 2 || conditional->getValue()->value != DlCore::terminalStr_imply()) {
						if (exceptionOnUnificationFailure) // The form is correct, but the formulas don't match to be antecedent and conditional. Thus, this is actually a unification failure.
							throw invalid_argument("DRuleParser::parseDProofs(): Invalid conditional for condensed detachment proof '" + proofNames[counter] + "'.");
						else
							return {};
					}
					int lastTodo;
					for (lastTodo = static_cast<int>(used.size()) - 2; lastTodo >= 0; lastTodo--)
						if (!used[lastTodo])
							break;
					if (lastTodo < 0)
						throw invalid_argument("DRuleParser::parseDProofs(): Cannot find antecedent for condensed detachment proof '" + proofNames[counter] + "'.");
					shared_ptr<DlFormula>& antecedent = formulas[lastTodo];
					used[lastTodo] = true;
					metadata[formulas.size() + 1] = { static_cast<unsigned>(lastTodo) + 1, static_cast<unsigned>(formulas.size()) };

					{ // NOTE: Need these braces so that the use counts are correct for updatePrimitives().

						// 2. Obtain substitutions via unification and partial cloning
						map<string, shared_ptr<DlFormula>> substitutions;
						if (!DlCore::tryUnifyTrees(antecedent, conditional_children[0], &substitutions)) {
							if (debug)
								cerr << formulas.size() << ". " << DlCore::formulaRepresentation_traverse(formulas.back()) << "\t\t" << dReasons.back() << endl;
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
				case '(':
					atRef = true;
					break;
				}
		if (used.size() > 1 && !used[0]) // the first formula was not used ; prevents parsing strings like "11" or "D123"
			throw invalid_argument("DRuleParser::parseDProofs(): Condensed detachment proof '" + proofNames[counter] + "' has unused formulas.");

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

		rawProofData.push_back(make_pair(proofNames[counter], make_tuple(formulas, dReasons, metadata)));
		counter++;
	}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to convert " << proofNames.size() << " condensed detachment proofs to DL-proofs." << endl;
	return rawProofData;
}

shared_ptr<DlFormula> DRuleParser::parseMmPlConsequent(const string& strConsequent, bool calculateMeanings) {
#ifdef PARSEMMPL_STORED
	static unordered_map<string, shared_ptr<DlFormula>> formulaBackups;
	unordered_map<string, shared_ptr<DlFormula>>::iterator backupResult = formulaBackups.find(strConsequent);
	if (backupResult != formulaBackups.end())
		return backupResult->second;
#endif
	string::const_iterator consBegin = strConsequent.begin();
	if (strConsequent.empty())
		throw invalid_argument("DRuleParser::parseConsequent(): Input is empty.");
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
			shared_ptr<DlFormula> subformula = _parseEnclosedMmPlFormula(formulaBackups, strConsequent, currentSubformulaIndex, i, subformulas, consBegin);
#else
			shared_ptr<DlFormula> subformula = _parseEnclosedMmPlFormula(strConsequent, currentSubformulaIndex, i, subformulas, consBegin);
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
			if (op != DlOperator::Not)
				throw logic_error("DRuleParser::parseConsequent(): Input \"" + strConsequent + "\" resulted in invalid unary operator (DlOperator)" + to_string(static_cast<unsigned>(op)) + ".");
			currentPrefix = "~ " + currentPrefix; // NOTE: It is only that simple since '~' (i.e. \not) is the only propositional unary operator.
			result = make_shared<DlFormula>(_not(), vector<shared_ptr<DlFormula>> { result });
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

#ifdef PARSEMMPL_STORED
shared_ptr<DlFormula> DRuleParser::_parseEnclosedMmPlFormula(unordered_map<string, shared_ptr<DlFormula>>& formulaBackups, const string& strConsequent, string::size_type myFirst, string::size_type myLast, const map<string::size_type, pair<string::size_type, shared_ptr<DlFormula>>>& potentialSubformulas, const string::const_iterator& consBegin) {
#else
shared_ptr<DlFormula> DRuleParser::_parseEnclosedMmPlFormula(const string& strConsequent, string::size_type myFirst, string::size_type myLast, const map<string::size_type, pair<string::size_type, shared_ptr<DlFormula>>>& potentialSubformulas, const string::const_iterator& consBegin) {
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
			if (op != DlOperator::Not)
				throw logic_error("DRuleParser::parseConsequent(): Input \"" + strConsequent + "\" resulted in invalid unary operator (DlOperator)" + to_string(static_cast<unsigned>(op)) + ".");
			target = make_shared<DlFormula>(_not(), vector<shared_ptr<DlFormula>> { target }); // NOTE: It is only that simple since '~' (i.e. \not) is the only propositional unary operator.
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
			if (op != "~")
				return unaryOperatorSequence.begin() + begin; // '~' (i.e. \not) is the only propositional unary operator ; return current pos when reaching a symbol that is not a unary operator
			unaryOperators.push_back(DlOperator::Not); // add unary operator to process queue (so it can be processed before earlier occurring operators)
		} else if (end + 1 == i)
			begin = i;
	return end == string_view::npos ? unaryOperatorSequence.begin() : unaryOperatorSequence.begin() + end + 1;
};

}
}
