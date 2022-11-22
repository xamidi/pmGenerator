#include "DRuleReducer.h"

#include "../helper/FctHelper.h"
#include "../tree/TreeNode.h"
#include "../nortmann/DlCore.h"
#include "../nortmann/DlFormula.h"
#include "../nortmann/DlProofEnumerator.h"
#include "DRuleParser.h"

#define TBB_PREVIEW_CONCURRENT_ORDERED_CONTAINERS 1 // TODO Temporary, for low tbb version ("libtbb-dev is already the newest version (2020.1-2)" on Linux Mint 20.3)
#include <tbb/concurrent_map.h>
#include <tbb/concurrent_vector.h>
#include <tbb/parallel_for.h>

#include <boost/algorithm/string.hpp> // for boost::replace_all()

#include <iostream>

using namespace std;
using namespace xamid::helper;
using namespace xamid::nortmann;

namespace xamid {
namespace metamath {

void DRuleReducer::createReplacementsFile(const string& pmproofsFile, const string& outputFile, bool memReduction, bool debug) {
	// 1. Load and parse mmsolitaire's D-proofs.
	chrono::time_point<chrono::steady_clock> startTime;
	vector<pair<string, string>> dProofsInFile;
	map<int, set<string>> knownDProofsByLength = DRuleParser::prepareDProofsByLength(pmproofsFile, 1, &dProofsInFile, debug);
	//#cout << FctHelper::vectorStringF(dProofsInFile, [](const pair<string, string>& p) { return p.first + ": " + p.second; }, "{\n\t", "\n}", "\n\t") << endl;
	//#cout << FctHelper::mapStringF(knownDProofsByLength, [](const pair<const int, set<string>>& p) { return to_string(p.first) + " : " + FctHelper::setString(p.second); }, "{\n\t", "\n}", "\n\t") << endl;
	if (debug)
		startTime = chrono::steady_clock::now();
	vector<string> knownDProofs;
	for (const pair<const int, set<string>>& p : knownDProofsByLength)
		for (const string& s : p.second)
			knownDProofs.push_back(s);
	if (debug) {
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to transfer." << endl;
		startTime = chrono::steady_clock::now();
	}
	// NOTE: A tbb::concurrent_set<string, cmpStringGrow> inside would be preferable, but it has no reverse iterators in order to directly address the last element (which is required later on),
	//       i.e. prev(set.end()) would crash and set.rbegin() does not exist: https://spec.oneapi.io/versions/latest/elements/oneTBB/source/containers/concurrent_set_cls/iterators.html
	tbb::concurrent_unordered_map<shared_ptr<DlFormula>, set<string, cmpStringGrow>, dlFormulaHash, dlFormulaEqual> formulasToCheck;
	atomic<uint64_t> conclusionCounter { 0 };
	atomic<uint64_t> redundantCounter { 0 };
	unique_ptr<DlProofEnumerator::FormulaMemoryReductionData> _memReductionData = memReduction ? unique_ptr<DlProofEnumerator::FormulaMemoryReductionData>(new DlProofEnumerator::FormulaMemoryReductionData()) : nullptr;
	DlProofEnumerator::FormulaMemoryReductionData* const memReductionData = _memReductionData.get();
	mutex mtx_set;
	tbb::parallel_for(tbb::blocked_range<vector<string>::const_iterator>(knownDProofs.begin(), knownDProofs.end()), [&formulasToCheck, &conclusionCounter, &redundantCounter, &memReductionData, &mtx_set](tbb::blocked_range<vector<string>::const_iterator>& range) {
		for (vector<string>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& s = *it;
			vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<unsigned, vector<unsigned>>>>> rawParseData = DRuleParser::parseDProof_raw(s);
			shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
			if (memReductionData) {
				DlCore::calculateEmptyMeanings(conclusion); // NOTE: May register new variables, which is thread-safe via DlCore::tryRegisterVariable().
				DlProofEnumerator::replaceNodes(conclusion, memReductionData->nodeStorage, memReductionData->nodeReplacementCounter);
				DlProofEnumerator::replaceValues(conclusion, memReductionData->valueStorage, memReductionData->valueReplacementCounter, memReductionData->alreadyProcessing);
				DlCore::clearMeanings(conclusion);
			}
			pair<tbb::concurrent_unordered_map<shared_ptr<DlFormula>, set<string, cmpStringGrow>, dlFormulaHash, dlFormulaEqual>::iterator, bool> emplaceResult = formulasToCheck.emplace(conclusion, set<string, cmpStringGrow> { });
			{
				lock_guard<mutex> lock(mtx_set);
				emplaceResult.first->second.insert(s);
			}
			if (!emplaceResult.second) // a proof for the conclusion is already known
				redundantCounter++;
			else
				conclusionCounter++;
		}
	});
	if (debug) {
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to parse " << conclusionCounter + redundantCounter << " D-proofs (" << conclusionCounter << " conclusions, " << redundantCounter << " redundant)." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 2. Load and parse generated D-proofs.
	string filePrefix = "data/dProofs";
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	uint64_t allRepresentativesCount;
	uint32_t start;
	if (!DlProofEnumerator::loadDProofRepresentatives(allRepresentatives, &allRepresentativesCount, &start, debug)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}
	filePostfix = "-unfiltered" + to_string(start) + "+.txt";
	if (!DlProofEnumerator::loadDProofRepresentatives(allRepresentatives, &allRepresentativesCount, &start, debug, filePrefix, filePostfix, false)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}
	ProgressData parseProgress(allRepresentatives.size() > 27 ? 5 : allRepresentatives.size() > 25 ? 10 : 20, allRepresentativesCount);
	tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual> representativeProofs = DlProofEnumerator::parseDProofRepresentatives(allRepresentatives, &parseProgress, memReductionData);
	if (debug) {
		cout << "Loaded and parsed " << representativeProofs.size() << " generated D-proofs in " << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << "." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 3. Consider formulas from mmsolitaire's D-proofs in case there are suboptimal proofs used despite better ones are already known.
	atomic<uint64_t> inputConclusionCounter { 0 };
	tbb::parallel_for(formulasToCheck.range(), [&representativeProofs, &inputConclusionCounter](tbb::concurrent_unordered_map<shared_ptr<DlFormula>, set<string, cmpStringGrow>, dlFormulaHash, dlFormulaEqual>::range_type& range) {
		for (tbb::concurrent_unordered_map<shared_ptr<DlFormula>, set<string, cmpStringGrow>, dlFormulaHash, dlFormulaEqual>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& currentBestDProof = *it->second.begin();
			pair<tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::iterator, bool> emplaceResult = representativeProofs.emplace(it->first, currentBestDProof);
			if (emplaceResult.second)
				inputConclusionCounter++;
		}
	});
	if (debug) {
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to load " << inputConclusionCounter << " more D-proofs from the input." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 4. Introduce a way to iterate formulas only up to a certain standard length (to greatly improve schema searching).
	tbb::concurrent_map<unsigned, tbb::concurrent_vector<pair<const shared_ptr<DlFormula>*, string>>> formulasByStandardLength;
	tbb::parallel_for(representativeProofs.range(), [&formulasByStandardLength](tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::range_type& range) {
		for (tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const shared_ptr<DlFormula>& formula = it->first;
			formulasByStandardLength[DlCore::standardFormulaLength(formula)].emplace_back(&formula, it->second);
		}
	});
	if (debug) {
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to create " << formulasByStandardLength.size() << " classes of formulas by their standard length." << endl;
		cout << "|representativeProofs| = " << representativeProofs.size() << ", |formulasByStandardLength| = " << formulasByStandardLength.size() << endl;
		//#cout << [](tbb::concurrent_map<unsigned, tbb::concurrent_vector<pair<const shared_ptr<DlFormula>*, string>>>& m) { stringstream ss; for (const pair<const unsigned, tbb::concurrent_vector<pair<const shared_ptr<DlFormula>*, string>>>& p : m) { ss << p.first << ":" << p.second.size() << ", "; } return ss.str(); }(formulasByStandardLength) << endl;
		startTime = chrono::steady_clock::now();
	}

	// 5. Consider formulas of generated D-proofs that would soon be generated, i.e. for a proof α for A\implyB (with B yet unproven) such that A has a known proof β, consider proof Dαβ for B.
	// NOTE: While iterating all proofs α of A\implyB, do not look for schemas [which would take too long – similarly long as DlProofEnumerator::_removeRedundantConclusionsForProofsOfMaxLength()]
	//       but just use A as a key for search (which is fast). [The results may be less due to the schema-filtered generation process, i.e. there might be an overlooked proof for a proper schema of A.]
	//       If a proof β for A can be found, just emplace Dαβ for B without verifying that B has not been proven yet. If a proof of B is already contained, Dαβ will be ignored.
//#define EXTRA_SCHEMA_LOOKUP // Issue: Not using schema search barely gives extra results, but using it takes very long (so that generating them permanently via DlProofEnumerator would be a better option).
	atomic<uint64_t> extraCheckCounter { 0 };
	atomic<uint64_t> extraSchemaCheckCounter { 0 };
	atomic<uint64_t> extraParseCounter { 0 };
	atomic<uint64_t> extraProofCounter { 0 };
#ifdef EXTRA_SCHEMA_LOOKUP
	ProgressData extraProgress(allRepresentatives.size() > 27 ? 1 : allRepresentatives.size() > 25 ? 2 : 5, allRepresentativesCount);
	extraProgress.setStartTime();
	tbb::parallel_for(representativeProofs.range(), [&representativeProofs, &formulasByStandardLength, &extraCheckCounter, &extraSchemaCheckCounter, &extraParseCounter, &extraProofCounter, &extraProgress, &memReductionData](tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::range_type& range) {
#else
	tbb::parallel_for(representativeProofs.range(), [&representativeProofs, &formulasByStandardLength, &extraCheckCounter, &extraSchemaCheckCounter, &extraParseCounter, &extraProofCounter, &memReductionData](tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::range_type& range) {
#endif
		for (tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const shared_ptr<DlFormula>& conditional = it->first;
			if (conditional->getValue()->value == DlCore::terminalStr_imply()) { // actually a conditional, i.e. A\implyB
				extraCheckCounter++;
				const shared_ptr<DlFormula>& antecedent = conditional->getChildren()[0]; // A
				// NOTE: Since the antecedent is the first part of its conditional, its variables are good for searching in 'representativeProofs' (i.e. they start from "0").
				tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::const_iterator searchResult = representativeProofs.find(antecedent);
				bool directHit = searchResult != representativeProofs.end(); // whether there is a proof with A being the literal consequent
#ifdef EXTRA_SCHEMA_LOOKUP
				string dProof_antecedent; // proof β for A
				auto setAntecedentDProof = [&](const string& dProof) { dProof_antecedent = dProof; }; // use to avoid error "cannot bind rvalue reference of type '[...]basic_string<char>&&' to lvalue of type 'const string' {aka 'const [...]basic_string<char>'}"
				atomic<bool> schemaHit { false };
				if (directHit)
					dProof_antecedent = searchResult->second;
				else { // NOTE: Not searching for the best schema, but only for any proven schema of A.
					unsigned formulaLen = DlCore::standardFormulaLength(antecedent);
					mutex mtx;
					tbb::parallel_for(formulasByStandardLength.range(), [&formulaLen, &schemaHit, &extraSchemaCheckCounter, &antecedent, &setAntecedentDProof, &mtx](tbb::concurrent_map<unsigned, tbb::concurrent_vector<pair<const shared_ptr<DlFormula>*, string>>>::range_type& range) {
						for (tbb::concurrent_map<unsigned, tbb::concurrent_vector<pair<const shared_ptr<DlFormula>*, string>>>::const_iterator it = range.begin(); it != range.end(); ++it)
							if (schemaHit)
								return;
							else if (it->first <= formulaLen)
								for (const pair<const shared_ptr<DlFormula>*, string>& p : it->second) {
									extraSchemaCheckCounter++;
									if (DlCore::isSchemaOf(*p.first, antecedent)) { // found a schema of A
										schemaHit = true;
										lock_guard<mutex> lock(mtx);
										setAntecedentDProof(p.second);
									}
									if (schemaHit)
										return;
								}
					});
				}
				if (directHit || schemaHit) {
					string dProof = "D" + it->second + dProof_antecedent; // proof Dαβ for B
#else
				if (directHit) {
					string dProof = "D" + it->second + searchResult->second; // proof Dαβ for B
#endif
					extraParseCounter++;
					// NOTE: If parsing took too long, we could clone B and substitute its variables to start from "0". But parsing isn't an issue here at all.
					vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<unsigned, vector<unsigned>>>>> rawParseData = DRuleParser::parseDProof_raw(dProof);
					shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
					if (memReductionData) {
						DlCore::calculateEmptyMeanings(conclusion); // NOTE: May register new variables, which is thread-safe via DlCore::tryRegisterVariable().
						DlProofEnumerator::replaceNodes(conclusion, memReductionData->nodeStorage, memReductionData->nodeReplacementCounter);
						DlProofEnumerator::replaceValues(conclusion, memReductionData->valueStorage, memReductionData->valueReplacementCounter, memReductionData->alreadyProcessing);
						DlCore::clearMeanings(conclusion);
					}
					pair<tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlFormulaHash, dlFormulaEqual>::iterator, bool> emplaceResult = representativeProofs.emplace(conclusion, dProof);
					if (emplaceResult.second) { // a proof for the conclusion was not already known
						extraProofCounter++;
						const shared_ptr<DlFormula>& formula = emplaceResult.first->first; // NOTE: It is crucial that the stored address (which remains valid) is used.
						formulasByStandardLength[DlCore::standardFormulaLength(formula)].emplace_back(&formula, dProof); // also the structure for efficient iteration requires to be updated
					}
					//#{ static mutex mtx_cout; lock_guard<mutex> lock(mtx_cout); cerr << (directHit ? "Direct hit!" : "Schema hit!") << " ; So far checked " << extraCheckCounter << " conditionals (using " << extraSchemaCheckCounter << " schema checks), parsed " << extraParseCounter << " candidates, and found " << extraProofCounter << " new D-proofs from existing combinations." << endl; }
				}
			}
#ifdef EXTRA_SCHEMA_LOOKUP
			// Show progress
			if (extraProgress.nextStep()) {
				uint64_t percentage;
				string progress;
				string etc;
				if (extraProgress.nextState(percentage, progress, etc)) {
					time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
					cout << strtok(ctime(&time), "\n") << ": Extra checked " << (percentage < 10 ? " " : "") << percentage << "% of D-proofs. [" << progress << "] (" << etc << ")" << endl;
				}
			}
#endif
		}
	});
	// NOTE: Doesn't seem to generate much, e.g. 27: 13366.48 ms taken to check 1733457 conditionals, parse 3 candidates, and load 3 extra D-proofs from existing combinations.
	if (debug) {
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to check " << extraCheckCounter << " conditionals (using " << extraSchemaCheckCounter << " schema checks), parse " << extraParseCounter << " candidates, and load " << extraProofCounter << " new D-proofs from existing combinations." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 6. Search for shorter proofs.
	tbb::concurrent_map<string, string, cmpStringShrink> shorteningReplacements;
	tbb::concurrent_map<string, string, cmpStringShrink> stylingReplacements;
	atomic<uint64_t> schemaCheckCounter { 0 };
	mutex mtx_cout;
	tbb::parallel_for(formulasToCheck.range(), [&debug, &formulasByStandardLength, &shorteningReplacements, &stylingReplacements, &schemaCheckCounter, &mtx_cout](tbb::concurrent_unordered_map<shared_ptr<DlFormula>, set<string, cmpStringGrow>, dlFormulaHash, dlFormulaEqual>::range_type& range) {
		for (tbb::concurrent_unordered_map<shared_ptr<DlFormula>, set<string, cmpStringGrow>, dlFormulaHash, dlFormulaEqual>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const shared_ptr<DlFormula>& formula = it->first;
			const set<string, cmpStringGrow>& dProofs = it->second;
			const string& currentWorstDProof = *dProofs.rbegin(); // NOTE: Using set<string, cmpStringGrow> instead of tbb::concurrent_set<string, cmpStringGrow>, avoids doing *next(dProofs.begin(), dProofs.size() - 1) each time.
			//#if (dProofs.size() > 1) { lock_guard<mutex> lock(mtx_cout); cout << "currentWorstDProof = " << currentWorstDProof << ", dProofs = " << FctHelper::setString(dProofs) << endl; }
			const unsigned currentWorstLength = currentWorstDProof.length();
			mutex mtx_best;
			bool bad = false;
			shared_ptr<DlFormula> bestSchema;
			string bestDProof;
			mutex mtx_alt;
			bool alt = false;
			set<string, cmpStringGrow> alternativeDProofs;
			unsigned formulaLen = DlCore::standardFormulaLength(formula);
			tbb::parallel_for(formulasByStandardLength.range(), [&formulaLen, &schemaCheckCounter, &formula, &currentWorstDProof, &currentWorstLength, &mtx_best, &bad, &bestSchema, &bestDProof, &mtx_alt, &alt, &alternativeDProofs](tbb::concurrent_map<unsigned, tbb::concurrent_vector<pair<const shared_ptr<DlFormula>*, string>>>::range_type& range) {
				for (tbb::concurrent_map<unsigned, tbb::concurrent_vector<pair<const shared_ptr<DlFormula>*, string>>>::const_iterator it = range.begin(); it != range.end(); ++it)
					// NOTE: No abort checks, since it is possible that multiple schemas with different proof sizes of the same formula are stored representatives.
					if (it->first <= formulaLen)
						for (const pair<const shared_ptr<DlFormula>*, string>& p : it->second) {
							const string& dProof = p.second;
							if (dProof.length() <= currentWorstLength) {
								const shared_ptr<DlFormula>& potentialSchema = *p.first;
								schemaCheckCounter++;
								if (DlCore::isSchemaOf(potentialSchema, formula)) { // found a schema
									{
										lock_guard<mutex> lock(mtx_best);
										if ((!bad || bestDProof.length() > dProof.length()) && dProof.length() < currentWorstLength) {
											bad = true;
											bestSchema = potentialSchema;
											bestDProof = dProof;
										}
									}
									if (currentWorstDProof != dProof) {
										lock_guard<mutex> lock(mtx_alt);
										alt = true;
										alternativeDProofs.emplace(dProof);
									}
								}
							}
						}
			});
			if (alt) { // NOTE: bad => (alt && |alternativeDProofs| > 0).
				const string& bestAlternative = *alternativeDProofs.begin();
				// Remember replacements
				bool hasMereAlternatives = false;
				if (bad) {
					for (const string& dProof : dProofs)
						if (dProof.length() > bestDProof.length()) // improvement
							shorteningReplacements.emplace(dProof, bestDProof);
						else if (dProof != bestAlternative) {
							if (!hasMereAlternatives)
								hasMereAlternatives = true;
							stylingReplacements.emplace(dProof, bestDProof);
						}
				} else {
					for (const string& dProof : dProofs)
						if (dProof != bestAlternative)
							stylingReplacements.emplace(dProof, bestAlternative);
				}
				if (debug) {
					lock_guard<mutex> lock(mtx_cout);
					auto setStr = [](const set<string, cmpStringGrow>& m, size_t len, bool longer, bool prntLen, const string& exclude) {
						stringstream ss;
						bool first = true;
						for (const string& s : m)
							if (s != exclude && ((longer && s.length() > len) || (!longer && s.length() <= len))) {
								if (first)
									first = false;
								else
									ss << ", ";
								if (prntLen)
									ss << "(" << s << ", " << s.length() << ")";
								else
									ss << s;
							}
						return ss.str();
					};
					if (bad)
						cout << "[NOTE] Found shorter proof \"" << bestDProof << "\" (length " << bestDProof.length() << ") for { " << setStr(dProofs, bestDProof.length(), true, true, bestDProof) << " }, best schema: " << DlCore::formulaRepresentation_traverse(bestSchema) << endl;
					if (!bad || hasMereAlternatives) // NOTE: !bad => bestDProof.length() == 0, thus printing longer proofs prints them all.
						cout << "[NOTE] Found alternative proof " + bestAlternative + " for { " << setStr(dProofs, bestDProof.length(), !bad, false, bestAlternative) << " }." << endl;
				}
			}
		}
	});
	if (debug) {
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken for " << schemaCheckCounter << " schema checks." << endl;
		startTime = chrono::steady_clock::now();
	}
	//#cout << "shorteningReplacements = " << FctHelper::vectorStringF(vector<pair<string, string>>(shorteningReplacements.begin(), shorteningReplacements.end()), [](const pair<string, string>& p) { return p.first + "," + p.second; }, "{\n\t", "\n}", "\n\t") << endl;
	//#cout << "stylingReplacements = " << FctHelper::vectorStringF(vector<pair<string, string>>(stylingReplacements.begin(), stylingReplacements.end()), [](const pair<string, string>& p) { return p.first + "," + p.second; }, "{\n\t", "\n}", "\n\t") << endl;

	// 7. Store useful replacements.
	string content = FctHelper::vectorStringF(vector<pair<string, string>>(shorteningReplacements.begin(), shorteningReplacements.end()), [](const pair<string, string>& p) { return p.first + "," + p.second; }, { }, "\n\n", "\n") + FctHelper::vectorStringF(vector<pair<string, string>>(stylingReplacements.begin(), stylingReplacements.end()), [](const pair<string, string>& p) { return p.first + "," + p.second; }, { }, "\n", "\n");
	FctHelper::writeToFile(outputFile, content);
	if (debug)
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << content.length() << " bytes of condensed detachment proof replacement strings to " << outputFile << "." << endl;
	else
		cout << "Condensed detachment proof replacement strings saved to " << outputFile << "." << endl;
}

void DRuleReducer::applyReplacements(const string& initials, const string& replacementsFile, const string& pmproofsFile, const string& outputFile, bool styleAll, bool listAll, bool wrap, bool debug) {
	// 1. Load generated replacements.
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	vector<pair<string, string>> shorteningReplacements;
	vector<pair<string, string>> stylingReplacements;
	{
		ifstream fin(replacementsFile, fstream::in | fstream::binary);
		if (!fin.is_open()) {
			if (debug)
				cerr << "Failed to read the replacements file \"" << replacementsFile << "\". Aborting." << endl;
			return;
		}
		bool shortening = true;
		string line;
		while (getline(fin, line)) {
			if (line.empty()) {
				if (shortening)
					shortening = false;
			} else {
				string::size_type i = line.find(',');
				if (i == string::npos) {
					if (debug)
						cerr << "Failed to parse the replacements file \"" << replacementsFile << "\". Aborting." << endl;
					return;
				}
				if (shortening)
					shorteningReplacements.emplace_back(line.substr(0, i), line.substr(i + 1));
				else
					stylingReplacements.emplace_back(line.substr(0, i), line.substr(i + 1));
			}
		}
		if (debug)
			cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to read " << shorteningReplacements.size() << " shortening replacements and " << stylingReplacements.size() << " styling replacements." << endl;
		//#cout << "shorteningReplacements = " << FctHelper::vectorStringF(shorteningReplacements, [](const pair<string, string>& p) { return p.first + "," + p.second; }, "{\n\t", "\n}", "\n\t") << endl;
		//#cout << "stylingReplacements = " << FctHelper::vectorStringF(stylingReplacements, [](const pair<string, string>& p) { return p.first + "," + p.second; }, "{\n\t", "\n}", "\n\t") << endl;
	}

	// 2. Load mmsolitaire's D-proofs.
	vector<pair<string, string>> dProofsInFile = DRuleParser::readFromMmsolitaireFile(pmproofsFile, debug);
	if (debug)
		startTime = chrono::steady_clock::now();
	vector<string::size_type> prevLengths(dProofsInFile.size());
	for (size_t i = 0; i < dProofsInFile.size(); i++)
		prevLengths[i] = dProofsInFile[i].second.length();
	if (debug) {
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to store " << dProofsInFile.size() << " lengths." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 3. Apply replacements.
	enum class Modification {
		None = 0, Styled = 1, Shorter = 2
	};
	vector<Modification> modifications(dProofsInFile.size());
	for (size_t i = 0; i < dProofsInFile.size(); i++) {
		pair<string, string>& p = dProofsInFile[i];
		const string originalDProof = p.second;
		string& dProof = p.second;
		for (pair<string, string>& replacement : shorteningReplacements)
			boost::replace_all(dProof, replacement.first, replacement.second);
		if (originalDProof != dProof) { // could actually reduce that proof
			modifications[i] = Modification::Shorter;
			const string reducedDProof = debug ? dProof : string { };
			if (debug)
				cerr << "[NOTE] Could reduce \"" << p.first << "\" from " << originalDProof.length() << " to " << dProof.length() << " steps. Before applying styling replacements: " << dProof << endl;
			for (pair<string, string>& replacement : stylingReplacements)
				boost::replace_all(dProof, replacement.first, replacement.second);
			if (debug) {
				if (reducedDProof != dProof)
					cout << "[NOTE] Could further modify \"" << p.first << "\" with styling replacements: " << dProof << endl;
				else
					cout << "[NOTE] Couldn't further modify \"" << p.first << "\" with applying styling replacements." << endl;
			}
		} else if (styleAll) {
			for (pair<string, string>& replacement : stylingReplacements)
				boost::replace_all(dProof, replacement.first, replacement.second);
			if (originalDProof != dProof) {
				modifications[i] = Modification::Styled;
				if (debug)
					cout << "[NOTE] Could modify \"" << p.first << "\" with styling replacements: " << dProof << endl;
			}
		}
	}
	if (debug)
		cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to apply replacements." << endl;
	startTime = chrono::steady_clock::now();

	// 4. Generate result depending on the request.
	stringstream ss;
	bool first = true;
	uint64_t noneCounter = 0;
	uint64_t styledCounter = 0;
	uint64_t shorterCounter = 0;
	for (size_t i = 0; i < dProofsInFile.size(); i++) {
		auto resultOfProof = [&](const string& context, const string& dProof) { // also checks for valid schema
			// Obtain desired consequent.
			string::size_type semIndex = context.find(';');
			if (semIndex == string::npos)
				throw invalid_argument("DRuleReducer::applyReplacements(): Invalid context \"" + context + "\" has no ';'.");
			shared_ptr<DlFormula> consequent = DRuleParser::parseMmPlConsequent(context.substr(0, semIndex), false);

			// Check if we can substitute to desired consequent.
			vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<unsigned, vector<unsigned>>>>> rawParseData = DRuleParser::parseDProof_raw(dProof);
			shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
			shared_ptr<DlFormula> reference = DlCore::toBasicDlFormula(consequent, nullptr, nullptr, nullptr, false);
			map<string, shared_ptr<DlFormula>> substitutions;
			if (!DlCore::isSchemaOf(conclusion, reference, &substitutions))
				throw invalid_argument("DRuleReducer::applyReplacements(): (" + context + ") " + DlCore::formulaRepresentation_traverse(conclusion) + " is not a subformula of BasicDL(consequent) " + DlCore::formulaRepresentation_traverse(reference) + ".");

			// Obtain result from conclusion.
			static const map<string, shared_ptr<DlFormula>> resultSubstitutions { { { "0", make_shared<DlFormula>(make_shared<String>("P")) }, { "1", make_shared<DlFormula>(make_shared<String>("Q")) }, { "2", make_shared<DlFormula>(make_shared<String>("R")) }, { "3", make_shared<DlFormula>(make_shared<String>("S")) }, { "4", make_shared<DlFormula>(make_shared<String>("T")) }, { "5", make_shared<DlFormula>(make_shared<String>("U")) }, { "6", make_shared<DlFormula>(make_shared<String>("V")) }, { "7", make_shared<DlFormula>(make_shared<String>("W")) }, { "8", make_shared<DlFormula>(make_shared<String>("X")) }, { "9", make_shared<DlFormula>(make_shared<String>("Y")) }, { "10", make_shared<DlFormula>(make_shared<String>("Z")) }, { "11", make_shared<DlFormula>(make_shared<String>("A")) }, { "12", make_shared<DlFormula>(make_shared<String>("B")) }, { "13", make_shared<DlFormula>(make_shared<String>("C")) }, { "14", make_shared<DlFormula>(make_shared<String>("D")) }, { "15", make_shared<DlFormula>(make_shared<String>("E")) }, { "16", make_shared<DlFormula>(make_shared<String>("F")) }, { "17", make_shared<DlFormula>(make_shared<String>("G")) }, { "18", make_shared<DlFormula>(make_shared<String>("H")) }, { "19", make_shared<DlFormula>(make_shared<String>("I")) }, { "20", make_shared<DlFormula>(make_shared<String>("J")) }, { "21", make_shared<DlFormula>(make_shared<String>("K")) }, { "22", make_shared<DlFormula>(make_shared<String>("L")) }, { "23", make_shared<DlFormula>(make_shared<String>("M")) }, { "24", make_shared<DlFormula>(make_shared<String>("N")) }, { "25", make_shared<DlFormula>(make_shared<String>("O")) } } };
			shared_ptr<DlFormula> result = DlCore::substitute(conclusion, resultSubstitutions);

			// Convert result.
			string f = DlCore::standardFormulaRepresentation(result);
			boost::replace_all(f, "\\not", "~ ");
			boost::replace_all(f, "\\imply", " -> ");
			return f + "; ! Result of proof\n";
		};
		const pair<string, string>& p = dProofsInFile[i];
		const string& head = p.first;
		const string& dStr = p.second;
		switch (modifications[i]) {
		case Modification::None:
			if (listAll) {
				if (first)
					first = false;
				else
					ss << "\n";
				ss << head << "\n" << resultOfProof(head, dStr) << dStr << "; ! " << dStr.length() << " step" << (dStr.length() == 1 ? "" : "s") << "\n";
				noneCounter++;
			}
			break;
		case Modification::Styled:
			if (first)
				first = false;
			else
				ss << "\n";
			ss << head << "\n" << resultOfProof(head, dStr) << dStr << "; ! " << dStr.length() << " step" << (dStr.length() == 1 ? "" : "s") << "\n";
			styledCounter++;
			break;
		case Modification::Shorter:
			if (first)
				first = false;
			else
				ss << "\n";
			ss << head << " (" << initials << " " << prevLengths[i] << "->" << dStr.length() << ")\n" << resultOfProof(head, dStr) << dStr << "; ! " << dStr.length() << " step" << (dStr.length() == 1 ? "" : "s") << "\n";
			shorterCounter++;
			break;
		}
	}

	// 5. Store result (wrapped, if requested).
	string result;
	if (wrap) {
		// NOTE: - formula lines are at most 68 chars
		//       - D-proof lines are at most 69 chars
		//       - "; !" and anything after it cannot be broken
		//       - formula lines _only_ wrap before ' '
		//       - there are no "  " (i.e. two consequent whitespaces)
		stringstream ss_wrap;
		string line;
		while (getline(ss, line)) {
			if (line.empty())
				ss_wrap << "\n";
			else {
				auto wrapStr = [](const string& s, string::size_type maxLineLen, string::size_type& currentLineIndex, bool isProofLine) {
					if (s.length() <= currentLineIndex + maxLineLen)
						return s;
					stringstream ss_localWrap;
					while (s.length() > currentLineIndex + maxLineLen) {
						if (currentLineIndex)
							ss_localWrap << "\n";
						string::size_type lineLen = maxLineLen;
						if (!isProofLine)
							while (s[currentLineIndex + lineLen] != ' ') {
								if (lineLen == 0)
									throw invalid_argument("DRuleReducer::applyReplacements(): Unwrappable formula line \"" + s + "\".");
								lineLen--;
							}
						ss_localWrap << s.substr(currentLineIndex, lineLen);
						currentLineIndex += lineLen;
					}
					if (s.length() > currentLineIndex)
						ss_localWrap << "\n" << s.substr(currentLineIndex);
					return ss_localWrap.str();
				};
				string::size_type semIndex = line.find("; ! ");
				if (semIndex == string::npos)
					throw logic_error("DRuleReducer::applyReplacements(): Invalid generated line \"" + line + "\" has no \"; ! \".");
				bool isProofLine = line.find_last_of(") (>-~<P", semIndex) == string::npos; // otherwise, formula line
				string::size_type lastLineIndex = 0;
				string::size_type maxLineLen = isProofLine ? 69 : 68;
				string wrapped = wrapStr(line.substr(0, semIndex), maxLineLen, lastLineIndex, isProofLine);
				if (line.length() - lastLineIndex <= maxLineLen) // "; ! [...]" fits without another wrap
					ss_wrap << wrapped << line.substr(semIndex) << "\n";
				else
					ss_wrap << wrapped << "\n" << line.substr(semIndex) << "\n";
			}
		}
		result = ss_wrap.str();
	} else
		result = ss.str();
	FctHelper::writeToFile(outputFile, result);
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to check, generate and save " << result.length() << " bytes of MM-styled condensed detachment proofs (" << shorterCounter << " shortened, " << styledCounter << " styled, " << noneCounter << " unmodified) to " << outputFile << "." << endl;
}

}
}
