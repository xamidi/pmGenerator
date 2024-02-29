#include "DRuleReducer.h"

#include "../helper/FctHelper.h"
#include "../tree/TreeNode.h"
#include "../logic/DlCore.h"
#include "../logic/DlProofEnumerator.h"

#include <tbb/concurrent_map.h>
#include <tbb/concurrent_vector.h>
#include <tbb/parallel_for.h>

#include <boost/algorithm/string.hpp>

#include <numeric>

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::logic;

namespace xamidi {
namespace metamath {

void DRuleReducer::createReplacementsFile(const string& dProofDB, const string& outputFile, const string& dataLocation, const string& inputFilePrefix, bool withConclusions, bool debug) {
	// 1. Load and parse mmsolitaire's D-proofs.
	chrono::time_point<chrono::steady_clock> startTime;
	vector<string> dProofsInFile = DRuleParser::readFromMmsolitaireFile(dProofDB, nullptr, debug);
	if (debug)
		startTime = chrono::steady_clock::now();
	// Parse all proofs - including subproofs - from 'dProofDB'. Since such collections tend to contain only a few but large proofs
	// it it is likely fastest to parse them all combined (so redundant parts are never parsed twice), even when single-threaded.
	vector<DProofInfo> allProofs = DRuleParser::parseDProofs_raw(dProofsInFile, DlProofEnumerator::getCustomAxioms(), 1, nullptr, debug, false, true, false, false);
	//#cout << FctHelper::vectorStringF(allProofs, [](const DProofInfo& p) { return p.first + ":" + DlCore::toPolishNotation_noRename(get<0>(p.second).back()); }, "{\n\t", "\n}", "\n\t") << endl;
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken for parsing altogether." << endl;
		startTime = chrono::steady_clock::now();
	}
	// Translation from tree structures to Polish notation is still multi-threaded.
	// NOTE: A tbb::concurrent_set<string, cmpStringGrow> inside would be preferable, but it has no reverse iterators in order to directly address the last element (which is required later on),
	//       i.e. prev(set.end()) would crash and set.rbegin() does not exist: https://spec.oneapi.io/versions/latest/elements/oneTBB/source/containers/concurrent_set_cls/iterators.html
	tbb::concurrent_unordered_map<string, set<string, cmpStringGrow>> formulasToCheck;
	atomic<uint64_t> conclusionCounter = 0;
	atomic<uint64_t> redundantCounter = 0;
	mutex mtx_set;
	tbb::parallel_for(tbb::blocked_range<vector<DProofInfo>::const_iterator>(allProofs.begin(), allProofs.end()), [&formulasToCheck, &conclusionCounter, &redundantCounter, &mtx_set](tbb::blocked_range<vector<DProofInfo>::const_iterator>& range) {
		for (vector<DProofInfo>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const shared_ptr<DlFormula>& conclusion = get<0>(it->second).back();
			pair<tbb::concurrent_unordered_map<string, set<string, cmpStringGrow>>::iterator, bool> emplaceResult = formulasToCheck.emplace(DlCore::toPolishNotation_noRename(conclusion), set<string, cmpStringGrow> { });
			{
				lock_guard<mutex> lock(mtx_set);
				emplaceResult.first->second.insert(it->first); // store concrete proof string (disabled 'reversedAbstractProofStrings' in DRuleParser::parseDProofs_raw() call)
			}
			if (!emplaceResult.second) // a proof for the conclusion is already known
				redundantCounter++;
			else
				conclusionCounter++;
		}
	});
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to translate " << conclusionCounter + redundantCounter << " D-proof" << (conclusionCounter + redundantCounter == 1 ? "" : "s") << " (" << conclusionCounter << " conclusion" << (conclusionCounter == 1 ? "" : "s") << ", " << redundantCounter << " redundant)." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 2. Load and parse generated D-proofs.
	string fullInputFilePrefix = DlProofEnumerator::concatenateDataPath(dataLocation, inputFilePrefix);
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	vector<vector<string>> allConclusions; // TODO: Need ability to parse conclusions on-the-fly in order to save RAM for huge generator files.
	uint64_t allRepresentativesCount;
	uint32_t start;
	if (!DlProofEnumerator::loadDProofRepresentatives(allRepresentatives, withConclusions ? &allConclusions : nullptr, &allRepresentativesCount, &start, debug, fullInputFilePrefix)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}
	filePostfix = "-unfiltered" + to_string(start) + "+.txt";
	if (!DlProofEnumerator::loadDProofRepresentatives(allRepresentatives, withConclusions ? &allConclusions : nullptr, &allRepresentativesCount, &start, debug, fullInputFilePrefix, filePostfix, false)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}
	size_t showProgress_bound = 17;
	size_t parseProgressSteps5 = 29;
	size_t parseProgressSteps10 = 27;
	if (DlProofEnumerator::getCustomAxioms())
		DlProofEnumerator::readConfigFile(true, &showProgress_bound, &parseProgressSteps5, &parseProgressSteps10);
	bool showProgress = allRepresentatives.size() > showProgress_bound;
	ProgressData parseProgress = showProgress ? ProgressData(allRepresentatives.size() > parseProgressSteps5 ? 5 : allRepresentatives.size() > parseProgressSteps10 ? 10 : 20, allRepresentativesCount) : ProgressData();
	atomic<uint64_t> misses_speedupN = 0;
	tbb::concurrent_unordered_map<string, string> representativeProofs = withConclusions ? DlProofEnumerator::connectDProofConclusions(allRepresentatives, allConclusions, showProgress ? &parseProgress : nullptr) : DlProofEnumerator::parseDProofRepresentatives(allRepresentatives, showProgress ? &parseProgress : nullptr, debug ? &misses_speedupN : nullptr);
	if (debug) {
		cout << "Loaded and parsed " << representativeProofs.size() << " generated D-proof" << (withConclusions ? " conclusion" : "") << "s in " << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << "." << (misses_speedupN ? " Parsed " + to_string(misses_speedupN) + (misses_speedupN == 1 ? " proof" : " proofs") + " - i.e. ≈" + FctHelper::round((long double) misses_speedupN * 100 / allRepresentativesCount, 2) + "% - of the form Nα:Lβ, despite α:β allowing for composition based on previous results." : "") << endl;
		startTime = chrono::steady_clock::now();
	}

	// 3. Consider formulas from mmsolitaire's D-proofs in case there are suboptimal proofs used despite better ones are already known.
	atomic<uint64_t> inputConclusionCounter = 0;
	tbb::parallel_for(formulasToCheck.range(), [&representativeProofs, &inputConclusionCounter](tbb::concurrent_unordered_map<string, set<string, cmpStringGrow>>::range_type& range) {
		for (tbb::concurrent_unordered_map<string, set<string, cmpStringGrow>>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& currentBestDProof = *it->second.begin();
			pair<tbb::concurrent_unordered_map<string, string>::iterator, bool> emplaceResult = representativeProofs.emplace(it->first, currentBestDProof);
			if (emplaceResult.second)
				inputConclusionCounter++;
		}
	});
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to load " << inputConclusionCounter << " more D-proof" << (inputConclusionCounter == 1 ? "" : "s") << " from the input." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 4. Introduce a way to iterate formulas only up to a certain standard length (to greatly improve schema searching).
	tbb::concurrent_map<size_t, tbb::concurrent_vector<pair<const string*, string*>>> formulasByStandardLength;
	tbb::parallel_for(representativeProofs.range(), [&formulasByStandardLength](tbb::concurrent_unordered_map<string, string>::range_type& range) {
		for (tbb::concurrent_unordered_map<string, string>::iterator it = range.begin(); it != range.end(); ++it) {
			const string& formula = it->first;

			// Store (pointer to formula -> representative proof) pair w.r.t. symbolic length of the formula.
			formulasByStandardLength[DlCore::standardLen_polishNotation_noRename_numVars(formula)].emplace_back(&formula, &it->second);
		}
	});
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to create " << formulasByStandardLength.size() << " class" << (formulasByStandardLength.size() == 1 ? "" : "es") << " of formulas by their standard length." << endl;
		cout << "|representativeProofs| = " << representativeProofs.size() << ", |formulasByStandardLength| = " << formulasByStandardLength.size() << endl;
		//#cout << [](tbb::concurrent_map<size_t, tbb::concurrent_vector<pair<const string*, string*>>>& m) { stringstream ss; for (const pair<const unsigned, tbb::concurrent_vector<pair<const string*, string*>>>& p : m) { ss << p.first << ":" << p.second.size() << ", "; } return ss.str(); }(formulasByStandardLength) << endl;
		startTime = chrono::steady_clock::now();
	}
	auto iterateFormulasOfStandardLengthUpTo = [&formulasByStandardLength](const size_t upperBound, atomic<bool>& done, const auto& func) {
		tbb::parallel_for(formulasByStandardLength.range(), [&upperBound, &done, &func](tbb::concurrent_map<size_t, tbb::concurrent_vector<pair<const string*, string*>>>::range_type& range) {
			for (tbb::concurrent_map<size_t, tbb::concurrent_vector<pair<const string*, string*>>>::const_iterator it = range.begin(); it != range.end(); ++it)
				if (done)
					return;
				else if (it->first <= upperBound)
					for (const pair<const string*, string*>& p : it->second) {
						func(*p.first, *p.second);
						if (done)
							return;
					}
		});
	};

	// 5. Consider formulas of generated D-proofs that would soon be generated, i.e. for a proof α for A\implyB (with B yet unproven) such that A has a known proof β, consider proof Dαβ for B.
	// NOTE: While iterating all proofs α of A\implyB, do not look for schemas [which would take too long – similarly long as DlProofEnumerator::_removeRedundantConclusionsForProofsOfMaxLength()]
	//       but just use A as a key for search (which is fast). [The results may be less due to the schema-filtered generation process, i.e. there might be an overlooked proof for a proper schema of A.]
	//       If a proof β for A can be found, just emplace Dαβ for B without verifying that B has not been proven yet. If a proof of B is already contained, Dαβ will be ignored.
	//       Issue: Not using schema search barely gives extra results, but using it takes very long (so that generating them permanently via DlProofEnumerator is a better option).
	atomic<uint64_t> extraCheckCounter = 0;
	atomic<uint64_t> extraParseCounter = 0;
	atomic<uint64_t> extraProofCounter = 0;
	atomic<uint64_t> improvedProofCounter = 0;
	tbb::parallel_for(representativeProofs.range(), [&representativeProofs, &formulasByStandardLength, &extraCheckCounter, &extraParseCounter, &extraProofCounter, &improvedProofCounter](tbb::concurrent_unordered_map<string, string>::range_type& range) {
		for (tbb::concurrent_unordered_map<string, string>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& conditional = it->first;
			if (conditional[0] == 'C') { // actually a conditional, i.e. A\implyB
				extraCheckCounter++;

				// 5.1 Determine antecedent of the conditional.
				string::size_type finalIndex = DlCore::traverseFormulas_polishNotation_noRename_numVars(conditional, 1);
				if (conditional.begin() + finalIndex == conditional.end())
					throw logic_error("Failed to determine bounds of antecedent of conditional \"" + conditional + "\"");
				const string antecedent = conditional.substr(1, finalIndex); // A
				// NOTE: Since the antecedent is the first part of its conditional, its variables are good for searching in 'representativeProofs' (i.e. they start from "0").
				//#{ static mutex mtx_cout; lock_guard<mutex> lock(mtx_cout); cout << "### antecedent: " << antecedent << ", conditional: " << conditional << endl; }

				tbb::concurrent_unordered_map<string, string>::const_iterator searchResult = representativeProofs.find(antecedent);
				if (searchResult != representativeProofs.end()) { // whether there is a proof with A being the literal consequent

					// 5.2 Emplace conditional with its proof (in case there is a proof for antecedent).
					string dProof = "D" + it->second + searchResult->second; // proof Dαβ for B
					extraParseCounter++;
					// NOTE: If parsing took too long, we could clone B and substitute its variables to start from "0". But parsing isn't an issue here at all.
					vector<DProofInfo> rawParseData = DRuleParser::parseDProof_raw(dProof, DlProofEnumerator::getCustomAxioms(), 1);
					const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
					pair<tbb::concurrent_unordered_map<string, string>::iterator, bool> emplaceResult = representativeProofs.emplace(DlCore::toPolishNotation_noRename(conclusion), dProof);

					// 5.3 Update the structure for efficient iteration
					if (emplaceResult.second) { // a proof for the conclusion was not already known
						extraProofCounter++;
						const string& formula = emplaceResult.first->first; // NOTE: It is crucial that the stored address (which remains valid) is used.

						// Store (pointer to formula -> representative proof) pair w.r.t. symbolic length of the formula.
						formulasByStandardLength[DlCore::standardLen_polishNotation_noRename_numVars(formula)].emplace_back(&formula, &emplaceResult.first->second);
					} else { // NOTE: Usually never happens.
						static mutex mtx_modify;
						lock_guard<mutex> lock(mtx_modify);
						if (dProof.length() < emplaceResult.first->second.length() || (dProof.length() == emplaceResult.first->second.length() && dProof < emplaceResult.first->second)) {
							improvedProofCounter++;
							//#{ static mutex mtx_cout; lock_guard<mutex> lock(mtx_cout); cerr << "Found better D-proof ; new: " << dProof << " (length " << dProof.length() << ") ; old: " << emplaceResult.first->second << " (length " << emplaceResult.first->second.length() << ") ; formula: " << emplaceResult.first->first << endl; }

							// Overwrite stored D-proof (which is also referenced by 'formulasByStandardLength').
							emplaceResult.first->second = dProof;
						}
					}
					//#{ static mutex mtx_cout; lock_guard<mutex> lock(mtx_cout); cerr << "Direct hit! ; So far checked " << extraCheckCounter << " conditionals, parsed " << extraParseCounter << " candidates, and found " << extraProofCounter << " new and " << improvedProofCounter << " improved D-proofs from existing combinations. ; proof: " << dProof << " (length " << dProof.length() << ") ; formula: " << emplaceResult.first->first << endl; }
				}
			}
		}
	});
	// NOTE: Doesn't seem to generate much, e.g. 27: 13366.48 ms taken to check 1733457 conditionals, parse 3 candidates, and load 3 extra D-proofs from existing combinations.
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to check " << extraCheckCounter << " conditionals, parse " << extraParseCounter << " candidates, and load " << extraProofCounter << " new and " << improvedProofCounter << " improved D-proofs from existing combinations." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 6. Search for shorter proofs.
	tbb::concurrent_map<string, string, cmpStringShrink> shorteningReplacements;
	tbb::concurrent_map<string, string, cmpStringShrink> stylingReplacements;
	atomic<uint64_t> schemaCheckCounter = 0;
	mutex mtx_cout;
	tbb::parallel_for(formulasToCheck.range(), [&debug, &iterateFormulasOfStandardLengthUpTo, &shorteningReplacements, &stylingReplacements, &schemaCheckCounter, &mtx_cout](tbb::concurrent_unordered_map<string, set<string, cmpStringGrow>>::range_type& range) {
		for (tbb::concurrent_unordered_map<string, set<string, cmpStringGrow>>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& formula = it->first;
			const set<string, cmpStringGrow>& dProofs = it->second;
			const string& currentWorstDProof = *dProofs.rbegin(); // NOTE: Using set<string, cmpStringGrow> instead of tbb::concurrent_set<string, cmpStringGrow>, avoids doing *next(dProofs.begin(), dProofs.size() - 1) each time.
			//#if (dProofs.size() > 1) { lock_guard<mutex> lock(mtx_cout); cout << "currentWorstDProof = " << currentWorstDProof << ", dProofs = " << FctHelper::setString(dProofs) << endl; }
			const string::size_type currentWorstLength = currentWorstDProof.length();
			atomic<bool> done = false; // NOTE: Shall not be used to abort the below iterateFormulasOfStandardLengthUpTo(), since it is possible that multiple schemas with different proof sizes of the same formula are stored representatives.
			mutex mtx_best;
			bool bad = false;
			string bestSchema;
			string bestDProof;
			mutex mtx_alt;
			bool alt = false;
			set<string, cmpStringGrow> alternativeDProofs;
			size_t formulaLen = DlCore::standardLen_polishNotation_noRename_numVars(formula);
			iterateFormulasOfStandardLengthUpTo(formulaLen, done, [&schemaCheckCounter, &formula, &currentWorstDProof, &currentWorstLength, &mtx_best, &bad, &bestSchema, &bestDProof, &mtx_alt, &alt, &alternativeDProofs](const string& potentialSchema, const string& dProof) {
				if (dProof.length() <= currentWorstLength) {
					schemaCheckCounter++;
					if (DlCore::isSchemaOf_polishNotation_noRename_numVars_vec(potentialSchema, formula)) { // found a schema
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
				} else
					for (const string& dProof : dProofs)
						if (dProof != bestAlternative)
							stylingReplacements.emplace(dProof, bestAlternative);
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
						cout << "[NOTE] Found shorter proof \"" << bestDProof << "\" (length " << bestDProof.length() << ") for { " << setStr(dProofs, bestDProof.length(), true, true, bestDProof) << " }, best schema: " << bestSchema << endl;
					if (!bad || hasMereAlternatives) // NOTE: !bad => bestDProof.length() == 0, thus printing longer proofs prints them all.
						cout << "[NOTE] Found alternative proof " + bestAlternative + " for { " << setStr(dProofs, bestDProof.length(), !bad, false, bestAlternative) << " }." << endl;
				}
			}
		}
	});
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken for " << schemaCheckCounter << " schema checks." << endl;
		startTime = chrono::steady_clock::now();
	}

#if 1 //### TODO: "shaking": To combine strengths of multiple heterogeneous proofs. Some smaller rules may be better than some larger rules. Look for better paths to take!
	// (down,large) : ./pmGenerator_shaky ; (!down,large) : ./pmGenerator_shakyUp ; (down,!large) : ./pmGenerator_shakyN ; (!down,!large) : ./pmGenerator_shakyNUp
	bool shakeDown = true;
	bool largeShaking = true;
	vector<tbb::concurrent_map<string, string, cmpStringShrink>::iterator> reverseShorteningReplacements;
	if (!shakeDown) { // tbb::concurrent_map lacks reverse iterators, so reverse iterate manually
		reverseShorteningReplacements.resize(shorteningReplacements.size());
		size_t i = shorteningReplacements.size();
		for (tbb::concurrent_map<string, string, cmpStringShrink>::iterator it = shorteningReplacements.begin(); it != shorteningReplacements.end(); ++it)
			reverseShorteningReplacements[--i] = it;
	}
	size_t num = 0;
	auto replacementLengths = [&](size_t* sum) { if (sum) *sum = 0; stringstream ss; bool first = true; for (tbb::concurrent_map<string, string, cmpStringShrink>::iterator it = shorteningReplacements.begin(); it != shorteningReplacements.end(); ++it) { if (first) first = false; else ss << ", "; if (sum) *sum += it->second.length(); ss << it->second.length(); } return ss.str(); };
	size_t sum;
	cout << "[NOTE] Lengths before: " << replacementLengths(&sum) << endl;
	cout << "[NOTE] Summed up lengths before: " << sum << endl;
	auto procEntry = [&](tbb::concurrent_map<string, string, cmpStringShrink>::iterator it) {
		const string& key = it->first;
		string& replacement = it->second;
		//#size_t counter = 0;
		vector<tbb::concurrent_map<string, string, cmpStringShrink>::iterator> candidatesForImprovement;
		while (++it != shorteningReplacements.end()) { // long to short keys that are shorter than the key of the current replacement to improve
			if (largeShaking || key.find(it->first) != string::npos)
				candidatesForImprovement.push_back(it);
			//#counter++;
		}
		//#cout << "[keylen " << key.length() << ", replen " << replacement.length() << "] has " << counter << " shorter replacements. ; " << candidatesForImprovement.size() << " candidates for improvement" << endl; //### TODO
		if (!candidatesForImprovement.empty()) {
			string bestResult;
			vector<thread> threads;
			unsigned concurrencyCount = thread::hardware_concurrency(); //### TODO As parameter?
			tbb::concurrent_bounded_queue<vector<size_t>> queue;
			queue.set_capacity(5 * concurrencyCount);
			mutex mtx;
			atomic<bool> incomplete = true;
			auto process = [&](const vector<size_t>& indices) {
				string key_copy = key;
				for (size_t i : indices) {
					tbb::concurrent_map<string, string, cmpStringShrink>::iterator& entry = candidatesForImprovement[i];
					boost::replace_all(key_copy, entry->first, entry->second);
				}
				{
					lock_guard<mutex> lock(mtx);
					if (bestResult.empty() || key_copy.length() < bestResult.length()) {
						//#if (!bestResult.empty())
						//#	cout << "NOTE: New best result, previously " << bestResult.length() << ", now " << key_copy.length() << "." << endl;
						bestResult = key_copy;
					}
				}
			};
			auto worker = [&process, &queue, &incomplete]() {
				// NOTE: It is important to check '!queue.empty()' in loop header _after_ 'incomplete', since 'queue' might
				//       become filled and 'incomplete' false, while this condition is being processed in this thread.
				//       Since 'incomplete' can only become false after all queues are filled and no more balancing will
				//       take place, evaluating 'incomplete' first ensures that whenever 'queue' is not filled completely,
				//       the loop remains active, i.e. whenever !incomplete holds (such that '!queue.empty()' is checked here),
				//       the loop is discontinued only if there is nothing left to process.
				while (incomplete || !queue.empty()) {
					vector<size_t> s;
					if (queue.try_pop(s))
						process(s);
					else
						this_thread::yield();
				}
			};
			for (unsigned t = 0; t < concurrencyCount; t++)
				threads.emplace_back(worker);
			auto registerReplacements = [&](const vector<size_t>& indices) {
				queue.push(indices);
			};
			if (candidatesForImprovement.size() <= 7) {
				// NOTE: Choose 7! as the maximum amount of permutations to test for guaranteed perfect results. (6! = 720, 7! = 5040, 8! = 40320, 9! = 362880)
				vector<size_t> indices(candidatesForImprovement.size());
				iota(indices.begin(), indices.end(), 0);
				size_t counter = 0;
				startTime = chrono::steady_clock::now(); //### TODO
				do {
					registerReplacements(indices);
					counter++;
				} while (next_permutation(indices.begin(), indices.end()));
				incomplete = false;
				for (thread& t : threads)
					t.join();
				//# TODO
				cout << "[Full, " << ++num << " / " << shorteningReplacements.size() << "] Applied " << counter << " permutations in " << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms." << endl;
			} else {
				size_t counter = 0;
				startTime = chrono::steady_clock::now(); //### TODO
				// NOTE: There are too many possibilities. We only test all indices as start, then all valid 2-tuples over { start -> bottom, start -> top, top -> start, bottom -> start }, of which there are
				//       |{ up, down }^2 x { top first, bottom first }| = 4 * 2 = 8. This makes 8 * |candidatesForImprovement| an upper bound for the amount of sequences to be tested per replacements entry. [O(n^2) overall]
				vector<size_t> indices(candidatesForImprovement.size());
				for (size_t start = 0; start < candidatesForImprovement.size(); start++) {
					indices[0] = start;
					// 1. ( start  -> top   , bottom -> start  ) ; e.g. [5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4]
					if (start && start + 1 < candidatesForImprovement.size()) { // would be the same as (5.) for start == 0 || start == candidatesForImprovement.size() - 1
						iota(indices.begin() + 1, indices.end() - start, start + 1); // add increasing indices (start + 1, candidatesForImprovement.size() - 1)
						iota(indices.begin() + indices.size() - start, indices.end(), 0); // add increasing indices (0, start - 1)
						//#cout << "1. [ start  -> top   , bottom -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 2. ( start  -> top   , start  -> bottom ) ; e.g. [5, 6, 7, 8, 9, 10, 11, 4, 3, 2, 1, 0]
					if (start > 1 && start + 2 < candidatesForImprovement.size()) { // would be the same as (5.) for start == 0, the same as (4.) for start >= candidatesForImprovement.size() - 2, and the same as (1.) for start == 1
						iota(indices.begin() + 1, indices.end() - start, start + 1); // add increasing indices (start + 1, candidatesForImprovement.size() - 1)
						iota(indices.rbegin(), indices.rend() - indices.size() + start, 0); // add decreasing indices (start - 1, ..., 0)
						//#cout << "2. [ start  -> top   , start  -> bottom ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 3. ( top    -> start , bottom -> start  ) ; e.g. [5, 11, 10, 9, 8, 7, 6, 0, 1, 2, 3, 4]
					if (start > 1 && start + 2 < candidatesForImprovement.size()) { // would be the same as (4.) for start <= 1, the same as (5.) for start == candidatesForImprovement.size() - 1, and the same as (1.) for start == candidatesForImprovement.size() - 2
						iota(indices.rbegin() + start, indices.rend() - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						iota(indices.begin() + indices.size() - start, indices.end(), 0); // add increasing indices (0, start - 1)
						//#cout << "3. [ top    -> start , bottom -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 4. ( top    -> start , start  -> bottom ) ; e.g. [5, 11, 10, 9, 8, 7, 6, 4, 3, 2, 1, 0]
					{
						iota(indices.rbegin() + start, indices.rend() - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						iota(indices.rbegin(), indices.rend() - indices.size() + start, 0); // add decreasing indices (start - 1, ..., 0)
						//#cout << "4. [ top    -> start , start  -> bottom ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 5. ( bottom -> start , start  -> top    ) ; e.g. [5, 0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11]
					{
						iota(indices.begin() + 1, indices.begin() + start + 1, 0); // add increasing indices (0, start - 1)
						iota(indices.begin() + start + 1, indices.end(), start + 1); // add increasing indices (start + 1, ..., candidatesForImprovement.size() - 1)
						//#cout << "5. [ bottom -> start , start  -> top    ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 6. ( bottom -> start , top    -> start  ) ; e.g. [5, 0, 1, 2, 3, 4, 11, 10, 9, 8, 7, 6]
					if (start && start + 2 < candidatesForImprovement.size()) { // would be the same as (4.) for start == 0 and the same as (5.) for start >= candidatesForImprovement.size() - 2
						iota(indices.begin() + 1, indices.begin() + start + 1, 0); // add increasing indices (0, start - 1)
						iota(indices.rbegin(), indices.rend() - start - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						//#cout << "6. [ bottom -> start , top    -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 7. ( start  -> bottom, start  -> top    ) ; e.g. [5, 4, 3, 2, 1, 0, 6, 7, 8, 9, 10, 11]
					if (start > 1 && start + 1 < candidatesForImprovement.size()) { // would be the same as (5.) for start <= 1 and the same as (4.) for start == candidatesForImprovement.size() - 1
						iota(indices.rbegin() + indices.size() - start - 1, indices.rend() - 1, 0); // add decreasing indices (start - 1, ..., 0)
						iota(indices.begin() + start + 1, indices.end(), start + 1); // add increasing indices (start + 1, ..., candidatesForImprovement.size() - 1)
						//#cout << "7. [ start  -> bottom, start  -> top    ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 8. ( start  -> bottom, top    -> start  ) ; e.g. [5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6]
					if (start > 1 && start + 2 < candidatesForImprovement.size()) { // would be the same as (4.) for start == 0 || start == candidatesForImprovement.size() - 1, the same as (6.) for start == 1, and the same as (7.) for start == candidatesForImprovement.size() - 2
						iota(indices.rbegin() + indices.size() - start - 1, indices.rend() - 1, 0); // add decreasing indices (start - 1, ..., 0)
						iota(indices.rbegin(), indices.rend() - start - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						//#cout << "8. [ start  -> bottom, top    -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
				}
				incomplete = false;
				for (thread& t : threads)
					t.join();
				//# TODO
				cout << "[Part, " << ++num << " / " << shorteningReplacements.size() << "] Applied " << counter << " permutations in " << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms." << endl;
			}
			if (replacement.length() > bestResult.length()) {
				cout << "Replacement improved from length " << replacement.length() << " to " << bestResult.length() << "." << endl;
				replacement = bestResult;
			}
		} else
			++num;
	};
	if (shakeDown)
		for (tbb::concurrent_map<string, string, cmpStringShrink>::iterator it = shorteningReplacements.begin(); it != shorteningReplacements.end(); ++it) // long to short keys
			procEntry(it);
	else
		for (tbb::concurrent_map<string, string, cmpStringShrink>::iterator it : reverseShorteningReplacements) // short to long keys
			procEntry(it);
	cout << "[NOTE] Lengths after: " << replacementLengths(&sum) << endl;
	cout << "[NOTE] Summed up lengths after: " << sum << endl;
	//### TODO
#endif

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

void DRuleReducer::applyReplacements(const string& initials, const string& replacementsFile, const string& dProofDB, const string& outputFile, bool styleAll, bool listAll, bool wrap, bool debug) {
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
		while (getline(fin, line))
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
		if (debug)
			cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to read " << shorteningReplacements.size() << " shortening replacements and " << stylingReplacements.size() << " styling replacements." << endl;
		//#cout << "shorteningReplacements = " << FctHelper::vectorStringF(shorteningReplacements, [](const pair<string, string>& p) { return p.first + "," + p.second; }, "{\n\t", "\n}", "\n\t") << endl;
		//#cout << "stylingReplacements = " << FctHelper::vectorStringF(stylingReplacements, [](const pair<string, string>& p) { return p.first + "," + p.second; }, "{\n\t", "\n}", "\n\t") << endl;
	}

#if 1 //### TODO: "shaking": To combine strengths of multiple heterogeneous proofs. Some smaller rules may be better than some larger rules. Look for better paths to take!
	// (down,large) : ./pmGenerator_shaky ; (!down,large) : ./pmGenerator_shakyUp ; (down,!large) : ./pmGenerator_shakyN ; (!down,!large) : ./pmGenerator_shakyNUp
	bool shakeDown = true;
	bool largeShaking = true;
	vector<vector<pair<string, string>>::iterator> reverseShorteningReplacements;
	if (!shakeDown) { // tbb::concurrent_map lacks reverse iterators, so reverse iterate manually
		reverseShorteningReplacements.resize(shorteningReplacements.size());
		size_t i = shorteningReplacements.size();
		for (vector<pair<string, string>>::iterator it = shorteningReplacements.begin(); it != shorteningReplacements.end(); ++it)
			reverseShorteningReplacements[--i] = it;
	}
	size_t num = 0;
	auto replacementLengths = [&](size_t* sum) { if (sum) *sum = 0; stringstream ss; bool first = true; for (vector<pair<string, string>>::iterator it = shorteningReplacements.begin(); it != shorteningReplacements.end(); ++it) { if (first) first = false; else ss << ", "; if (sum) *sum += it->second.length(); ss << it->second.length(); } return ss.str(); };
	size_t sum;
	cout << "[NOTE] Lengths before: " << replacementLengths(&sum) << endl;
	cout << "[NOTE] Summed up lengths before: " << sum << endl;
	auto procEntry = [&](vector<pair<string, string>>::iterator it) {
		const string& key = it->first;
		string& replacement = it->second;
		//#size_t counter = 0;
		vector<vector<pair<string, string>>::iterator> candidatesForImprovement;
		while (++it != shorteningReplacements.end()) { // long to short keys that are shorter than the key of the current replacement to improve
			if (largeShaking || key.find(it->first) != string::npos)
				candidatesForImprovement.push_back(it);
			//#counter++;
		}
		//#cout << "[keylen " << key.length() << ", replen " << replacement.length() << "] has " << counter << " shorter replacements. ; " << candidatesForImprovement.size() << " candidates for improvement" << endl; //### TODO
		if (!candidatesForImprovement.empty()) {
			string bestResult;
			vector<thread> threads;
			unsigned concurrencyCount = thread::hardware_concurrency(); //### TODO As parameter?
			tbb::concurrent_bounded_queue<vector<size_t>> queue;
			queue.set_capacity(5 * concurrencyCount);
			mutex mtx;
			atomic<bool> incomplete = true;
			auto process = [&](const vector<size_t>& indices) {
				string key_copy = key;
				for (size_t i : indices) {
					vector<pair<string, string>>::iterator& entry = candidatesForImprovement[i];
					boost::replace_all(key_copy, entry->first, entry->second);
				}
				{
					lock_guard<mutex> lock(mtx);
					if (bestResult.empty() || key_copy.length() < bestResult.length()) {
						//#if (!bestResult.empty())
						//#	cout << "NOTE: New best result, previously " << bestResult.length() << ", now " << key_copy.length() << "." << endl;
						bestResult = key_copy;
					}
				}
			};
			auto worker = [&process, &queue, &incomplete]() {
				// NOTE: It is important to check '!queue.empty()' in loop header _after_ 'incomplete', since 'queue' might
				//       become filled and 'incomplete' false, while this condition is being processed in this thread.
				//       Since 'incomplete' can only become false after all queues are filled and no more balancing will
				//       take place, evaluating 'incomplete' first ensures that whenever 'queue' is not filled completely,
				//       the loop remains active, i.e. whenever !incomplete holds (such that '!queue.empty()' is checked here),
				//       the loop is discontinued only if there is nothing left to process.
				while (incomplete || !queue.empty()) {
					vector<size_t> s;
					if (queue.try_pop(s))
						process(s);
					else
						this_thread::yield();
				}
			};
			for (unsigned t = 0; t < concurrencyCount; t++)
				threads.emplace_back(worker);
			auto registerReplacements = [&](const vector<size_t>& indices) {
				queue.push(indices);
			};
			if (candidatesForImprovement.size() <= 7) {
				// NOTE: Choose 7! as the maximum amount of permutations to test for guaranteed perfect results. (6! = 720, 7! = 5040, 8! = 40320, 9! = 362880)
				vector<size_t> indices(candidatesForImprovement.size());
				iota(indices.begin(), indices.end(), 0);
				size_t counter = 0;
				startTime = chrono::steady_clock::now(); //### TODO
				do {
					registerReplacements(indices);
					counter++;
				} while (next_permutation(indices.begin(), indices.end()));
				incomplete = false;
				for (thread& t : threads)
					t.join();
				//# TODO
				cout << "[Full, " << ++num << " / " << shorteningReplacements.size() << "] Applied " << counter << " permutations in " << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms." << endl;
			} else {
				size_t counter = 0;
				startTime = chrono::steady_clock::now(); //### TODO
				// NOTE: There are too many possibilities. We only test all indices as start, then all valid 2-tuples over { start -> bottom, start -> top, top -> start, bottom -> start }, of which there are
				//       |{ up, down }^2 x { top first, bottom first }| = 4 * 2 = 8. This makes 8 * |candidatesForImprovement| an upper bound for the amount of sequences to be tested per replacements entry. [O(n^2) overall]
				vector<size_t> indices(candidatesForImprovement.size());
				for (size_t start = 0; start < candidatesForImprovement.size(); start++) {
					indices[0] = start;
					// 1. ( start  -> top   , bottom -> start  ) ; e.g. [5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4]
					if (start && start + 1 < candidatesForImprovement.size()) { // would be the same as (5.) for start == 0 || start == candidatesForImprovement.size() - 1
						iota(indices.begin() + 1, indices.end() - start, start + 1); // add increasing indices (start + 1, candidatesForImprovement.size() - 1)
						iota(indices.begin() + indices.size() - start, indices.end(), 0); // add increasing indices (0, start - 1)
						//#cout << "1. [ start  -> top   , bottom -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 2. ( start  -> top   , start  -> bottom ) ; e.g. [5, 6, 7, 8, 9, 10, 11, 4, 3, 2, 1, 0]
					if (start > 1 && start + 2 < candidatesForImprovement.size()) { // would be the same as (5.) for start == 0, the same as (4.) for start >= candidatesForImprovement.size() - 2, and the same as (1.) for start == 1
						iota(indices.begin() + 1, indices.end() - start, start + 1); // add increasing indices (start + 1, candidatesForImprovement.size() - 1)
						iota(indices.rbegin(), indices.rend() - indices.size() + start, 0); // add decreasing indices (start - 1, ..., 0)
						//#cout << "2. [ start  -> top   , start  -> bottom ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 3. ( top    -> start , bottom -> start  ) ; e.g. [5, 11, 10, 9, 8, 7, 6, 0, 1, 2, 3, 4]
					if (start > 1 && start + 2 < candidatesForImprovement.size()) { // would be the same as (4.) for start <= 1, the same as (5.) for start == candidatesForImprovement.size() - 1, and the same as (1.) for start == candidatesForImprovement.size() - 2
						iota(indices.rbegin() + start, indices.rend() - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						iota(indices.begin() + indices.size() - start, indices.end(), 0); // add increasing indices (0, start - 1)
						//#cout << "3. [ top    -> start , bottom -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 4. ( top    -> start , start  -> bottom ) ; e.g. [5, 11, 10, 9, 8, 7, 6, 4, 3, 2, 1, 0]
					{
						iota(indices.rbegin() + start, indices.rend() - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						iota(indices.rbegin(), indices.rend() - indices.size() + start, 0); // add decreasing indices (start - 1, ..., 0)
						//#cout << "4. [ top    -> start , start  -> bottom ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 5. ( bottom -> start , start  -> top    ) ; e.g. [5, 0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11]
					{
						iota(indices.begin() + 1, indices.begin() + start + 1, 0); // add increasing indices (0, start - 1)
						iota(indices.begin() + start + 1, indices.end(), start + 1); // add increasing indices (start + 1, ..., candidatesForImprovement.size() - 1)
						//#cout << "5. [ bottom -> start , start  -> top    ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 6. ( bottom -> start , top    -> start  ) ; e.g. [5, 0, 1, 2, 3, 4, 11, 10, 9, 8, 7, 6]
					if (start && start + 2 < candidatesForImprovement.size()) { // would be the same as (4.) for start == 0 and the same as (5.) for start >= candidatesForImprovement.size() - 2
						iota(indices.begin() + 1, indices.begin() + start + 1, 0); // add increasing indices (0, start - 1)
						iota(indices.rbegin(), indices.rend() - start - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						//#cout << "6. [ bottom -> start , top    -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 7. ( start  -> bottom, start  -> top    ) ; e.g. [5, 4, 3, 2, 1, 0, 6, 7, 8, 9, 10, 11]
					if (start > 1 && start + 1 < candidatesForImprovement.size()) { // would be the same as (5.) for start <= 1 and the same as (4.) for start == candidatesForImprovement.size() - 1
						iota(indices.rbegin() + indices.size() - start - 1, indices.rend() - 1, 0); // add decreasing indices (start - 1, ..., 0)
						iota(indices.begin() + start + 1, indices.end(), start + 1); // add increasing indices (start + 1, ..., candidatesForImprovement.size() - 1)
						//#cout << "7. [ start  -> bottom, start  -> top    ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
					// 8. ( start  -> bottom, top    -> start  ) ; e.g. [5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6]
					if (start > 1 && start + 2 < candidatesForImprovement.size()) { // would be the same as (4.) for start == 0 || start == candidatesForImprovement.size() - 1, the same as (6.) for start == 1, and the same as (7.) for start == candidatesForImprovement.size() - 2
						iota(indices.rbegin() + indices.size() - start - 1, indices.rend() - 1, 0); // add decreasing indices (start - 1, ..., 0)
						iota(indices.rbegin(), indices.rend() - start - 1, start + 1); // add decreasing indices (candidatesForImprovement.size() - 1, ..., start + 1)
						//#cout << "8. [ start  -> bottom, top    -> start  ] ; start = " << start << ", indices: " << FctHelper::vectorString(indices) << endl;
						registerReplacements(indices);
						counter++;
					}
				}
				incomplete = false;
				for (thread& t : threads)
					t.join();
				//# TODO
				cout << "[Part, " << ++num << " / " << shorteningReplacements.size() << "] Applied " << counter << " permutations in " << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms." << endl;
			}
			if (replacement.length() > bestResult.length()) {
				cout << "Replacement improved from length " << replacement.length() << " to " << bestResult.length() << "." << endl;
				replacement = bestResult;
			}
		} else
			++num;
	};
	if (shakeDown)
		for (vector<pair<string, string>>::iterator it = shorteningReplacements.begin(); it != shorteningReplacements.end(); ++it) // long to short keys
			procEntry(it);
	else
		for (vector<pair<string, string>>::iterator it : reverseShorteningReplacements) // short to long keys
			procEntry(it);
	cout << "[NOTE] Lengths after: " << replacementLengths(&sum) << endl;
	cout << "[NOTE] Summed up lengths after: " << sum << endl;

	// [TMP] Store useful replacements.
	string replacementsOutputFile = replacementsFile + "_shaken.txt";
	string content = FctHelper::vectorStringF(shorteningReplacements, [](const pair<string, string>& p) { return p.first + "," + p.second; }, { }, "\n\n", "\n") + FctHelper::vectorStringF(stylingReplacements, [](const pair<string, string>& p) { return p.first + "," + p.second; }, { }, "\n", "\n");
	FctHelper::writeToFile(replacementsOutputFile, content);
	if (debug)
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << content.length() << " bytes of condensed detachment proof replacement strings to " << replacementsOutputFile << "." << endl;
	else
		cout << "Condensed detachment proof replacement strings saved to " << replacementsOutputFile << "." << endl;
	//### TODO
#endif

	// 2. Load mmsolitaire's D-proofs.
	vector<string> dProofNamesInFile;
	vector<string> dProofsInFile = DRuleParser::readFromMmsolitaireFile(dProofDB, &dProofNamesInFile, debug);
	if (debug)
		startTime = chrono::steady_clock::now();
	vector<string::size_type> prevLengths(dProofsInFile.size());
	for (size_t i = 0; i < dProofsInFile.size(); i++)
		prevLengths[i] = dProofsInFile[i].length();
	if (debug) {
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to store " << dProofsInFile.size() << " lengths." << endl;
		startTime = chrono::steady_clock::now();
	}

	// 3. Apply replacements.
	enum class Modification {
		None = 0, Styled = 1, Shorter = 2
	};
	vector<Modification> modifications(dProofsInFile.size());
	for (size_t i = 0; i < dProofsInFile.size(); i++) {
		const string originalDProof = dProofsInFile[i];
		string& dProofName = dProofNamesInFile[i];
		string& dProof = dProofsInFile[i];
		for (pair<string, string>& replacement : shorteningReplacements)
			boost::replace_all(dProof, replacement.first, replacement.second);
		if (originalDProof != dProof) { // could actually reduce that proof
			modifications[i] = Modification::Shorter;
			const string reducedDProof = debug ? dProof : string { };
			if (debug)
				cerr << "[NOTE] Could reduce \"" << dProofName << "\" from " << originalDProof.length() << " to " << dProof.length() << " steps. Before applying styling replacements: " << dProof << endl;
			for (pair<string, string>& replacement : stylingReplacements)
				boost::replace_all(dProof, replacement.first, replacement.second);
			if (debug) {
				if (reducedDProof != dProof)
					cout << "[NOTE] Could further modify \"" << dProofName << "\" with styling replacements: " << dProof << endl;
				else
					cout << "[NOTE] Couldn't further modify \"" << dProofName << "\" with applying styling replacements." << endl;
			}
		} else if (styleAll) {
			for (pair<string, string>& replacement : stylingReplacements)
				boost::replace_all(dProof, replacement.first, replacement.second);
			if (originalDProof != dProof) {
				modifications[i] = Modification::Styled;
				if (debug)
					cout << "[NOTE] Could modify \"" << dProofName << "\" with styling replacements: " << dProof << endl;
			}
		}
	}
	if (debug)
		cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to apply replacements." << endl;
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
			shared_ptr<DlFormula> consequent = DRuleParser::parseMmConsequent(context.substr(0, semIndex), false);

			// Check if we can substitute to desired consequent.
			vector<DProofInfo> rawParseData = DRuleParser::parseDProof_raw(dProof, DlProofEnumerator::getCustomAxioms(), 1);
			const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
			shared_ptr<DlFormula> reference = DlCore::toBasicDlFormula(consequent, nullptr, nullptr, nullptr, false);
			if (!DlCore::isSchemaOf(conclusion, reference))
				throw invalid_argument("DRuleReducer::applyReplacements(): (" + context + ") " + DlCore::formulaRepresentation_traverse(conclusion) + " is not a schema of BasicDL(consequent) " + DlCore::formulaRepresentation_traverse(reference) + ".");

			// Obtain result from conclusion.
			static const map<string, shared_ptr<DlFormula>> resultSubstitutions { { { "0", make_shared<DlFormula>(make_shared<String>("P")) }, { "1", make_shared<DlFormula>(make_shared<String>("Q")) }, { "2", make_shared<DlFormula>(make_shared<String>("R")) }, { "3", make_shared<DlFormula>(make_shared<String>("S")) }, { "4", make_shared<DlFormula>(make_shared<String>("T")) }, { "5", make_shared<DlFormula>(make_shared<String>("U")) }, { "6", make_shared<DlFormula>(make_shared<String>("V")) }, { "7", make_shared<DlFormula>(make_shared<String>("W")) }, { "8", make_shared<DlFormula>(make_shared<String>("X")) }, { "9", make_shared<DlFormula>(make_shared<String>("Y")) }, { "10", make_shared<DlFormula>(make_shared<String>("Z")) }, { "11", make_shared<DlFormula>(make_shared<String>("A")) }, { "12", make_shared<DlFormula>(make_shared<String>("B")) }, { "13", make_shared<DlFormula>(make_shared<String>("C")) }, { "14", make_shared<DlFormula>(make_shared<String>("D")) }, { "15", make_shared<DlFormula>(make_shared<String>("E")) }, { "16", make_shared<DlFormula>(make_shared<String>("F")) }, { "17", make_shared<DlFormula>(make_shared<String>("G")) }, { "18", make_shared<DlFormula>(make_shared<String>("H")) }, { "19", make_shared<DlFormula>(make_shared<String>("I")) }, { "20", make_shared<DlFormula>(make_shared<String>("J")) }, { "21", make_shared<DlFormula>(make_shared<String>("K")) }, { "22", make_shared<DlFormula>(make_shared<String>("L")) }, { "23", make_shared<DlFormula>(make_shared<String>("M")) }, { "24", make_shared<DlFormula>(make_shared<String>("N")) }, { "25", make_shared<DlFormula>(make_shared<String>("O")) } } };
			shared_ptr<DlFormula> result = DlCore::substitute(conclusion, resultSubstitutions);

			// Convert result.
			string f = DlCore::standardFormulaRepresentation(result);
			boost::replace_all(f, DlCore::terminalStr_not(), "~ ");
			boost::replace_all(f, DlCore::terminalStr_nece(), "□ ");
			boost::replace_all(f, DlCore::terminalStr_imply(), " -> ");
			return f + "; ! Result of proof\n";
		};
		const string& head = dProofNamesInFile[i];
		const string& dStr = dProofsInFile[i];
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
		while (getline(ss, line))
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
		result = ss_wrap.str();
	} else
		result = ss.str();
	FctHelper::writeToFile(outputFile, result);
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to check, generate and save " << result.length() << " bytes of MM-styled condensed detachment proofs (" << shorterCounter << " shortened, " << styledCounter << " styled, " << noneCounter << " unmodified) to " << outputFile << "." << endl;
}

}
}
