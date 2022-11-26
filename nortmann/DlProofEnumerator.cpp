#include "DlProofEnumerator.h"

#include "../helper/FctHelper.h"
#include "../helper/Resources.h"
#include "../tree/TreeNode.h"
#include "../metamath/DRuleParser.h"
#include "DlCore.h"
#include "DlFormula.h"

#include <boost/filesystem/operations.hpp>

#define TBB_PREVIEW_CONCURRENT_ORDERED_CONTAINERS 1 // TODO Temporary, for low tbb version ("libtbb-dev is already the newest version (2020.1-2)" on Linux Mint 20.3)
#include <tbb/concurrent_map.h>
#include <tbb/concurrent_set.h>
#include <tbb/concurrent_vector.h>
#include <tbb/parallel_for.h>

#include <iostream>

using namespace std;
using namespace xamid::helper;
using namespace xamid::metamath;

namespace xamid {
namespace nortmann {

size_t dlNumFormulaHash::operator()(const shared_ptr<DlFormula>& f) const {
	hash<string> stringHash;
	// NOTE: While a representation such as dlFormulaHash::representativeString() is faster to compute (since there are no translations on individual values),
	//       it is slower to use as a key since it results in longer sequences.
	return stringHash.operator()(DlCore::toPolishNotation_noRename(f));
}

const vector<const vector<string>*>& DlProofEnumerator::builtinRepresentatives() {
	static const vector<const vector<string>*> _builtinRepresentatives = { &Resources::dProofRepresentatives1, &Resources::dProofRepresentatives3, &Resources::dProofRepresentatives5, &Resources::dProofRepresentatives7, &Resources::dProofRepresentatives9, &Resources::dProofRepresentatives11, &Resources::dProofRepresentatives13, &Resources::dProofRepresentatives15 };
	return _builtinRepresentatives;
}

vector<vector<string>> DlProofEnumerator::composeRepresentativesToLookupVector(const vector<const vector<string>*>& allRepresentatives) {
	vector<vector<string>> allRepresentatives_refined(2 * allRepresentatives.size());
	vector<const vector<string>*>::const_iterator it = allRepresentatives.begin();
	uint32_t limit = 2 * allRepresentatives.size() - 1;
	for (uint32_t wordLengthLimit = 1; wordLengthLimit <= limit; wordLengthLimit += 2)
		allRepresentatives_refined[wordLengthLimit] = **it++;
	return allRepresentatives_refined;
}

bool DlProofEnumerator::readRepresentativesLookupVectorFromFiles_seq(vector<vector<string>>& allRepresentativesLookup, bool debug, const string& filePrefix, const string& filePostfix, bool initFresh) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (initFresh) {
		if (debug)
			startTime = chrono::steady_clock::now();
		allRepresentativesLookup = composeRepresentativesToLookupVector(builtinRepresentatives());
		if (debug)
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to load built-in representatives." << endl;
	}
	for (uint32_t wordLengthLimit = allRepresentativesLookup.size() + 1; true; wordLengthLimit += 2) { // look for files containing D-proofs, starting from built-in limit + 2
		string file = filePrefix + to_string(wordLengthLimit) + filePostfix;
		if (boost::filesystem::exists(file)) { // load
			allRepresentativesLookup.push_back( { });
			allRepresentativesLookup.push_back( { });
			vector<string>& contents = allRepresentativesLookup.back();
			if (debug)
				startTime = chrono::steady_clock::now();
			ifstream fin(file, fstream::in | fstream::binary);
			if (!fin.is_open()) {
				if (debug)
					cerr << "Failed to read the data file \"" << file << "\". Aborting." << endl;
				return false;
			}
			string line;
			while (getline(fin, line)) {
				string::size_type i = line.find(':'); // support both variants "<D-proof>:<formula>" and "<D-proof>"
				if (i == string::npos)
					contents.push_back(line);
				else
					contents.push_back(line.substr(0, i));
			}
			if (debug)
				cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to read " << contents.size() << " condensed detachment proofs from " << file << "." << endl;
		} else
			break; // remains to generate
	}
	return true;
}

bool DlProofEnumerator::readRepresentativesLookupVectorFromFiles_par(vector<vector<string>>& allRepresentativesLookup, bool debug, unsigned concurrencyCount, const string& filePrefix, const string& filePostfix, bool initFresh) {
	if (concurrencyCount < 2)
		return readRepresentativesLookupVectorFromFiles_seq(allRepresentativesLookup, debug, filePrefix, filePostfix, initFresh); // system cannot execute threads concurrently
	chrono::time_point<chrono::steady_clock> startTime;
	if (initFresh) {
		if (debug)
			startTime = chrono::steady_clock::now();
		allRepresentativesLookup = composeRepresentativesToLookupVector(builtinRepresentatives());
		if (debug)
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to load built-in representatives." << endl;
	}
	vector<unsigned> threadComplete(concurrencyCount);
	vector<unsigned> threadAbort(concurrencyCount);
	vector<string> threadResults(concurrencyCount);
	vector<thread> threads;
	unsigned t = 0;
	for (uint32_t wordLengthLimit = allRepresentativesLookup.size() + 1; true; wordLengthLimit += 2) { // look for files containing D-proofs, starting from built-in limit + 2
		const string file = filePrefix + to_string(wordLengthLimit) + filePostfix;
		if (boost::filesystem::exists(file)) { // load
			allRepresentativesLookup.push_back( { });
			allRepresentativesLookup.push_back( { });
			vector<string>& contents = allRepresentativesLookup.back();
			auto load = [&](unsigned t, const string& file) {
				if (debug)
					startTime = chrono::steady_clock::now();
				ifstream fin(file, fstream::in | fstream::binary);
				if (!fin.is_open()) {
					if (debug) {
						stringstream ss;
						ss << "Failed to read the data file \"" << file << "\". Aborting.";
						threadResults[t] = ss.str();
					}
					threadAbort[t] = 1;
					return;
				}
				string line;
				while (getline(fin, line)) {
					string::size_type i = line.find(':'); // support both variants "<D-proof>:<formula>" and "<D-proof>"
					if (i == string::npos)
						contents.push_back(line);
					else
						contents.push_back(line.substr(0, i));
				}
				if (debug) {
					stringstream ss;
					ss << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to read " << contents.size() << " condensed detachment proofs from " << file << ". [tid:" << this_thread::get_id() << "]";
					threadResults[t] = ss.str();
				}
				threadComplete[t] = 1;
			};
			if (t < concurrencyCount)
				threads.emplace_back(load, t++, file);
			else {
				bool startedNext = false;
				while (!startedNext) {
					for (unsigned t = 0; t < concurrencyCount; t++) {
						if (threadComplete[t]) {
							threadComplete[t] = 0;
							threads[t].join();
							if (threadAbort[t]) {
								if (debug)
									cerr << threadResults[t] << endl;
								return false;
							} else if (debug)
								cout << threadResults[t] << endl;
							threads[t] = thread(load, t, file);
							startedNext = true;
							break;
						}
					}
					this_thread::yield(); // avoid deadlock ; put current thread at the back of the queue of threads that are ready to execute => allow other threads to run before this thread is scheduled again
				}
			}
		} else
			break; // remains to generate
	}
	for (unsigned t = 0; t < threads.size(); t++) {
		threads[t].join();
		if (threadAbort[t]) {
			if (debug)
				cerr << threadResults[t] << endl;
			return false;
		} else if (debug)
			cout << threadResults[t] << endl;
	}
	return true;
}

vector<pair<array<uint32_t, 2>, unsigned>> DlProofEnumerator::proofLengthCombinations(unsigned knownLimit) {
	vector<array<uint32_t, 2>> combinations;
	for (unsigned i = 1; i <= knownLimit; i += 2) {
		for (unsigned j = 1; j <= knownLimit; j += 2) {
			if (i <= j && i + j > knownLimit) {
				combinations.push_back( { i, j });
				if (i != j)
					combinations.push_back( { j, i });
			}
		}
	}
	unsigned a = knownLimit + 2;
	for (unsigned i = 1; i <= knownLimit; i += 2) {
		combinations.push_back( { i, a });
		combinations.push_back( { a, i });
	}
	vector<pair<array<uint32_t, 2>, unsigned>> combinationsRefined;
	for (unsigned i = knownLimit + 2; i <= 1 + knownLimit + a; i += 2)
		for (const array<uint32_t, 2>& arr : combinations)
			if (1 + arr[0] + arr[1] == i)
				combinationsRefined.push_back(make_pair(arr, 1 + arr[0] + arr[1]));
	combinationsRefined.push_back(make_pair(array<uint32_t, 2> { a, a }, 1 + 2 * a));
	return combinationsRefined;
}

bool DlProofEnumerator::loadDProofRepresentatives(vector<vector<string>>& allRepresentatives, uint64_t* optOut_allRepresentativesCount, uint32_t* optOut_firstMissingIndex, bool debug, const string& filePrefix, const string& filePostfix, bool initFresh) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	vector<vector<string>>::size_type startSize = initFresh ? 0 : allRepresentatives.size();
	if (!readRepresentativesLookupVectorFromFiles_par(allRepresentatives, debug, thread::hardware_concurrency(), filePrefix, filePostfix, initFresh))
		return false;
	unsigned more = 1;
	if (debug) {
		if (initFresh) {
			unsigned total = allRepresentatives.size() / 2;
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " total read duration." << endl;
			cout << "Loaded " << total << " representative collection" << (total == 1 ? "" : "s") << " of size" << (total == 1 ? "" : "s") << ":" << endl;
		} else {
			more = (allRepresentatives.size() - startSize) / 2;
			if (more) {
				cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " additional read duration." << endl;
				cout << "Loaded " << more << " more representative collection" << (more == 1 ? "" : "s") << " of size" << (more == 1 ? "" : "s") << ":" << endl;
			}
		}
	}
	uint64_t allRepresentativesCount = 0;
	for (uint32_t wordLengthLimit = 1; wordLengthLimit < allRepresentatives.size(); wordLengthLimit += 2) {
		size_t size = allRepresentatives[wordLengthLimit].size();
		allRepresentativesCount += size;
		if (debug && wordLengthLimit > startSize)
			cout << wordLengthLimit << " : " << size << endl;
	}
	if (debug && more)
		cout << allRepresentativesCount << " representatives in total." << endl;
	if (optOut_allRepresentativesCount)
		*optOut_allRepresentativesCount = allRepresentativesCount;
	if (optOut_firstMissingIndex)
		*optOut_firstMissingIndex = allRepresentatives.size() + 1;
	return true;
}

tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual> DlProofEnumerator::parseDProofRepresentatives(const vector<vector<string>>& allRepresentatives, ProgressData* const progressData, FormulaMemoryReductionData* const memReductionData) {
	tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual> representativeProofs;
	if (progressData)
		progressData->setStartTime();
	for (uint32_t wordLengthLimit = 1; wordLengthLimit < allRepresentatives.size(); wordLengthLimit += 2) { // FASTEST: Parse each string individually and without translation to DlProof objects.
		const vector<string>& representativesOfWordLengthLimit = allRepresentatives[wordLengthLimit];
		tbb::parallel_for(tbb::blocked_range<vector<string>::const_iterator>(representativesOfWordLengthLimit.begin(), representativesOfWordLengthLimit.end()), [&progressData, &representativeProofs, &memReductionData](tbb::blocked_range<vector<string>::const_iterator>& range) {
			for (vector<string>::const_iterator it = range.begin(); it != range.end(); ++it) {
				const string& s = *it;
				vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<unsigned, vector<unsigned>>>>> rawParseData = DRuleParser::parseDProof_raw(s);
				shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
				if (memReductionData) {
					DlCore::calculateEmptyMeanings(conclusion); // NOTE: May register new variables, which is thread-safe via DlCore::tryRegisterVariable().
					replaceNodes(conclusion, memReductionData->nodeStorage, memReductionData->nodeReplacementCounter);
					replaceValues(conclusion, memReductionData->valueStorage, memReductionData->valueReplacementCounter, memReductionData->alreadyProcessing);
					DlCore::clearMeanings(conclusion);
				}
				// NOTE: Definitely stores 'conclusion', since that is how the input files were constructed.
				representativeProofs.emplace(conclusion, s);

				// Show progress if requested
				if (progressData) {
					if (progressData->nextStep()) {
						uint64_t percentage;
						string progress;
						string etc;
						if (progressData->nextState(percentage, progress, etc)) {
							time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
							cout << strtok(ctime(&time), "\n") << ": Parsed " << (percentage < 10 ? " " : "") << percentage << "% of D-proofs. [" << progress << "] (" << etc << ")" << endl;
						}
					}
				}
			}
		}); // NOTE: Requires __has_include(<tbb/tbb.h>) to use parallel execution.
	}
	return representativeProofs;
}

void DlProofEnumerator::generateDProofRepresentativeFiles(uint32_t limit, bool redundantSchemasRemoval, bool memReduction) { // NOTE: More debug code & performance results available before https://github.com/deontic-logic/proof-tool/commit/45627054d14b6a1e08eb56eaafcf7cf202f2ab96
	chrono::time_point<chrono::steady_clock> startTime;

	// 1. Load representative D-proof strings.
	time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
	cout << strtok(ctime(&time), "\n") << ": " << (limit == UINT32_MAX ? "Unl" : "L") << "imited D-proof representative generator started. [parallel ; " << thread::hardware_concurrency() << " hardware thread contexts" << (limit == UINT32_MAX ? "" : ", limit: " + to_string(limit)) << (redundantSchemasRemoval ? "" : ", unfiltered") << (memReduction ? "" : ", no memory reduction") << "]" << endl;
	string filePrefix = "data/dProofs";
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	uint64_t allRepresentativesCount;
	uint32_t start;
	if (!loadDProofRepresentatives(allRepresentatives, &allRepresentativesCount, &start, true, filePrefix, filePostfix))
		return;
	// e.g., for up to 'data/dProofs27.txt' present:
	//   0.07 ms taken to load built-in representatives.
	//   0.47 ms taken to read 5221 condensed detachment proofs from data/dProofs17.txt. [tid:4]
	//   1.51 ms taken to read 15275 condensed detachment proofs from data/dProofs19.txt. [tid:5]
	//   4.14 ms taken to read 44206 condensed detachment proofs from data/dProofs21.txt. [tid:6]
	//  20.14 ms taken to read 129885 condensed detachment proofs from data/dProofs23.txt. [tid:7]
	//  66.17 ms taken to read 385789 condensed detachment proofs from data/dProofs25.txt. [tid:8]
	// 201.04 ms taken to read 1149058 condensed detachment proofs from data/dProofs27.txt. [tid:9]
	// 204.85 ms total read duration.
	// Loaded 14 representative collections of sizes:
	//  1 :       3
	//  3 :       6
	//  5 :      12
	//  7 :      38
	//  9 :      89
	// 11 :     229
	// 13 :     672
	// 15 :    1844
	// 17 :    5221
	// 19 :   15275
	// 21 :   44206
	// 23 :  129885
	// 25 :  385789
	// 27 : 1149058
	// 1732327 representatives in total.
	if (!redundantSchemasRemoval) {
		filePostfix = "-unfiltered" + to_string(start) + "+.txt";
		if (!loadDProofRepresentatives(allRepresentatives, &allRepresentativesCount, &start, true, filePrefix, filePostfix, false))
			return;
	}
	if (start > limit) {
		time = chrono::system_clock::to_time_t(chrono::system_clock::now());
		cout << strtok(ctime(&time), "\n") << ": Limited D-proof representative generator skipped. [parallel ; " << thread::hardware_concurrency() << " hardware thread contexts" << (limit == UINT32_MAX ? "" : ", limit: " + to_string(limit)) << (redundantSchemasRemoval ? "" : ", unfiltered") << (memReduction ? "" : ", no memory reduction") << "]" << endl;
		return;
	}

	// 2. Initialize and prepare progress data.
	bool showProgress = allRepresentatives.size() > 15;
	ProgressData parseProgress = showProgress ? ProgressData(allRepresentatives.size() > 27 ? 5 : allRepresentatives.size() > 25 ? 10 : 20, allRepresentativesCount) : ProgressData();
	ProgressData findProgress;
	ProgressData removalProgress;

	// 3. Prepare representative proofs that are already known addressable by conclusions, for filtering. To find the conclusions, parse all loaded D-proofs.
	startTime = chrono::steady_clock::now();
	FormulaMemoryReductionData memReductionData;
	tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual> representativeProofs;
	if (memReduction) {
		representativeProofs = parseDProofRepresentatives(allRepresentatives, showProgress ? &parseProgress : nullptr, &memReductionData);
		cout << "nodeReplacements: " << memReductionData.nodeReplacementCounter << ", valueReplacements: " << memReductionData.valueReplacementCounter << endl;
	} else
		representativeProofs = parseDProofRepresentatives(allRepresentatives, showProgress ? &parseProgress : nullptr);
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " total parse & insertion duration." << endl;
	// e.g. 15:    160.42 ms                        total parse & insertion duration.
	//      17:    516.98 ms                        total parse & insertion duration.
	//      19:   1729.93 ms (       1 s 729.93 ms) total parse & insertion duration.
	//      21:   5941.66 ms (       5 s 941.66 ms) total parse & insertion duration.
	//      23:  20350.66 ms (      20 s 350.66 ms) total parse & insertion duration.
	//      25:  70434.18 ms (1 min 10 s 434.18 ms) total parse & insertion duration.
	//      27: 244267.10 ms (4 min  4 s 267.10 ms) total parse & insertion duration.

	// 4. Compute and store new representatives indefinitely.
	for (uint32_t wordLengthLimit = start; wordLengthLimit <= limit; wordLengthLimit += 2) {

		// 4.1 Prepare progress data.
		showProgress = wordLengthLimit >= 17;
		// NOTE: The following maps are built dynamically and may contain gaps, in which case earlier
		//       values are used to approximate the exponential growth rate, based on which new values
		//       are approximated in order to estimate ongoing progress of unknown scale.
		static map<uint32_t, uint64_t> iterationCounts_builtin = { { 1, 3 }, { 3, 9 }, { 5, 36 }, { 7, 108 }, { 9, 372 }, { 11, 1134 }, { 13, 3354 }, { 15, 10360 }, { 17, 31388 } };
		static map<uint32_t, uint64_t> iterationCounts = { { 1, 3 }, { 3, 9 }, { 5, 36 }, { 7, 108 }, { 9, 372 }, { 11, 1134 }, { 13, 3354 }, { 15, 10360 }, { 17, 31388 }, { 19, 94907 }, { 21, 290392 }, { 23, 886041 }, { 25, 2709186 }, { 27, 8320672 }, { 29, 25589216 }, };
		static map<uint32_t, uint64_t> removalCounts = { { 1, 0 }, { 3, 0 }, { 5, 3 }, { 7, 6 }, { 9, 24 }, { 11, 59 }, { 13, 171 }, { 15, 504 }, { 17, 1428 }, { 19, 4141 }, { 21, 12115 }, { 23, 35338 }, { 25, 104815 }, { 27, 310497 }, { 29, 926015 }, };
		if (showProgress) {
			auto determineCountingLimit = [&wordLengthLimit](uint64_t& count, const map<uint32_t, uint64_t>& counts) -> bool {
				map<uint32_t, uint64_t>::const_iterator itIterationCount = counts.find(wordLengthLimit);
				if (itIterationCount == counts.end()) {
					map<uint32_t, uint64_t>::const_iterator itLastKnown = prev(counts.end());
					while (itLastKnown->first > wordLengthLimit)
						itLastKnown = prev(itLastKnown); // bridge potential gaps to reach the relevant entries
					map<uint32_t, uint64_t>::const_iterator itPrevLastKnown = prev(itLastKnown);
					uint32_t lastKnownLimit = itLastKnown->first;
					uint32_t lastKnownCount = itLastKnown->second;
					while (itLastKnown->first != itPrevLastKnown->first + 2) { // to not require the initial amount stored, approximate from earlier pairs if necessary
						itLastKnown = prev(itLastKnown);
						itPrevLastKnown = prev(itPrevLastKnown);
					}
					double lastKnownGrowth = (double) itLastKnown->second / itPrevLastKnown->second;
					double estimatedLimit = lastKnownCount;
					for (uint32_t i = lastKnownLimit; i < wordLengthLimit; i += 2)
						estimatedLimit *= lastKnownGrowth;
					count = estimatedLimit;
					return true;
				} else {
					count = itIterationCount->second;
					return false;
				}
			};
			uint64_t iterationCount;
			bool iterationCountEstimated = determineCountingLimit(iterationCount, redundantSchemasRemoval ? iterationCounts : iterationCounts_builtin);
			findProgress = ProgressData(wordLengthLimit >= 27 ? 2 : wordLengthLimit >= 25 ? 5 : wordLengthLimit >= 23 ? 10 : 20, iterationCount, iterationCountEstimated);
			uint64_t removalCount;
			bool removalCountEstimated = determineCountingLimit(removalCount, removalCounts);
			removalProgress = ProgressData(wordLengthLimit >= 23 ? 2 : wordLengthLimit >= 21 ? 5 : wordLengthLimit >= 19 ? 10 : 20, removalCount, removalCountEstimated);
		}

		time = chrono::system_clock::to_time_t(chrono::system_clock::now());
		cout << strtok(ctime(&time), "\n") << ": Starting to generate D-proof representatives of length " << wordLengthLimit << "." << endl;

		// 4.2 Iterate proofs of length 'wordLengthLimit' and generate their conclusions.
		uint64_t counter;
		uint64_t representativeCounter;
		uint64_t redundantCounter;
		uint64_t invalidCounter;
		const vector<uint32_t> stack = { wordLengthLimit }; // do not generate all words up to a certain length, but only of length 'wordLengthLimit' ; NOTE: Uses nonterminal 'A' as lower limit 'wordLengthLimit' in combination with upper limit 'wordLengthLimit'.
		const unsigned knownLimit = wordLengthLimit - 2;
		startTime = chrono::steady_clock::now();
		if (memReduction) {
			_findProvenFormulas(representativeProofs, wordLengthLimit, DlProofEnumeratorMode::Generic, showProgress ? &findProgress : nullptr, &counter, &representativeCounter, &redundantCounter, &invalidCounter, &memReductionData, &stack, &knownLimit, &allRepresentatives);
			cout << "nodeReplacements: " << memReductionData.nodeReplacementCounter << ", valueReplacements: " << memReductionData.valueReplacementCounter << endl;
			// e.g. 25:   831 MB memory commit size ; nodeReplacements:   806328, valueReplacements:  345001 ; at "[...] total parse & insertion duration."
			//           2892 MB memory commit size ; nodeReplacements:  3796756, valueReplacements: 1103491 ; at "[...] taken to collect 490604 D-proofs of length 25. [iterated 2709186 condensed detachment proof strings]"
			//      27:  2601 MB memory commit size ; nodeReplacements:  2373851, valueReplacements: 1011151 ; at "[...] total parse & insertion duration."
			//           9748 MB memory commit size ; nodeReplacements: 11348932, valueReplacements: 3265546 ; at "[...] taken to collect 1459555 D-proofs of length 27. [iterated 8320672 condensed detachment proof strings]"
			//      29:  8663 MB memory commit size ; nodeReplacements:  7036815, valueReplacements: 2986586 ; at "[...] total parse & insertion duration."
			//          32190 MB memory commit size ; nodeReplacements: 34154357, valueReplacements: 9736481 ; at "[...] taken to collect 4375266 D-proofs of length 29. [iterated 25589216 condensed detachment proof strings]"
			// NOTE: When [Windows 7] Task Manager shows e.g. "811.644 K", it means roughly 811644 * 1024 bytes = 831123456 B ≈ 831 MB. (It uses prefixes according to JEDEC memory standards, in contrast to SI prefixes.)
			//       Due to 32190 MB ≈ 29.98 GiB, results for word length limit 29 can still be computed without page faults on a 32 GiB RAM machine.
		} else {
			_findProvenFormulas(representativeProofs, wordLengthLimit, DlProofEnumeratorMode::Generic, showProgress ? &findProgress : nullptr, &counter, &representativeCounter, &redundantCounter, &invalidCounter, nullptr, &stack, &knownLimit, &allRepresentatives);
			// e.g. 25:  1578 MB memory commit size ;  1578 / 831   ≈ 1.89892                                ; at "[...] total parse & insertion duration."
			//           5974 MB memory commit size ;  5974 / 2892  ≈ 2.06570                                ; at "[...] taken to collect 490604 D-proofs of length 25. [iterated 2709186 condensed detachment proof strings]"
			//      27:  5254 MB memory commit size ;  5254 / 2601  ≈ 2.01999                                ; at "[...] total parse & insertion duration."
			//          19937 MB memory commit size ; 19937 / 9748  ≈ 2.04524                                ; at "[...] taken to collect 1459555 D-proofs of length 27. [iterated 8320672 condensed detachment proof strings]"
			//      29: 17627 MB memory commit size ; 17627 / 8663  ≈ 2.03475                                ; at "[...] total parse & insertion duration."
			//          67375 MB memory commit size ; 67375 / 32190 ≈ 2.09304                                ; at "[...] taken to collect 4375266 D-proofs of length 29. [iterated 25589216 condensed detachment proof strings]"
		}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to collect " << representativeCounter << " D-proofs of length " << wordLengthLimit << ". [iterated " << counter << " condensed detachment proof strings]" << endl;
		// e.g. 17:    1631.72 ms (        1 s 631.72 ms) taken to collect    6649 [...]
		//      19:    5883.22 ms (        5 s 883.22 ms) taken to collect   19416 [...]
		//      21:   21007.67 ms (       21 s   7.67 ms) taken to collect   56321 [...]
		//      23:   75916.37 ms ( 1 min 15 s 916.37 ms) taken to collect  165223 [...]
		//      25:  268873.93 ms ( 4 min 28 s 873.93 ms) taken to collect  490604 [...]
		//      27:  957299.91 ms (15 min 57 s 299.91 ms) taken to collect 1459555 [...]
		//      29: 3378071.50 ms (56 min 18 s  71.50 ms) taken to collect 4375266 [...]

		// 4.3 Update iteration progress information.
		(redundantSchemasRemoval ? iterationCounts : iterationCounts_builtin).emplace(wordLengthLimit, counter);
		//#cout << "Updated iterationCounts: " << FctHelper::mapString((redundantSchemasRemoval ? iterationCounts : iterationCounts_builtin)) << endl;

		// 4.4 Remove new proofs with redundant conclusions.
		// NOTE: For a few steps more to not take ages (but still get all minimal D-proofs up to a certain length), one can skip the time-intensive filtering below and then
		//       load 'dProofs17.txt', ..., 'dProofs<n>.txt', 'dProofs<n+1>-unfiltered<n+1>+.txt', ..., 'dProofs<n+m>-unfiltered<n+1>+.txt', for <n+1> being the first 'wordLengthLimit'
		//       used to generate files without redundant conclusions removal.
		//       Due to the higher growth rate of sets with unfiltered schema redundancies, the difference in size can get significant, e.g.
		//       'dProofs25.txt'               and 'dProofs27.txt'               are 10.030.513 and 32.173.623 bytes in size (i.e. 385789 and 1149058 D-proofs), respectively, whereas  [1149058 / 385789 ≈ 2.97846]
		//       'dProofs25-unfiltered17+.txt' and 'dProofs27-unfiltered17+.txt' are 19.969.715 and 70.423.275 bytes in size (i.e. 768066 and 2515117 D-proofs), respectively.          [2515117 / 768066 ≈ 3.27461 ; 768066 / 385789 ≈ 1.99090 ; 2515117 / 1149058 ≈ 2.18885]
		//       Where one enters the unfiltered strategy makes quite a difference, e.g.
		//       'dProofs25-unfiltered25+.txt' and 'dProofs27-unfiltered25+.txt' are 12.755.703 and 47.068.055 bytes is size (i.e. 490604 and 1681002 D-proofs), respectively, and      [1681002 / 490604 ≈ 3.42639 ; 490604 / 385789 ≈ 1.27169 ; 1681002 / 1149058 ≈ 1.46294]
		//       generating 'dProofs17.txt', ..., 'dProofs23.txt' doesn't take long. But while generating 'dProofs25.txt' and 'dProofs27.txt' take several hours and over a day on an average PC,
		//       respectively, generating 'dProofs25-unfiltered25+.txt' and 'dProofs27-unfiltered25+.txt' only take around 5 and 20 minutes, respectively. But the latter also take more RAM, so
		//       a good choice really boils down to what the space and time constraints are. For example, on a machine with only 32 GiB of RAM, the only way to use all proof representatives up
		//       to length 29 without page faults (apart from transferring the file) is to generate 'dProofs29.txt', which takes several weeks.
		if (redundantSchemasRemoval) {
			startTime = chrono::steady_clock::now();
			uint64_t oldRepresentativeCounter = representativeCounter;
			// TODO: Performance should be improved significantly if possible. Can we define a schema tree database structure to reduce the amount of schema checks?
			_removeRedundantConclusionsForProofsOfMaxLength(wordLengthLimit, representativeProofs, showProgress ? &removalProgress : nullptr, representativeCounter, redundantCounter);
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to detect " << oldRepresentativeCounter - representativeCounter << " conclusions for which there are more general variants proven in lower or equal amounts of steps." << endl;
			// e.g. 17:      1440.11 ms (                 1 s 440.11 ms) taken to detect   1428 conclusions [...]
			//      19:     15274.82 ms (                15 s 274.82 ms) taken to detect   4141 conclusions [...]
			//      21:    165695.51 ms (          2 min 45 s 695.51 ms) taken to detect  12115 conclusions [...]
			//      23:   1572083.47 ms (         26 min 12 s  83.47 ms) taken to detect  35338 conclusions [...]
			//      25:  15072757.24 ms (     4 h 11 min 12 s 757.24 ms) taken to detect 104815 conclusions [...]
			//      27: 144893608.98 ms (1 d 16 h 14 min 53 s 608.98 ms) taken to detect 310497 conclusions [...]
			// NOTE: It is essential for performance to have a sufficient amount of RAM in order to avoid page faults.
			//       For example, a less optimized variant of the algorithm with an expected duration of around a week
			//       for word length limit 27 resulted in a commit size of 19586820 KiB, i.e. ≈18.68 GiB for the process
			//       on a machine with only 16 GiB of RAM. The task ran from 10th August, and at 10th September still had
			//       not completed this phase. The CPU utilized was an Intel Core i7-3610QM (4 cores, 8 threads). The mostly
			//       around 3000 to 5000 page faults per second resulted in constantly reading from a Samsung SSD 870 EVO 1TB
			//       hard drive (in full full performance mode) at around 120 to 200 MB/s.
			//       For comparison, the current algorithm requires a memory commit size of only ≈9.08 GiB and completed this phase on
			//       the same machine in only 1 d 22 h 40 min 16 s 422.05 ms. The durations above were recorded from a machine with an
			//       Intel Core i7-3770 (also 4 cores, 8 threads) of similar but slightly better performance. [details: https://www.cpubenchmark.net/compare/Intel-i7-3770-vs-Intel-i7-3610QM/896vs891]
			//       Both machines used 1600 MHz DDR3 RAM, the slower 16 GiB CL11, the faster 32 GiB CL9. [16 GiB ≈ 17.18 GB, 32 GiB  ≈ 34.36 GB]
			//       For illustration, a 1600 MHz CL9 RAM (thus 800 MHz signal frequency), by 800 MHz = 0.8 / ns = 1 / (1.25 ns), has a latency to
			//       read of around 9 * 1.25 ns = 11.25 ns, but the designated hard drive has one above 1.3 ms, i.e. more than 116000 times as much.
			//       Given that every single formula could potentially lead to several page faults, these latencies may add up sequentially.
			//       Memory requirements depending on 'memReduction' are illustrated below the _findProvenFormulas() call.
			//       All measurements of given durations took place in 'memReduction' mode without page faults, compiled without
			//       CPU-specific compiler flags (i.e. compiled by GCC 11.2.0 with default flags "-march=x86-64 -mtune=generic").
			//       Notably, using "-march=native" (which implies "-mtune=native") did not result in any apparent performance improvement
			//       for these Ivy Bridge processors under Windows 7, but building and running on Linux Mint 20.3 – compiled by GCC 10.3.0
			//       with the same general-purpose default flags – resulted in around 11% reduced runtimes.

			// 4.5 Update removal progress information.
			removalCounts.emplace(wordLengthLimit, oldRepresentativeCounter - representativeCounter);
			//#cout << "Updated removalCounts: " << FctHelper::mapString(removalCounts) << endl;
		}

		// 4.6 Order and output information.
		startTime = chrono::steady_clock::now();
		map<unsigned, unsigned> amountPerLength;
		set<string, cmpStringGrow> newRepresentativeSequences;
		for (const pair<const shared_ptr<DlFormula>, string>& p : representativeProofs) {
			size_t len = p.second.length();
			if (len == wordLengthLimit)
				newRepresentativeSequences.insert(p.second);
			amountPerLength[len]++;
		}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to filter and order new representative proofs." << endl;
		cout << "Found " << representativeCounter << " representative, " << redundantCounter << " redundant, and " << invalidCounter << " invalid condensed detachment proof strings." << endl;
		cout << "lengths up to " << wordLengthLimit << " ; amounts per length: " << FctHelper::mapString(amountPerLength) << " ; " << newRepresentativeSequences.size() << " new representative proofs (" << redundantCounter << " redundant, " << invalidCounter << " invalid)" << endl;
		// e.g. 17:    5221 new representative proofs (  14809 redundant,   11358 invalid)
		//      19:   15275 new representative proofs (  44743 redundant,   34889 invalid)
		//      21:   44206 new representative proofs ( 134493 redundant,  111693 invalid)
		//      23:  129885 new representative proofs ( 409159 redundant,  346997 invalid)
		//      25:  385789 new representative proofs (1243007 redundant, 1080390 invalid)
		//      27: 1149058 new representative proofs (3778453 redundant, 3393161 invalid)

		// 4.7 Store information for current run.
		allRepresentatives.push_back( { });
		allRepresentatives.push_back(vector<string>(newRepresentativeSequences.begin(), newRepresentativeSequences.end()));

		// 4.8 Store information permanently.
		startTime = chrono::steady_clock::now();
		string file = filePrefix + to_string(wordLengthLimit) + filePostfix;
		string content = FctHelper::vectorString(allRepresentatives.back(), { }, { }, "\n");
		FctHelper::writeToFile(file, content);
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << content.length() << " bytes of representative condensed detachment proof strings to " << file << "." << endl;
	}
	time = chrono::system_clock::to_time_t(chrono::system_clock::now());
	cout << strtok(ctime(&time), "\n") << ": Limited D-proof representative generator complete. [parallel ; " << thread::hardware_concurrency() << " hardware thread contexts" << (limit == UINT32_MAX ? "" : ", limit: " + to_string(limit)) << (redundantSchemasRemoval ? "" : ", unfiltered") << (memReduction ? "" : ", no memory reduction") << "]" << endl;
}

// NOTE: Requires 'formula' with meanings.
void DlProofEnumerator::replaceNodes(shared_ptr<DlFormula>& formula, tbb::concurrent_unordered_map<vector<uint32_t>, shared_ptr<DlFormula>, myhash<vector<uint32_t>>>& nodeStorage, atomic<uint64_t>& nodeReplacementCounter) {
	pair<tbb::concurrent_unordered_map<vector<uint32_t>, shared_ptr<DlFormula>, myhash<vector<uint32_t>>>::iterator, bool> emplaceResult = nodeStorage.emplace(formula->meaning(), formula);
	if (!emplaceResult.second) {
		if (formula != emplaceResult.first->second) {
			formula = emplaceResult.first->second;
			nodeReplacementCounter++;
		}
	} else // formula was used to initialize a fresh key => formula wasn't already registered => try register children
		for (uint32_t i = 0; i < formula->getChildren().size(); i++)
			replaceNodes(formula->children()[i], nodeStorage, nodeReplacementCounter);
}

void DlProofEnumerator::replaceValues(shared_ptr<DlFormula>& formula, tbb::concurrent_unordered_map<string, shared_ptr<String>>& valueStorage, atomic<uint64_t>& valueReplacementCounter, tbb::concurrent_unordered_set<DlFormula*>& alreadyProcessing) {
	if (!alreadyProcessing.emplace(formula.get()).second)
		return; // avoid duplicated handlings
	shared_ptr<String>& val = formula->value();
	pair<tbb::concurrent_unordered_map<string, shared_ptr<String>>::iterator, bool> emplaceResult = valueStorage.emplace(val->value, val);
	if (!emplaceResult.second && val != emplaceResult.first->second) {
		val = emplaceResult.first->second;
		valueReplacementCounter++;
	}
	for (uint32_t i = 0; i < formula->getChildren().size(); i++)
		replaceValues(formula->children()[i], valueStorage, valueReplacementCounter, alreadyProcessing);
}

void DlProofEnumerator::_findProvenFormulas(tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>& representativeProofs, uint32_t wordLengthLimit, DlProofEnumeratorMode mode, ProgressData* const progressData, uint64_t* optOut_counter, uint64_t* optOut_conclusionCounter, uint64_t* optOut_redundantCounter, uint64_t* optOut_invalidCounter, FormulaMemoryReductionData* const memReductionData, const vector<uint32_t>* genIn_stack, const uint32_t* genIn_n, const vector<vector<string>>* genIn_allRepresentativesLookup) {
	atomic<uint64_t> counter { 0 };
	atomic<uint64_t> conclusionCounter { 0 };
	atomic<uint64_t> redundantCounter { 0 };
	atomic<uint64_t> invalidCounter { 0 };
	auto process = [&representativeProofs, &progressData, &counter, &conclusionCounter, &redundantCounter, &invalidCounter, &memReductionData](string& sequence) {
		counter++;
		vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<unsigned, vector<unsigned>>>>> rawParseData;
		if (!(rawParseData = DRuleParser::parseDProof_raw(sequence)).empty()) {
			shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
			if (memReductionData) {
				DlCore::calculateEmptyMeanings(conclusion); // NOTE: May register new variables, which is thread-safe via DlCore::tryRegisterVariable().
				replaceNodes(conclusion, memReductionData->nodeStorage, memReductionData->nodeReplacementCounter);
				replaceValues(conclusion, memReductionData->valueStorage, memReductionData->valueReplacementCounter, memReductionData->alreadyProcessing);
				DlCore::clearMeanings(conclusion);
			}
			pair<tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>::iterator, bool> emplaceResult = representativeProofs.emplace(conclusion, sequence);
			if (!emplaceResult.second) { // a proof for the conclusion is already known
				redundantCounter++;
				string& storedSequence = emplaceResult.first->second;
				if (storedSequence.length() > sequence.length())
					storedSequence = sequence; // use the shorter proof
				else if (storedSequence.length() == sequence.length() && storedSequence > sequence)
					storedSequence = sequence; // use the "preceding" proof
			} else
				conclusionCounter++;
		} else
			invalidCounter++;

		// Show progress if requested
		if (progressData) {
			if (progressData->nextStep()) {
				uint64_t percentage;
				string progress;
				string etc;
				if (progressData->nextState(percentage, progress, etc)) {
					time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
					cout << strtok(ctime(&time), "\n") << ": Iterated " << (progressData->maximumEstimated ? "≈" : "") << (percentage < 10 ? " " : "") << percentage << "% of D-proof candidates. [" << progress << "] (" << etc << ")" << endl;
				}
			}
		}
	};
	switch (mode) {
	case DlProofEnumeratorMode::Generic:
		if (!genIn_stack || !genIn_n || !genIn_allRepresentativesLookup)
			throw invalid_argument("Parameters missing for DlProofEnumeratorMode::Generic.");
		if (progressData)
			progressData->setStartTime();
		processCondensedDetachmentPlProofs_generic(*genIn_stack, wordLengthLimit, *genIn_n, *genIn_allRepresentativesLookup, process);
		break;
	case DlProofEnumeratorMode::Naive:
		if (progressData)
			progressData->setStartTime();
		processCondensedDetachmentPlProofs_naive(wordLengthLimit, process);
		break;
	}
	if (optOut_counter)
		*optOut_counter = counter;
	if (optOut_conclusionCounter)
		*optOut_conclusionCounter = conclusionCounter;
	if (optOut_redundantCounter)
		*optOut_redundantCounter = redundantCounter;
	if (optOut_invalidCounter)
		*optOut_invalidCounter = invalidCounter;
}

void DlProofEnumerator::_findProvenFormulasWithEquivalenceClasses(tbb::concurrent_unordered_map<shared_ptr<DlFormula>, tbb::concurrent_set<string, cmpStringGrow>, dlNumFormulaHash, dlFormulaEqual>& representativeProofsWithEquivalenceClasses, uint32_t wordLengthLimit, DlProofEnumeratorMode mode, ProgressData* const progressData, uint64_t* optOut_counter, uint64_t* optOut_conclusionCounter, uint64_t* optOut_redundantCounter, uint64_t* optOut_invalidCounter, FormulaMemoryReductionData* const memReductionData, const vector<uint32_t>* genIn_stack, const uint32_t* genIn_n, const vector<vector<string>>* genIn_allRepresentativesLookup) {
	atomic<uint64_t> counter { 0 };
	atomic<uint64_t> conclusionCounter { 0 };
	atomic<uint64_t> redundantCounter { 0 };
	atomic<uint64_t> invalidCounter { 0 };
	auto process = [&representativeProofsWithEquivalenceClasses, &progressData, &counter, &conclusionCounter, &redundantCounter, &invalidCounter, &memReductionData](string& sequence) {
		counter++;
		vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<unsigned, vector<unsigned>>>>> rawParseData;
		if (!(rawParseData = DRuleParser::parseDProof_raw(sequence)).empty()) {
			shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
			if (memReductionData) {
				DlCore::calculateEmptyMeanings(conclusion); // NOTE: May register new variables, which is thread-safe via DlCore::tryRegisterVariable().
				replaceNodes(conclusion, memReductionData->nodeStorage, memReductionData->nodeReplacementCounter);
				replaceValues(conclusion, memReductionData->valueStorage, memReductionData->valueReplacementCounter, memReductionData->alreadyProcessing);
				DlCore::clearMeanings(conclusion);
			}
			pair<tbb::concurrent_unordered_map<shared_ptr<DlFormula>, tbb::concurrent_set<string, cmpStringGrow>, dlNumFormulaHash, dlFormulaEqual>::iterator, bool> emplaceResult = representativeProofsWithEquivalenceClasses.emplace(conclusion, tbb::concurrent_set<string, cmpStringGrow> { });
			emplaceResult.first->second.insert(sequence);
			if (!emplaceResult.second) // a proof for the conclusion is already known
				redundantCounter++;
			else
				conclusionCounter++;
		} else
			invalidCounter++;

		// Show progress if requested
		if (progressData) {
			if (progressData->nextStep()) {
				uint64_t percentage;
				string progress;
				string etc;
				if (progressData->nextState(percentage, progress, etc)) {
					time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
					cout << strtok(ctime(&time), "\n") << ": Iterated " << (progressData->maximumEstimated ? "≈" : "") << (percentage < 10 ? " " : "") << percentage << "% of D-proof candidates. [" << progress << "] (" << etc << ")" << endl;
				}
			}
		}
	};
	switch (mode) {
	case DlProofEnumeratorMode::Generic:
		if (!genIn_stack || !genIn_n || !genIn_allRepresentativesLookup)
			throw invalid_argument("Parameters missing for DlProofEnumeratorMode::Generic.");
		if (progressData)
			progressData->setStartTime();
		processCondensedDetachmentPlProofs_generic(*genIn_stack, wordLengthLimit, *genIn_n, *genIn_allRepresentativesLookup, process);
		break;
	case DlProofEnumeratorMode::Naive:
		if (progressData)
			progressData->setStartTime();
		processCondensedDetachmentPlProofs_naive(wordLengthLimit, process);
		break;
	}
	if (optOut_counter)
		*optOut_counter = counter;
	if (optOut_conclusionCounter)
		*optOut_conclusionCounter = conclusionCounter;
	if (optOut_redundantCounter)
		*optOut_redundantCounter = redundantCounter;
	if (optOut_invalidCounter)
		*optOut_invalidCounter = invalidCounter;
}

void DlProofEnumerator::_removeRedundantConclusionsForProofsOfMaxLength(const uint32_t maxLength, tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>& representativeProofs, ProgressData* const progressData, uint64_t& conclusionCounter, uint64_t& redundantCounter) {
	//#chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	tbb::concurrent_map<unsigned, tbb::concurrent_vector<const shared_ptr<DlFormula>*>> formulasByStandardLength;
	tbb::parallel_for(representativeProofs.range(), [&formulasByStandardLength](tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>::range_type& range) {
		for (tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const shared_ptr<DlFormula>& formula = it->first;
			formulasByStandardLength[DlCore::standardFormulaLength(formula)].push_back(&formula);
		}
	});
	//#cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to create " << formulasByStandardLength.size() << " classes of formulas by their standard length." << endl;
	//#cout << [](tbb::concurrent_map<unsigned, tbb::concurrent_vector<const shared_ptr<DlFormula>*>>& m) { stringstream ss; for (const pair<const unsigned, tbb::concurrent_vector<const shared_ptr<DlFormula>*>>& p : m) { ss << p.first << ":" << p.second.size() << ", "; } return ss.str(); }(formulasByStandardLength) << endl;
	tbb::concurrent_unordered_map<const shared_ptr<DlFormula>*, tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>::const_iterator> toErase;
	if (progressData)
		progressData->setStartTime();
	tbb::parallel_for(representativeProofs.range(), [&maxLength, &progressData, &formulasByStandardLength, &toErase](tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>::range_type& range) {
		for (tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const uint32_t formula_sequenceLength = it->second.length();
			if (formula_sequenceLength == maxLength) {
				const shared_ptr<DlFormula>& formula = it->first;
				atomic<bool> redundant { false };
				unsigned formulaLen = DlCore::standardFormulaLength(formula);
				tbb::parallel_for(formulasByStandardLength.range(), [&formulaLen, &redundant, &formula](tbb::concurrent_map<unsigned, tbb::concurrent_vector<const shared_ptr<DlFormula>*>>::range_type& range) {
					for (tbb::concurrent_map<unsigned, tbb::concurrent_vector<const shared_ptr<DlFormula>*>>::const_iterator it = range.begin(); it != range.end(); ++it)
						if (redundant)
							return;
						else if (it->first <= formulaLen)
							for (const shared_ptr<DlFormula>* const potentialSchema : it->second)
								if (formula != *potentialSchema && DlCore::isSchemaOf(*potentialSchema, formula)) { // formula redundant
									redundant = true;
									return;
								}
				});
				if (redundant) {
					toErase.emplace(&it->first, it);

					// Show progress if requested
					if (progressData) {
						if (progressData->nextStep()) {
							uint64_t percentage;
							string progress;
							string etc;
							if (progressData->nextState(percentage, progress, etc)) {
								time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
								cout << strtok(ctime(&time), "\n") << ": Removed " << (progressData->maximumEstimated ? "≈" : "") << (percentage < 10 ? " " : "") << percentage << "% of redundant conclusions. [" << progress << "] (" << etc << ")" << endl;
							}
						}
					}
				}
			}
		}
	});
	conclusionCounter -= toErase.size();
	redundantCounter += toErase.size();
	//#cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken for data iteration." << endl;
	//#startTime = chrono::steady_clock::now();
	for (const pair<const shared_ptr<DlFormula>* const, tbb::concurrent_unordered_map<shared_ptr<DlFormula>, string, dlNumFormulaHash, dlFormulaEqual>::const_iterator>& p : toErase)
		representativeProofs.unsafe_erase(p.second);
	//#cout << FctHelper::round((chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken for erasure of " << toErase.size() << " elements." << endl;
}

namespace {
void recurse_loadCondensedDetachmentPlProofs_generic_par(string& prefix, vector<uint32_t>& stack, const uint32_t wordLengthLimit, const uint32_t knownLimit, const vector<vector<string>>& allRepresentatives, vector<deque<string>>& queues, vector<mutex>& mtxs, const vector<pair<array<uint32_t, 2>, unsigned>>& combinations) {
	constexpr uint32_t S = 0;
	const uint32_t A = knownLimit + 2;
	// NOTE: N1, N3, ..., N<knownLimit> are now simply 1, 3, ..., knownLimit.
	if (prefix.length() + stack.size() > wordLengthLimit)
		return;
	if (stack.empty()) {
		bool processed = false;
		unsigned bestIndex = 0;
		unsigned bestSize = UINT_MAX;
		for (unsigned t = 0; t < queues.size(); t++) {
			deque<string>& queue = queues[t];
			size_t size = queue.size();
			if (size) {
				if (size < bestSize) {
					bestIndex = t;
					bestSize = size;
				}
			} else {
				{
					lock_guard<mutex> lock(mtxs[t]);
					queue.push_back(prefix);
				}
				processed = true;
				break;
			}
		}
		if (!processed) {
			lock_guard<mutex> lock(mtxs[bestIndex]);
			queues[bestIndex].push_back(prefix);
		}
	} else {
		auto processN = [&](const vector<string>& representatives) {
			vector<uint32_t> stack_copy; // Since there are multiple options, we use copies for all
			string prefix_copy; //          but the last option, in order to restore the parameters.
			vector<string>::const_iterator last = prev(representatives.end());
			for (vector<string>::const_iterator it = representatives.begin(); it != last; ++it) {
				stack_copy = stack;
				prefix_copy = prefix;
				prefix_copy += *it;
				recurse_loadCondensedDetachmentPlProofs_generic_par(prefix_copy, stack_copy, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
			}
			prefix += *last;
			recurse_loadCondensedDetachmentPlProofs_generic_par(prefix, stack, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
		};
		uint32_t symbol = stack.back();
		if (symbol == S) {
			stack.pop_back(); // pop already for all cases
			// 1/2 : {1,...,allRepresentatives[knownLimit].back()}, S, [] ; stack: pop current symbol, push nothing
			vector<uint32_t> stack_copy; // Since there are multiple options, we use copies for all
			string prefix_copy; //          but the last option, in order to restore the parameters.
			auto processRepresentatives = [&](const vector<string>& representatives) {
				for (const string& sequence : representatives) {
					stack_copy = stack;
					prefix_copy = prefix;
					prefix_copy += sequence;
					recurse_loadCondensedDetachmentPlProofs_generic_par(prefix_copy, stack_copy, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
				}
			};
			processRepresentatives(allRepresentatives[1]);
			uint32_t remainingSpace = wordLengthLimit - (prefix.length() + stack.size()); // NOTE: Considers that stack already popped the current symbol.
			for (uint32_t s = 3; s <= knownLimit; s += 2)
				if (remainingSpace >= s)
					processRepresentatives(allRepresentatives[s]);

			// 2/2 : ε, S, [A] ; stack: pop current symbol, push [A] on top of stack
			stack.push_back(A);
			recurse_loadCondensedDetachmentPlProofs_generic_par(prefix, stack, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
		} else if (symbol == A) {
			uint32_t remainingSpace = wordLengthLimit - (prefix.length() + stack.size() - 1); // NOTE: Considers that stack still has to pop the current symbol.
			if (remainingSpace < knownLimit + 2)
				return; // cancel already if adding the below sequences would exceed the word length limit
			// 1/|combinations| : D, A, [N1,N<knownLimit>] ; stack: pop current symbol, push [N1,N<knownLimit>] on top of stack
			// ...
			// |combinations|/|combinations| : D, A, [A,A] ; stack: pop current symbol, push [A,A] on top of stack
			prefix += "D"; // same terminal for all cases, so all prefix already
			stack.pop_back(); // pop already for all cases
			vector<uint32_t> stack_copy; // Since there are multiple options, we use copies for all
			string prefix_copy; //          but the last option, in order to restore the parameters.
			for (unsigned i = 0; i < combinations.size() - 1; i++) {
				const pair<array<uint32_t, 2>, unsigned>& p = combinations[i];
				if (remainingSpace < p.second)
					return; // cancel already if adding the following sequences would exceed the word length limit
				stack_copy = stack;
				prefix_copy = prefix;
				stack_copy.insert(stack_copy.end(), p.first.rbegin(), p.first.rend());
				recurse_loadCondensedDetachmentPlProofs_generic_par(prefix_copy, stack_copy, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
			}
			const pair<array<uint32_t, 2>, unsigned>& p = combinations[combinations.size() - 1];
			if (remainingSpace < p.second)
				return; // cancel already if adding the final sequence would exceed the word length limit
			stack.insert(stack.end(), p.first.rbegin(), p.first.rend());
			recurse_loadCondensedDetachmentPlProofs_generic_par(prefix, stack, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
		} else {
			if (symbol > 1 && prefix.length() + symbol + stack.size() - 1 > wordLengthLimit)
				return; // cancel already if adding the below sequences would exceed the word length limit
			stack.pop_back(); // pop already for all cases
			// 1/1 : {w | w is known representative of length <knownLimit>}, N<symbol>, [] ; stack: pop current symbol, push nothing
			processN(allRepresentatives[symbol]);
		}
	}
};
}
void DlProofEnumerator::_loadCondensedDetachmentPlProofs_generic_par(string& prefix, vector<uint32_t>& stack, uint32_t wordLengthLimit, uint32_t knownLimit, const vector<vector<string>>& allRepresentatives, vector<deque<string>>& queues, vector<mutex>& mtxs) {
	const vector<pair<array<uint32_t, 2>, unsigned>> combinations = proofLengthCombinations(knownLimit);
	recurse_loadCondensedDetachmentPlProofs_generic_par(prefix, stack, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
}

void DlProofEnumerator::_loadCondensedDetachmentPlProofs_naive_par(string& prefix, unsigned stackSize, uint32_t wordLengthLimit, vector<deque<string>>& queues, vector<mutex>& mtxs) {
	if (prefix.length() + stackSize > wordLengthLimit)
		return;
	if (!stackSize) {
		bool processed = false;
		unsigned bestIndex = 0;
		unsigned bestSize = UINT_MAX;
		for (unsigned t = 0; t < queues.size(); t++) {
			deque<string>& queue = queues[t];
			size_t size = queue.size();
			if (size) {
				if (size < bestSize) {
					bestIndex = t;
					bestSize = size;
				}
			} else {
				{
					lock_guard<mutex> lock(mtxs[t]);
					queue.push_back(prefix);
				}
				processed = true;
				break;
			}
		}
		if (!processed) {
			lock_guard<mutex> lock(mtxs[bestIndex]);
			queues[bestIndex].push_back(prefix);
		}
	} else {
		// 1/4 : 1, S, [] ; stack: pop current symbol, push nothing
		string prefix_copy = prefix; // Since there are multiple options, we use copies for all but the last option, in order to restore the parameters.
		prefix_copy += "1";
		_loadCondensedDetachmentPlProofs_naive_par(prefix_copy, stackSize - 1, wordLengthLimit, queues, mtxs);

		// 2/4 : 2, S, [] ; stack: pop current symbol, push nothing
		prefix_copy = prefix;
		prefix_copy += "2";
		_loadCondensedDetachmentPlProofs_naive_par(prefix_copy, stackSize - 1, wordLengthLimit, queues, mtxs);

		// 3/4 : 3, S, [] ; stack: pop current symbol, push nothing
		prefix_copy = prefix;
		prefix_copy += "3";
		_loadCondensedDetachmentPlProofs_naive_par(prefix_copy, stackSize - 1, wordLengthLimit, queues, mtxs);

		// 4/4 : D, S, [S,S] ; stack: pop current symbol, push [S,S] on top of stack
		prefix += "D";
		_loadCondensedDetachmentPlProofs_naive_par(prefix, stackSize + 1, wordLengthLimit, queues, mtxs);
	}
}

}
}
