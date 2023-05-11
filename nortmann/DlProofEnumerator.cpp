#include "DlProofEnumerator.h"

#include "../helper/FctHelper.h"
#include "../helper/Resources.h"
#include "../tree/TreeNode.h"
#include "../metamath/DRuleParser.h"
#include "DlCore.h"
#include "DlFormula.h"

#include <boost/filesystem/operations.hpp>

#include <tbb/concurrent_map.h>
#include <tbb/concurrent_queue.h>
#include <tbb/concurrent_unordered_map.h>
#include <tbb/concurrent_unordered_set.h>
#include <tbb/concurrent_vector.h>
#include <tbb/parallel_for.h>
#include <tbb/parallel_sort.h>

#include <cstring>
#include <iostream>

using namespace std;
using namespace xamid::helper;
using namespace xamid::metamath;

namespace xamid {
namespace nortmann {

namespace {
inline string myTime() {
	time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
	return strtok(ctime(&time), "\n");
}
}

const vector<const vector<string>*>& DlProofEnumerator::builtinRepresentatives() {
	static const vector<const vector<string>*> _builtinRepresentatives = { &Resources::dProofRepresentatives1, &Resources::dProofRepresentatives3, &Resources::dProofRepresentatives5, &Resources::dProofRepresentatives7, &Resources::dProofRepresentatives9, &Resources::dProofRepresentatives11, &Resources::dProofRepresentatives13, &Resources::dProofRepresentatives15 };
	return _builtinRepresentatives;
}

const vector<const vector<string>*>& DlProofEnumerator::builtinConclusions() {
	static const vector<const vector<string>*> _builtinConclusions = { &Resources::dProofConclusions1, &Resources::dProofConclusions3, &Resources::dProofConclusions5, &Resources::dProofConclusions7, &Resources::dProofConclusions9, &Resources::dProofConclusions11, &Resources::dProofConclusions13, &Resources::dProofConclusions15 };
	return _builtinConclusions;
}

vector<vector<string>> DlProofEnumerator::composeToLookupVector(const vector<const vector<string>*>& all) {
	vector<vector<string>> all_refined(2 * all.size());
	vector<const vector<string>*>::const_iterator it = all.begin();
	uint32_t limit = static_cast<uint32_t>(2 * all.size() - 1);
	for (uint32_t wordLengthLimit = 1; wordLengthLimit <= limit; wordLengthLimit += 2)
		all_refined[wordLengthLimit] = **it++;
	return all_refined;
}

bool DlProofEnumerator::readRepresentativesLookupVectorFromFiles_seq(vector<vector<string>>& allRepresentativesLookup, vector<vector<string>>* optOut_allConclusionsLookup, bool debug, const string& filePrefix, const string& filePostfix, bool initFresh, uint32_t limit) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (initFresh) {
		if (debug)
			startTime = chrono::steady_clock::now();
		allRepresentativesLookup = composeToLookupVector(builtinRepresentatives());
		if (optOut_allConclusionsLookup)
			*optOut_allConclusionsLookup = composeToLookupVector(builtinConclusions());
		if (debug)
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to load built-in representatives." << endl;
	}
	for (uint32_t wordLengthLimit = static_cast<uint32_t>(allRepresentativesLookup.size() + 1); wordLengthLimit <= limit; wordLengthLimit += 2) { // look for files containing D-proofs, starting from built-in limit + 2
		string file = filePrefix + to_string(wordLengthLimit) + filePostfix;
		if (boost::filesystem::exists(file)) { // load
			allRepresentativesLookup.push_back( { });
			allRepresentativesLookup.push_back( { });
			vector<string>& contents = allRepresentativesLookup.back();
			vector<string>* conclusions = nullptr;
			if (optOut_allConclusionsLookup) {
				optOut_allConclusionsLookup->push_back( { });
				optOut_allConclusionsLookup->push_back( { });
				conclusions = &optOut_allConclusionsLookup->back();
			}
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
				if (i == string::npos) {
					contents.push_back(line);
					if (conclusions) {
						if (debug)
							cerr << "Missing conclusion in data file " << file << "\". Aborting." << endl;
						return false;
					}
				} else {
					contents.push_back(line.substr(0, i));
					if (conclusions)
						conclusions->push_back(line.substr(i + 1));
				}
			}
			if (debug)
				cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to read " << contents.size() << " condensed detachment proofs " << (conclusions ? "and conclusions " : "") << "from " << file << "." << endl;
		} else
			break; // remains to generate
	}
	return true;
}

bool DlProofEnumerator::readRepresentativesLookupVectorFromFiles_par(vector<vector<string>>& allRepresentativesLookup, vector<vector<string>>* optOut_allConclusionsLookup, bool debug, unsigned concurrencyCount, const string& filePrefix, const string& filePostfix, bool initFresh, uint32_t limit, size_t containerReserve) {
	if (concurrencyCount < 2)
		return readRepresentativesLookupVectorFromFiles_seq(allRepresentativesLookup, optOut_allConclusionsLookup, debug, filePrefix, filePostfix, initFresh, limit); // system cannot execute threads concurrently
	chrono::time_point<chrono::steady_clock> startTime;
	if (initFresh) {
		if (debug)
			startTime = chrono::steady_clock::now();
		allRepresentativesLookup = composeToLookupVector(builtinRepresentatives());
		if (optOut_allConclusionsLookup)
			*optOut_allConclusionsLookup = composeToLookupVector(builtinConclusions());
		if (debug)
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to load built-in representatives." << endl;
	}
	vector<unsigned> threadComplete(concurrencyCount);
	vector<unsigned> threadAbort(concurrencyCount);
	vector<string> threadResults(concurrencyCount);
	vector<thread> threads;
	unsigned t = 0;
	bool abortAll = false;
	allRepresentativesLookup.reserve(containerReserve); // ensure that no container reallocations happen during concurrent access, since they would result in data races
	if (optOut_allConclusionsLookup)
		optOut_allConclusionsLookup->reserve(containerReserve);
	for (uint32_t wordLengthLimit = static_cast<uint32_t>(allRepresentativesLookup.size() + 1); wordLengthLimit <= limit; wordLengthLimit += 2) { // look for files containing D-proofs, starting from built-in limit + 2
		const string file = filePrefix + to_string(wordLengthLimit) + filePostfix;
		if (boost::filesystem::exists(file)) { // load
			allRepresentativesLookup.push_back( { });
			allRepresentativesLookup.push_back( { });
			if (optOut_allConclusionsLookup) {
				optOut_allConclusionsLookup->push_back( { });
				optOut_allConclusionsLookup->push_back( { });
			}
			auto load = [&](unsigned t, size_t index, const string& file) {
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
					threadComplete[t] = 1;
					abortAll = true;
					return;
				}
				vector<string>& contents = allRepresentativesLookup[index];
				vector<string>* conclusions = optOut_allConclusionsLookup ? &(*optOut_allConclusionsLookup)[index] : nullptr;
				string line;
				while (getline(fin, line) && !abortAll) {
					string::size_type i = line.find(':'); // support both variants "<D-proof>:<formula>" and "<D-proof>"
					if (i == string::npos) {
						contents.push_back(line);
						if (conclusions) {
							if (debug)
								threadResults[t] = "Missing conclusion in data file " + file + "\". Aborting.";
							threadAbort[t] = 1;
							threadComplete[t] = 1;
							abortAll = true;
							return;
						}
					} else {
						contents.push_back(line.substr(0, i));
						if (conclusions)
							conclusions->push_back(line.substr(i + 1));
					}
				}
				if (debug && !abortAll) {
					stringstream ss;
					ss << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to read " << contents.size() << " condensed detachment proofs " << (conclusions ? "and conclusions " : "") << "from " << file << ". [tid:" << this_thread::get_id() << "]";
					threadResults[t] = ss.str();
				}
				threadComplete[t] = 1;
			};
			if (t < concurrencyCount)
				threads.emplace_back(load, t++, allRepresentativesLookup.size() - 1, file);
			else {
				bool startedNext = false;
				while (!startedNext && !abortAll) {
					for (unsigned t = 0; t < concurrencyCount; t++) {
						if (threadComplete[t]) {
							threadComplete[t] = 0;
							threads[t].join();
							if (threadAbort[t]) {
								if (debug)
									cerr << threadResults[t] << endl;
								for (t = t + 1; t < threads.size(); t++)
									threads[t].join(); // 'abortAll' was set, so soon all loader threads should terminate
								return false;
							} else if (debug)
								cout << threadResults[t] << endl;
							threads[t] = thread(load, t, allRepresentativesLookup.size() - 1, file);
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
			for (t = t + 1; t < threads.size(); t++)
				threads[t].join(); // 'abortAll' was set, so soon all loader threads should terminate
			return false;
		} else if (debug)
			cout << threadResults[t] << endl;
	}
	return true;
}

vector<pair<array<uint32_t, 2>, unsigned>> DlProofEnumerator::proofLengthCombinations(unsigned knownLimit) {
	vector<array<uint32_t, 2>> combinations;
	for (unsigned i = 1; i <= knownLimit; i += 2)
		for (unsigned j = 1; j <= knownLimit; j += 2)
			if (i <= j && i + j > knownLimit) {
				combinations.push_back( { i, j });
				if (i != j)
					combinations.push_back( { j, i });
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

bool DlProofEnumerator::loadDProofRepresentatives(vector<vector<string>>& allRepresentatives, vector<vector<string>>* optOut_allConclusionsLookup, uint64_t* optOut_allRepresentativesCount, uint32_t* optOut_firstMissingIndex, bool debug, const string& filePrefix, const string& filePostfix, bool initFresh, uint32_t limit) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();
	size_t startSize = initFresh ? 0 : allRepresentatives.size();
	if (!readRepresentativesLookupVectorFromFiles_par(allRepresentatives, optOut_allConclusionsLookup, debug, thread::hardware_concurrency(), filePrefix, filePostfix, initFresh, limit))
		return false;
	size_t more = 1;
	if (debug) {
		if (initFresh) {
			size_t total = allRepresentatives.size() / 2;
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
		*optOut_firstMissingIndex = static_cast<uint32_t>(allRepresentatives.size() + 1);
	return true;
}

tbb::concurrent_unordered_map<string, string> DlProofEnumerator::parseDProofRepresentatives(const vector<string>& representatives, ProgressData* const progressData) {
	tbb::concurrent_unordered_map<string, string> representativeProofs;
	if (progressData)
		progressData->setStartTime();
	tbb::parallel_for(tbb::blocked_range<vector<string>::const_iterator>(representatives.begin(), representatives.end()), [&progressData, &representativeProofs](tbb::blocked_range<vector<string>::const_iterator>& range) {
		for (vector<string>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& s = *it;
			vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> rawParseData = DRuleParser::parseDProof_raw(s);
			const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
			// NOTE: Definitely stores, since that is how the input files were constructed.
			representativeProofs.emplace(DlCore::toPolishNotation_noRename(conclusion), s);

			// Show progress if requested
			if (progressData && progressData->nextStep()) {
				uint64_t percentage;
				string progress;
				string etc;
				if (progressData->nextState(percentage, progress, etc))
					cout << myTime() << ": Parsed " << (percentage < 10 ? " " : "") << percentage << "% of D-proofs. [" << progress << "] (" << etc << ")" << endl;
			}
		}
	});
	return representativeProofs;
}

tbb::concurrent_unordered_map<string, string> DlProofEnumerator::parseDProofRepresentatives(const vector<vector<string>>& allRepresentatives, ProgressData* const progressData) {
	tbb::concurrent_unordered_map<string, string> representativeProofs;
	if (progressData)
		progressData->setStartTime();
	for (uint32_t wordLengthLimit = 1; wordLengthLimit < allRepresentatives.size(); wordLengthLimit += 2) { // FASTEST: Parse each string individually and without translation to DlProof objects.
		const vector<string>& representativesOfWordLengthLimit = allRepresentatives[wordLengthLimit];
		tbb::parallel_for(tbb::blocked_range<vector<string>::const_iterator>(representativesOfWordLengthLimit.begin(), representativesOfWordLengthLimit.end()), [&progressData, &representativeProofs](tbb::blocked_range<vector<string>::const_iterator>& range) {
			for (vector<string>::const_iterator it = range.begin(); it != range.end(); ++it) {
				const string& s = *it;
				vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> rawParseData = DRuleParser::parseDProof_raw(s);
				const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
				// NOTE: Definitely stores, since that is how the input files were constructed.
				representativeProofs.emplace(DlCore::toPolishNotation_noRename(conclusion), s);

				// Show progress if requested
				if (progressData && progressData->nextStep()) {
					uint64_t percentage;
					string progress;
					string etc;
					if (progressData->nextState(percentage, progress, etc))
						cout << myTime() << ": Parsed " << (percentage < 10 ? " " : "") << percentage << "% of D-proofs. [" << progress << "] (" << etc << ")" << endl;
				}
			}
		});
	}
	return representativeProofs;
}

tbb::concurrent_unordered_map<string, string> DlProofEnumerator::connectDProofConclusions(const vector<vector<string>>& allRepresentatives, const vector<vector<string>>& allConclusions, ProgressData* const progressData) {
	tbb::concurrent_unordered_map<string, string> representativeProofs;
	if (progressData)
		progressData->setStartTime();
	for (uint32_t wordLengthLimit = 1; wordLengthLimit < allRepresentatives.size(); wordLengthLimit += 2) {
		const vector<string>& representativesOfWordLengthLimit = allRepresentatives[wordLengthLimit];
		if (representativesOfWordLengthLimit.empty())
			continue;
		const vector<string>& conclusionsOfWordLengthLimit = allConclusions[wordLengthLimit];
		if (representativesOfWordLengthLimit.size() != conclusionsOfWordLengthLimit.size())
			throw invalid_argument("allRepresentatives[" + to_string(wordLengthLimit) + "].size() = " + to_string(representativesOfWordLengthLimit.size()) + " != " + to_string(conclusionsOfWordLengthLimit.size()) + " = allConclusions[" + to_string(wordLengthLimit) + "].size()");
		tbb::parallel_for(size_t(0), representativesOfWordLengthLimit.size(), [&progressData, &representativeProofs, &representativesOfWordLengthLimit, &conclusionsOfWordLengthLimit](size_t i) { // NOTE: Counts from i = start := 0 until i < end := representativesOfWordLengthLimit.size().
			// NOTE: Definitely stores, since that is how the input files were constructed.
			representativeProofs.emplace(conclusionsOfWordLengthLimit[i], representativesOfWordLengthLimit[i]);

			// Show progress if requested
			if (progressData && progressData->nextStep()) {
				uint64_t percentage;
				string progress;
				string etc;
				if (progressData->nextState(percentage, progress, etc))
					cout << myTime() << ": Inserted " << (percentage < 10 ? " " : "") << percentage << "% of D-proof conclusions. [" << progress << "] (" << etc << ")" << endl;
			}
		});
	}
	return representativeProofs;
}

void DlProofEnumerator::countNextIterationAmount(bool redundantSchemaRemoval, bool withConclusions) {
	chrono::time_point<chrono::steady_clock> startTime;

	// 1. Load representative D-proof strings.
	auto myInfo = [&]() -> string {
		stringstream ss;
		ss << "[parallel ; " << thread::hardware_concurrency() << " hardware thread contexts" << (redundantSchemaRemoval ? "" : ", unfiltered") << "]";
		return ss.str();
	};
	cout << myTime() << ": Next iteration amount counter started. " << myInfo() << endl;
	string filePrefix = withConclusions ? "data/dProofs-withConclusions/dProofs" : "data/dProofs-withoutConclusions/dProofs";
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	vector<vector<string>> allConclusions;
	uint64_t allRepresentativesCount;
	uint32_t wordLengthLimit;
	if (!loadDProofRepresentatives(allRepresentatives, withConclusions ? &allConclusions : nullptr, &allRepresentativesCount, &wordLengthLimit, true, filePrefix, filePostfix))
		return;
	uint32_t unfilteredStart = 0;
	if (!redundantSchemaRemoval) {
		unfilteredStart = wordLengthLimit;
		filePostfix = "-unfiltered" + to_string(wordLengthLimit) + "+.txt";
		if (!loadDProofRepresentatives(allRepresentatives, withConclusions ? &allConclusions : nullptr, &allRepresentativesCount, &wordLengthLimit, true, filePrefix, filePostfix, false))
			return;
	}

	// 2. Initialize and prepare progress data.
	bool showProgress = allRepresentatives.size() > 15;
	ProgressData parseProgress = showProgress ? ProgressData(allRepresentatives.size() > 27 ? 5 : allRepresentatives.size() > 25 ? 10 : 20, allRepresentativesCount) : ProgressData();

	// 3. Prepare representative proofs that are already known addressable by conclusions, for filtering.
	startTime = chrono::steady_clock::now();
	tbb::concurrent_unordered_map<string, string> representativeProofs;
	representativeProofs = withConclusions ? connectDProofConclusions(allRepresentatives, allConclusions, showProgress ? &parseProgress : nullptr) : parseDProofRepresentatives(allRepresentatives, showProgress ? &parseProgress : nullptr);
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " total " << (withConclusions ? "" : "parse, conversion & ") << "insertion duration." << endl;

	// 4. Iterate and count candidates of length 'wordLengthLimit'.
	cout << myTime() << ": Starting to iterate D-proof candidates of length " << wordLengthLimit << "." << endl;
	uint64_t counter;
	const vector<uint32_t> stack = { wordLengthLimit }; // do not generate all words up to a certain length, but only of length 'wordLengthLimit' ; NOTE: Uses nonterminal 'A' as lower limit 'wordLengthLimit' in combination with upper limit 'wordLengthLimit'.
	const unsigned knownLimit = wordLengthLimit - 2;
	auto _iterateRepresentatives = [&]() -> uint64_t {
		atomic<uint64_t> counter { 0 };
		processCondensedDetachmentPlProofs_generic(stack, wordLengthLimit, knownLimit, allRepresentatives, [&counter](string& sequence) { counter++; });
		return counter;
	};
	startTime = chrono::steady_clock::now();
	counter = _iterateRepresentatives();
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to iterate " << counter << " condensed detachment proof strings of length " << wordLengthLimit << "." << endl;
	// e.g. 17              :     11.54 ms                        taken to iterate     31388
	//      19              :     42.47 ms                        taken to iterate     94907
	//      21              :     98.47 ms                        taken to iterate    290392
	//      23              :    280.59 ms                        taken to iterate    886041
	//      25              :    897.72 ms                        taken to iterate   2709186
	//      27              :   3248.31 ms (       3 s 248.31 ms) taken to iterate   8320672
	//      29              :   9294.50 ms (       9 s 294.50 ms) taken to iterate  25589216
	//      29-unfiltered27+:  10765.89 ms (      10 s 765.88 ms) taken to iterate  27452198
	//      29-unfiltered25+:  12193.00 ms (      12 s 193.00 ms) taken to iterate  30038660
	//      29-unfiltered23+:  12953.30 ms (      12 s 953.30 ms) taken to iterate  32772266
	//      29-unfiltered21+:  14458.88 ms (      14 s 458.88 ms) taken to iterate  36185400
	//      29-unfiltered19+:  15760.71 ms (      15 s 760.71 ms) taken to iterate  40243692
	//      29-unfiltered17+:  19397.85 ms (      19 s 397.85 ms) taken to iterate  44934432
	//      31              :  35628.12 ms (      35 s 628.12 ms) taken to iterate  78896376 ;  78896376 / 44934432 ≈ 1.75581 ;  35628.12 / 19397.85 ≈ 1.83670
	//      33-unfiltered31+: 106942.91 ms (1 min 46 s 942.90 ms) taken to iterate 260604052 ; 260604052 / 78896376 ≈ 3.30312 ; 106942.91 / 35628.12 ≈ 3.00164
	cout << "[Copy] Next iteration count (" << (redundantSchemaRemoval || unfilteredStart == wordLengthLimit ? "filtered" : "unfiltered" + to_string(unfilteredStart) + "+") << "): { " << wordLengthLimit << ", " << counter << " }" << endl;
	cout << myTime() << ": Next iteration amount counter complete. " << myInfo() << endl;
}

bool DlProofEnumerator::determineCountingLimit(uint32_t wordLengthLimit, uint64_t& count, const map<uint32_t, uint64_t>& counts, bool iteration) {
	map<uint32_t, uint64_t>::const_iterator itIterationCount = counts.find(wordLengthLimit);
	if (itIterationCount == counts.end()) {
		map<uint32_t, uint64_t>::const_iterator itLastKnown = prev(counts.end());
		while (itLastKnown->first > wordLengthLimit)
			itLastKnown = prev(itLastKnown); // bridge potential gaps to reach the relevant entries
		map<uint32_t, uint64_t>::const_iterator itPrevLastKnown = prev(itLastKnown);
		uint32_t lastKnownLimit = itLastKnown->first;
		uint64_t lastKnownCount = itLastKnown->second;
		while (itLastKnown->first != itPrevLastKnown->first + 2) { // to not require the initial amount stored, approximate from earlier pairs if necessary
			itLastKnown = prev(itLastKnown);
			itPrevLastKnown = prev(itPrevLastKnown);
		}
		double lastKnownGrowth = static_cast<double>(itLastKnown->second) / static_cast<double>(itPrevLastKnown->second);
		uint32_t exp = (wordLengthLimit - lastKnownLimit) / 2;
		double estimatedLimit = static_cast<double>(lastKnownCount) * pow(lastKnownGrowth, exp);
		count = static_cast<uint64_t>(estimatedLimit);
		cout << "Estimated " << (iteration ? "iteration" : "removal") << " count set to " << count << ", based on last known pair (" << itPrevLastKnown->first << ":" << itPrevLastKnown->second << ", " << itLastKnown->first << ":" << itLastKnown->second << ") with " << itLastKnown->second << "/" << itPrevLastKnown->second << " ≈ " << lastKnownGrowth << " and " << itLastKnown->second << " * (" << itLastKnown->second << "/" << itPrevLastKnown->second << ")^" << (wordLengthLimit - lastKnownLimit) / 2 << " ≈ " << FctHelper::round(estimatedLimit, 2) << "." << endl;
		return true;
	} else {
		count = itIterationCount->second;
		cout << "Known " << (iteration ? "iteration" : "removal") << " count loaded from " << itIterationCount->first << ":" << itIterationCount->second << "." << endl;
		return false;
	}
}

map<uint32_t, uint64_t>& DlProofEnumerator::iterationCounts_filtered() {
	static map<uint32_t, uint64_t> _ = { { 1, 3 }, { 3, 9 }, { 5, 36 }, { 7, 108 }, { 9, 372 }, { 11, 1134 }, { 13, 3354 }, { 15, 10360 }, { 17, 31388 }, { 19, 94907 }, { 21, 290392 }, { 23, 886041 }, { 25, 2709186 }, { 27, 8320672 }, { 29, 25589216 }, { 31, 78896376 }, { 33, 243907474 } };
	return _;
}

map<uint32_t, map<uint32_t, uint64_t>>& DlProofEnumerator::iterationCounts_unfiltered() {
	static map<uint32_t, map<uint32_t, uint64_t>> _ = {
			{ 17, { { 19, 103475 }, { 21, 350830 }, { 23, 1173825 }, { 25, 3951918 }, { 27, 13339002 }, { 29, 44934432 } } },
			{ 19, {                 { 21, 315238 }, { 23, 1061733 }, { 25, 3546684 }, { 27, 11942738 }, { 29, 40243692 } } },
			{ 21, {                                 { 23,  958731 }, { 25, 3221706 }, { 27, 10765954 }, { 29, 36185400 } } },
			{ 23, {                                                  { 25, 2921214 }, { 27,  9822130 }, { 29, 32772266 } } },
			{ 25, {                                                                   { 27,  8949562 }, { 29, 30038660 } } },
			{ 27, {                                                                                     { 29, 27452198 }, { 31, 92103906 } } },
			{ 29, {                                                                                                       { 31, 84452466 }, { 33, 283384726 } } },
			{ 31, {                                                                                                                         { 33, 260604052 }, { 35, 874253765 }, { 37, 2917037256 }, { 39, 9795199165 } } },
			{ 33, {                                                                                                                                            { 35, 805814039 }, { 37, 2703737502 } } },
	};
	return _;
}

map<uint32_t, uint64_t>& DlProofEnumerator::removalCounts() {
	static map<uint32_t, uint64_t> _ = { { 1, 0 }, { 3, 0 }, { 5, 3 }, { 7, 6 }, { 9, 24 }, { 11, 59 }, { 13, 171 }, { 15, 504 }, { 17, 1428 }, { 19, 4141 }, { 21, 12115 }, { 23, 35338 }, { 25, 104815 }, { 27, 310497 }, { 29, 926015 }, { 31, 2782763 } };
	return _;
}

void DlProofEnumerator::generateDProofRepresentativeFiles(uint32_t limit, bool redundantSchemaRemoval, bool withConclusions) { // NOTE: More debug code & performance results available before https://github.com/deontic-logic/proof-tool/commit/45627054d14b6a1e08eb56eaafcf7cf202f2ab96 ; representation of formulas as tree structures before https://github.com/xamidi/pmGenerator/commit/1d05f2a646563061162be9ad0db68946499ac867
	chrono::time_point<chrono::steady_clock> startTime;

	// 1. Load representative D-proof strings.
	auto myInfo = [&]() -> string {
		stringstream ss;
		ss << "[parallel ; " << thread::hardware_concurrency() << " hardware thread contexts" << (limit == UINT32_MAX ? "" : ", limit: " + to_string(limit)) << (redundantSchemaRemoval ? "" : ", unfiltered") << "]";
		return ss.str();
	};
	cout << myTime() << ": " << (limit == UINT32_MAX ? "Unl" : "L") << "imited D-proof representative generator started. " << myInfo() << endl;
	string filePrefix = withConclusions ? "data/dProofs-withConclusions/dProofs" : "data/dProofs-withoutConclusions/dProofs";
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	vector<vector<string>> allConclusions;
	uint64_t allRepresentativesCount;
	uint32_t start;
	if (!loadDProofRepresentatives(allRepresentatives, withConclusions ? &allConclusions : nullptr, &allRepresentativesCount, &start, true, filePrefix, filePostfix))
		return;
	// e.g., for up to 'data/dProofs29.txt' present:
	//   0.07 ms taken to load built-in representatives.                                             | [with conclusions]    0.30 ms [...] detachment proofs and conclusions from [...]
	//   0.09 ms taken to read    5221 condensed detachment proofs from data/dProofs17.txt. [tid:2]  |                       0.55 ms [...] detachment proofs and conclusions from [...]
	//   0.19 ms taken to read   15275 condensed detachment proofs from data/dProofs19.txt. [tid:3]  |                       0.72 ms [...] detachment proofs and conclusions from [...]
	//   4.04 ms taken to read   44206 condensed detachment proofs from data/dProofs21.txt. [tid:4]  |                       8.09 ms [...] detachment proofs and conclusions from [...]
	//  16.71 ms taken to read  129885 condensed detachment proofs from data/dProofs23.txt. [tid:5]  |                      62.56 ms [...] detachment proofs and conclusions from [...]
	//  66.17 ms taken to read  385789 condensed detachment proofs from data/dProofs25.txt. [tid:6]  |                     213.14 ms [...] detachment proofs and conclusions from [...]
	// 201.04 ms taken to read 1149058 condensed detachment proofs from data/dProofs27.txt. [tid:7]  |                     683.21 ms [...] detachment proofs and conclusions from [...]
	// 743.53 ms taken to read 3449251 condensed detachment proofs from data/dProofs29.txt. [tid:8]  |                    2312.06 ms [...] detachment proofs and conclusions from [...]
	// 755.49 ms total read duration.                                                                |                    2338.89 ms (2 s 338.89 ms) total read duration.
	// Loaded 15 representative collections of sizes:
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
	// 29 : 3449251
	// 5181578 representatives in total.
	uint32_t unfilteredStart = 0;
	if (!redundantSchemaRemoval) {
		unfilteredStart = start;
		filePostfix = "-unfiltered" + to_string(start) + "+.txt";
		if (!loadDProofRepresentatives(allRepresentatives, withConclusions ? &allConclusions : nullptr, &allRepresentativesCount, &start, true, filePrefix, filePostfix, false))
			return;
	}
	if (start > limit) {
		cout << myTime() << ": Limited D-proof representative generator skipped. " << myInfo() << endl;
		return;
	}

	// 2. Initialize and prepare progress data.
	bool showProgress = allRepresentatives.size() > 15;
	ProgressData parseProgress = showProgress ? ProgressData(allRepresentatives.size() > 27 ? 5 : allRepresentatives.size() > 25 ? 10 : 20, allRepresentativesCount) : ProgressData();
	ProgressData findProgress;
	ProgressData removalProgress;

	// 3. Prepare representative proofs that are already known addressable by conclusions, for filtering.
	startTime = chrono::steady_clock::now();
	tbb::concurrent_unordered_map<string, string> representativeProofs;
	representativeProofs = withConclusions ? connectDProofConclusions(allRepresentatives, allConclusions, showProgress ? &parseProgress : nullptr) : parseDProofRepresentatives(allRepresentatives, showProgress ? &parseProgress : nullptr);
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " total " << (withConclusions ? "" : "parse, conversion & ") << "insertion duration." << endl;
	// e.g. 15:    165.82 ms                         total parse, conversion & insertion duration.  | [with conclusions]   1.06 ms total insertion duration.
	//      17:    482.36 ms                         total parse, conversion & insertion duration.  |                      2.07 ms total insertion duration.
	//      19:   1550.04 ms (        1 s 550.04 ms) total parse, conversion & insertion duration.  |                      4.81 ms total insertion duration.
	//      21:   5136.59 ms (        5 s 136.59 ms) total parse, conversion & insertion duration.  |                     12.96 ms total insertion duration.
	//      23:  17861.15 ms (       17 s 861.15 ms) total parse, conversion & insertion duration.  |                     32.84 ms total insertion duration.
	//      25:  61647.44 ms ( 1 min  1 s 647.44 ms) total parse, conversion & insertion duration.  |                     93.01 ms total insertion duration.
	//      27: 213272.64 ms ( 3 min 33 s 272.64 ms) total parse, conversion & insertion duration.  |                    293.06 ms total insertion duration.
	//      29: 741236.66 ms (12 min 21 s 236.66 ms) total parse, conversion & insertion duration.  |                    877.29 ms total insertion duration.
	//#cout << "Done loading (measure memory requirement)." << endl; while (true);

	// 4. Compute and store new representatives.
	map<uint32_t, uint64_t> iterationCounts;
	for (uint32_t wordLengthLimit = start; wordLengthLimit <= limit; wordLengthLimit += 2) {

		// 4.1 Prepare progress data.
		showProgress = wordLengthLimit >= 17;
		// NOTE: Static count maps are built dynamically and may contain gaps, in which case earlier
		//       values are used to approximate the exponential growth rate, based on which new values
		//       are approximated in order to estimate ongoing progress of unknown scale.
		if (iterationCounts.empty()) {
			if (redundantSchemaRemoval)
				iterationCounts = iterationCounts_filtered();
			else {
				for (const pair<const uint32_t, uint64_t>& p : iterationCounts_filtered())
					if (p.first <= unfilteredStart)
						iterationCounts.insert(p);
					else
						break;
				map<uint32_t, uint64_t>& counts = iterationCounts_unfiltered()[unfilteredStart];
				iterationCounts.insert(counts.begin(), counts.end());
			}
		}
		if (showProgress) {
			uint64_t iterationCount;
			bool iterationCountEstimated = determineCountingLimit(wordLengthLimit, iterationCount, iterationCounts, true);
			findProgress = ProgressData(wordLengthLimit >= 27 ? 2 : wordLengthLimit >= 25 ? 5 : wordLengthLimit >= 23 ? 10 : 20, iterationCount, iterationCountEstimated);
			if (redundantSchemaRemoval) {
				uint64_t removalCount;
				bool removalCountEstimated = determineCountingLimit(wordLengthLimit, removalCount, removalCounts(), false);
				removalProgress = ProgressData(wordLengthLimit >= 23 ? 2 : wordLengthLimit >= 21 ? 5 : wordLengthLimit >= 19 ? 10 : 20, removalCount, removalCountEstimated);
			}
		}

		cout << myTime() << ": Starting to generate D-proof representatives of length " << wordLengthLimit << "." << endl;

		// 4.2 Iterate proofs of length 'wordLengthLimit' and generate their conclusions.
		uint64_t counter;
		uint64_t representativeCounter;
		uint64_t redundantCounter;
		uint64_t invalidCounter;
		const vector<uint32_t> stack = { wordLengthLimit }; // do not generate all words up to a certain length, but only of length 'wordLengthLimit' ; NOTE: Uses nonterminal 'A' as lower limit 'wordLengthLimit' in combination with upper limit 'wordLengthLimit'.
		const unsigned knownLimit = wordLengthLimit - 2;
		startTime = chrono::steady_clock::now();
		_findProvenFormulas(representativeProofs, wordLengthLimit, DlProofEnumeratorMode::Generic, showProgress ? &findProgress : nullptr, &counter, &representativeCounter, &redundantCounter, &invalidCounter, &stack, &knownLimit, &allRepresentatives);
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to collect " << representativeCounter << " D-proofs of length " << wordLengthLimit << ". [iterated " << counter << " condensed detachment proof strings]" << endl;
		// e.g. 17:    1631.72 ms (        1 s 631.72 ms) taken to collect    6649 [...]
		//      19:    5586.94 ms (        5 s 586.94 ms) taken to collect   19416 [...] ;    5586.94 /   1631.72 ≈ 3.42396
		//      21:   20238.31 ms (       20 s 238.31 ms) taken to collect   56321 [...] ;   20238.31 /   5586.94 ≈ 3.62243
		//      23:   72496.97 ms ( 1 min 12 s 496.97 ms) taken to collect  165223 [...] ;   72496.97 /  20238.31 ≈ 3.58217
		//      25:  258267.65 ms ( 4 min 18 s 267.65 ms) taken to collect  490604 [...] ;  258267.65 /  72496.97 ≈ 3.56246
		//      27:  916905.86 ms (15 min 16 s 905.86 ms) taken to collect 1459555 [...] ;  916905.86 / 258267.65 ≈ 3.55022
		//      29: 3187900.65 ms (53 min  7 s 900.65 ms) taken to collect 4375266 [...] ; 3187900.65 / 916905.86 ≈ 3.47680

		// 4.3 Update iteration progress information.
		iterationCounts.emplace(wordLengthLimit, counter);
		(redundantSchemaRemoval ? iterationCounts_filtered() : (wordLengthLimit <= unfilteredStart ? iterationCounts_filtered() : iterationCounts_unfiltered()[unfilteredStart])).emplace(wordLengthLimit, counter); // also save progress statically for potential subsequent generations
		//#cout << "Updated iterationCounts: " << FctHelper::mapString(iterationCounts) << ", static entry: " << FctHelper::mapString(redundantSchemaRemoval ? iterationCounts_filtered() : iterationCounts_unfiltered()[unfilteredStart]) << endl;
		cout << "[Copy] Static filtered iteration counts: " << FctHelper::mapStringF(iterationCounts_filtered(), [](const pair<const uint32_t, uint64_t>& p) { return "{ " + to_string(p.first) + ", " + to_string(p.second) + " }"; }, "{ ", " }") << endl;
		if (!redundantSchemaRemoval)
			cout << "[Copy] Static unfiltered iteration counts: { " << unfilteredStart << ", " << FctHelper::mapStringF(iterationCounts_unfiltered()[unfilteredStart], [](const pair<const uint32_t, uint64_t>& p) { return "{ " + to_string(p.first) + ", " + to_string(p.second) + " }"; }, "{ ", " }") << " }," << endl;

		// 4.4 Remove new proofs with redundant conclusions.
		// NOTE: For a few steps more to not take ages (but still get all minimal D-proofs up to a certain length), one can skip the time-intensive filtering below and then
		//       load 'dProofs17.txt', ..., 'dProofs<n>.txt', 'dProofs<n+1>-unfiltered<n+1>+.txt', ..., 'dProofs<n+m>-unfiltered<n+1>+.txt', for <n+1> being the first 'wordLengthLimit'
		//       used to generate files without redundant conclusions removal.
		//       Due to the higher growth rate of sets with unfiltered schema redundancies, the difference in size can get significant, e.g.
		//       'dProofs25.txt'               and 'dProofs27.txt'               are 10.030.513 and 32.173.623 bytes in size (i.e. 385789 and 1149058 D-proofs), respectively, whereas  [1149058 / 385789 ≈ 2.97846]
		//       'dProofs25-unfiltered17+.txt' and 'dProofs27-unfiltered17+.txt' are 19.969.715 and 70.423.275 bytes in size (i.e. 768066 and 2515117 D-proofs), respectively.          [2515117 / 768066 ≈ 3.27461 ; 768066 / 385789 ≈ 1.99090 ; 2515117 / 1149058 ≈ 2.18885]
		//       Where one enters the unfiltered strategy makes quite a difference, e.g.
		//       'dProofs25-unfiltered25+.txt' and 'dProofs27-unfiltered25+.txt' are 12.755.703 and 47.068.055 bytes is size (i.e. 490604 and 1681002 D-proofs), respectively, and      [1681002 / 490604 ≈ 3.42639 ; 490604 / 385789 ≈ 1.27169 ; 1681002 / 1149058 ≈ 1.46294]
		//       generating 'dProofs17.txt', ..., 'dProofs23.txt' doesn't take long. But while generating 'dProofs25.txt' and 'dProofs27.txt' take several hours and over a day on an average PC, respectively, generating
		//       'dProofs25-unfiltered25+.txt' and 'dProofs27-unfiltered25+.txt' only take around 5 and 20 minutes, respectively. But the latter also take more memory, so a good choice really boils down to space and time constraints.
		//       For instance, on a machine with limited RAM, the only way to use all proof representatives up to a certain length without page faults may be to generate 'dProofs<n>.txt' for <n> sufficiently high. For example,
		//       loading up to 'dProofs31-unfiltered17+.txt' (39157358 representatives) requires ≈19.95 GiB of memory, whereas loading up to 'dProofs31-unfiltered31+.txt' (18375771 representatives) requires only ≈9.84 GiB.
		if (redundantSchemaRemoval) {
			startTime = chrono::steady_clock::now();
			uint64_t oldRepresentativeCounter = representativeCounter;
			// TODO: Performance should be improved significantly if possible. Can we define a schema tree database structure to reduce the amount of schema checks?
			_removeRedundantConclusionsForProofsOfMaxLength(wordLengthLimit, representativeProofs, showProgress ? &removalProgress : nullptr, representativeCounter, redundantCounter);
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to detect " << oldRepresentativeCounter - representativeCounter << " conclusions for which there are more general variants proven in lower or equal amounts of steps." << endl;
			// e.g. 17:     1440.11 ms (                1 s 440.11 ms) taken to detect   1428 conclusions [...]
			//      19:    13487.20 ms (               13 s 487.20 ms) taken to detect   4141 conclusions [...] ;    13487.20 /     1440.11 ≈ 9.36540
			//      21:   120905.65 ms (         2 min      905.65 ms) taken to detect  12115 conclusions [...] ;   120905.65 /    13487.20 ≈ 8.96447
			//      23:  1136294.46 ms (        18 min 56 s 294.46 ms) taken to detect  35338 conclusions [...] ;  1136294.46 /   120905.65 ≈ 9.39819
			//      25: 10569544.36 ms (    2 h 56 min  9 s 544.36 ms) taken to detect 104815 conclusions [...] ; 10569544.36 /  1136294.46 ≈ 9.30177
			//      27: 96153314.21 ms (1 d 2 h 42 min 33 s 314.21 ms) taken to detect 310497 conclusions [...] ; 96153314.21 / 10569544.36 ≈ 9.09721

			// 4.5 Update removal progress information.
			removalCounts().emplace(wordLengthLimit, oldRepresentativeCounter - representativeCounter);
			//#cout << "Updated removalCounts: " << FctHelper::mapString(removalCounts()) << endl;
			cout << "[Copy] Static filtered removal counts: " << FctHelper::mapStringF(removalCounts(), [](const pair<const uint32_t, uint64_t>& p) { return "{ " + to_string(p.first) + ", " + to_string(p.second) + " }"; }, "{ ", " }") << endl;
		}

		// 4.6 Order and output information.
		startTime = chrono::steady_clock::now();
		map<string::size_type, size_t> amountPerLength;
		set<string, cmpStringGrow> newRepresentativeSequences;
		map<string, string, cmpStringGrow> newContent;
		if (withConclusions)
			for (const pair<const string, string>& p : representativeProofs) {
				string::size_type len = p.second.length();
				if (len == wordLengthLimit)
					newContent.emplace(p.second, p.first);
				amountPerLength[len]++;
			}
		else
			for (const pair<const string, string>& p : representativeProofs) {
				string::size_type len = p.second.length();
				if (len == wordLengthLimit)
					newRepresentativeSequences.insert(p.second);
				amountPerLength[len]++;
			}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to filter and order new representative proofs." << endl;
		cout << "Found " << representativeCounter << " representative, " << redundantCounter << " redundant, and " << invalidCounter << " invalid condensed detachment proof strings." << endl;
		cout << "lengths up to " << wordLengthLimit << " ; amounts per length: " << FctHelper::mapString(amountPerLength) << " ; " << (withConclusions ? newContent.size() : newRepresentativeSequences.size()) << " new representative proofs (" << redundantCounter << " redundant, " << invalidCounter << " invalid)" << endl;
		// e.g. 17:    5221 representative,   14809 redundant, and   11358 invalid condensed detachment proof strings
		//      19:   15275 representative,   44743 redundant, and   34889 invalid condensed detachment proof strings
		//      21:   44206 representative,  134493 redundant, and  111693 invalid condensed detachment proof strings
		//      23:  129885 representative,  409159 redundant, and  346997 invalid condensed detachment proof strings
		//      25:  385789 representative, 1243007 redundant, and 1080390 invalid condensed detachment proof strings
		//      27: 1149058 representative, 3778453 redundant, and 3393161 invalid condensed detachment proof strings

		// 4.7 Store information for current run. Note that 'allRepresentatives' (unlike 'allConclusions') must be updated since it is used for D-proof generation.
		allRepresentatives.push_back( { });
		if (withConclusions) {
			vector<string> representatives;
			for (map<string, string, cmpStringGrow>::const_iterator it = newContent.begin(); it != newContent.end(); ++it)
				representatives.push_back(it->first);
			allRepresentatives.push_back(representatives);
		} else
			allRepresentatives.push_back(vector<string>(newRepresentativeSequences.begin(), newRepresentativeSequences.end()));

		// 4.8 Store information permanently. Not using FctHelper::writeToFile() in order to write huge files without huge string acquisition.
		startTime = chrono::steady_clock::now();
		string file = filePrefix + to_string(wordLengthLimit) + filePostfix;
		string::size_type bytes = 0;
		{
			while (!boost::filesystem::exists(file) && !FctHelper::ensureDirExists(file))
				cerr << "Failed to create file at \"" << file << "\", trying again." << endl;
			cout << myTime() << ": Starting to write " << allRepresentatives.back().size() << " entries to " << file << "." << endl;
			ofstream fout(file, fstream::out | fstream::binary);
			bool first = true;
			if (withConclusions)
				for (const pair<const string, string>& p : newContent) {
					const string& dProof = p.first;
					const string& conclusion = p.second;
					if (first) {
						bytes += dProof.length() + conclusion.length() + 1;
						fout << dProof << ":" << conclusion;
						first = false;
					} else {
						bytes += dProof.length() + conclusion.length() + 2;
						fout << "\n" << dProof << ":" << conclusion;
					}
				}
			else
				for (const string& s : allRepresentatives.back())
					if (first) {
						bytes += s.length();
						fout << s;
						first = false;
					} else {
						bytes += s.length() + 1;
						fout << "\n" << s;
					}
		}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << bytes << " bytes of representative condensed detachment proof strings to " << file << "." << endl;
	}
	cout << myTime() << ": Limited D-proof representative generator complete. " << myInfo() << endl;
}

void DlProofEnumerator::mpi_filterDProofRepresentativeFile(uint32_t wordLengthLimit, bool smoothProgress) {
	chrono::time_point<chrono::steady_clock> startTime;

	// Obtain the process ID and the number of processes
	int mpi_size;
	int mpi_rank;
	MPI_Comm_size(MPI_COMM_WORLD, &mpi_size);
	MPI_Comm_rank(MPI_COMM_WORLD, &mpi_rank);
	if (mpi_size <= 1)
		cerr << "Single-process call. Utilize multiple processes via \"mpiexec -n <np> ./pmGenerator <args>\" or \"srun -n <np> ./pmGenerator <args>\" (or similar), for np > 1." << endl;

	// 1. Load representative D-proof strings.
	auto myInfo = [&]() -> string {
		stringstream ss;
		ss << "[rank " << mpi_rank << " on \"" << FctHelper::mpi_nodeName() << "\" ; " << mpi_size << " process" << (mpi_size == 1 ? "" : "es") << " ; " << thread::hardware_concurrency() << " local hardware thread contexts]";
		return ss.str();
	};
	cout << myTime() + ": MPI-based D-proof representative filter started. " + myInfo() << endl;
	bool isMainProc = mpi_rank == 0;
	string filePrefix = "data/dProofs-withConclusions/dProofs";
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	vector<vector<string>> allConclusions;
	uint64_t allRepresentativesCount;
	uint32_t start;
	if (!loadDProofRepresentatives(allRepresentatives, &allConclusions, &allRepresentativesCount, &start, isMainProc, filePrefix, filePostfix)) {
		cerr << "[Rank " + to_string(mpi_rank) + "] Failed to load D-proof representatives. Aborting." << endl;
		MPI_Abort(MPI_COMM_WORLD, 1);
		return;
	}
	if (start != wordLengthLimit) {
		cerr << "[Rank " + to_string(mpi_rank) + "] First unfiltered file to load would be ./" + filePrefix + to_string(start) + "-unfiltered" + to_string(start) + "+.txt, but wordLengthLimit := " + to_string(wordLengthLimit) + ". Aborting." << endl;
		MPI_Abort(MPI_COMM_WORLD, 1);
		return;
	}
	if (!loadDProofRepresentatives(allRepresentatives, &allConclusions, &allRepresentativesCount, &start, isMainProc, filePrefix, "-unfiltered" + to_string(start) + "+.txt", false, wordLengthLimit)) {
		cerr << "[Rank " + to_string(mpi_rank) + "] Failed to load D-proof representatives. Aborting." << endl;
		MPI_Abort(MPI_COMM_WORLD, 1);
		return;
	}
	if (start != wordLengthLimit + 2) {
		cerr << "[Rank " + to_string(mpi_rank) + "] Could not find ./" + filePrefix + to_string(wordLengthLimit) + "-unfiltered" + to_string(wordLengthLimit) + ".txt. Aborting." << endl;
		MPI_Abort(MPI_COMM_WORLD, 1);
		return;
	}
	if (isMainProc) {
		ManagedArray<uint64_t> recvbuf(mpi_size);
		MPI_Gather(&allRepresentativesCount, 1, MPI_UNSIGNED_LONG_LONG, recvbuf.data, 1, MPI_UNSIGNED_LONG_LONG, 0, MPI_COMM_WORLD);
		for (int source = 1; source < mpi_size; source++)
			if (allRepresentativesCount != recvbuf.data[source]) {
				cerr << "Uniform loading failed: " + to_string(allRepresentativesCount) + " representatives loaded on rank 0, but " + to_string(recvbuf.data[source]) + " representatives loaded on rank " + to_string(source) + ". Aborting." << endl;
				MPI_Abort(MPI_COMM_WORLD, 1);
				return;
			}
		cout << myTime() + ": Representative collections were initialized successfully on all ranks." << endl;
	} else
		MPI_Gather(&allRepresentativesCount, 1, MPI_UNSIGNED_LONG_LONG, nullptr, 1, MPI_UNSIGNED_LONG_LONG, 0, MPI_COMM_WORLD);

	// 2. Initialize and prepare progress data.
	bool showProgress = isMainProc && allRepresentatives.size() > 15;
	ProgressData connectProgress = showProgress ? ProgressData(allRepresentatives.size() > 27 ? 5 : allRepresentatives.size() > 25 ? 10 : 20, allRepresentativesCount) : ProgressData();
	ProgressData removalProgress;
	if (isMainProc) {
		uint64_t removalCount;
		bool removalCountEstimated = determineCountingLimit(wordLengthLimit, removalCount, removalCounts(), false);
		removalProgress = ProgressData(wordLengthLimit >= 23 ? 2 : wordLengthLimit >= 21 ? 5 : wordLengthLimit >= 19 ? 10 : 20, removalCount, removalCountEstimated);
	}

	// 3. Prepare representative proofs that are already known addressable by conclusions, for filtering.
	if (isMainProc)
		startTime = chrono::steady_clock::now();
	tbb::concurrent_unordered_map<string, string> representativeProofs;
	representativeProofs = connectDProofConclusions(allRepresentatives, allConclusions, showProgress ? &connectProgress : nullptr);
	if (isMainProc)
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) + " total insertion duration." << endl;

	// 4. Remove new proofs with redundant conclusions.
	const vector<string>& recentRepresentativeSequence = allRepresentatives[wordLengthLimit];
	const vector<string>& recentConclusionSequence = allConclusions[wordLengthLimit];
	if (isMainProc)
		startTime = chrono::steady_clock::now();
	tbb::concurrent_unordered_set<uint64_t> redundant = _mpi_findRedundantConclusionsForProofsOfMaxLength(mpi_rank, mpi_size, wordLengthLimit, representativeProofs, recentConclusionSequence, isMainProc ? &removalProgress : nullptr, smoothProgress);
	if (isMainProc)
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) + " taken to detect " + to_string(redundant.size()) + " conclusions for which there are more general variants proven in lower or equal amounts of steps." << endl;

	// 5. Print removal progress information.
	if (isMainProc) {
		cout << "Found " + to_string(recentRepresentativeSequence.size() - redundant.size()) + " representative and " + to_string(redundant.size()) + " redundant condensed detachment proof strings." << endl;
		cout << "[Copy] Removal count: { " + to_string(wordLengthLimit) + ", " + to_string(redundant.size()) + " }" << endl;
	}

	// 6. Store new representatives.
	tbb::concurrent_map<string, string, cmpStringGrow> newContent;
	if (isMainProc) {

		// 6.1 Order information.
		startTime = chrono::steady_clock::now();
		tbb::parallel_for(size_t(0), recentRepresentativeSequence.size(), [&recentRepresentativeSequence, &recentConclusionSequence, &redundant, &newContent](size_t i) { // NOTE: Counts from i = start := 0 until i < end := recentRepresentativeSequence.size().
			if (!redundant.count(i))
				newContent.emplace(recentRepresentativeSequence[i], recentConclusionSequence[i]);
		});
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) + " taken to filter and order new representative proofs." << endl;

		// 6.2 Store information permanently. Not using FctHelper::writeToFile() in order to write huge files without huge string acquisition.
		startTime = chrono::steady_clock::now();
		string file = filePrefix + to_string(wordLengthLimit) + filePostfix;
		string::size_type bytes = 0;
		{
			while (!boost::filesystem::exists(file) && !FctHelper::ensureDirExists(file))
				cerr << "Failed to create file at \"" + file + "\", trying again." << endl;
			cout << myTime() + ": Starting to write " + to_string(newContent.size()) + " entries to " + file + "." << endl;
			ofstream fout(file, fstream::out | fstream::binary);
			bool first = true;
			for (const pair<const string, string>& p : newContent) {
				const string& dProof = p.first;
				const string& conclusion = p.second;
				if (first) {
					bytes += dProof.length() + conclusion.length() + 1;
					fout << dProof << ":" << conclusion;
					first = false;
				} else {
					bytes += dProof.length() + conclusion.length() + 2;
					fout << "\n" << dProof << ":" << conclusion;
				}
			}
		}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) + " taken to print and save " + to_string(bytes) + " bytes of representative condensed detachment proof strings to " + file + "." << endl;
	}
	cout << myTime() + ": MPI-based D-proof representative filter complete. " + myInfo() << endl;
}

void DlProofEnumerator::createGeneratorFilesWithConclusions(const string& inputFilePrefix, const string& outputFilePrefix, bool debug) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();

	// 1. Load generated D-proofs.
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	uint64_t allRepresentativesCount;
	uint32_t filteredMissing;
	if (!loadDProofRepresentatives(allRepresentatives, nullptr, &allRepresentativesCount, &filteredMissing, debug, inputFilePrefix)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}
	filePostfix = "-unfiltered" + to_string(filteredMissing) + "+.txt";
	uint32_t unfilteredMissing;
	if (!loadDProofRepresentatives(allRepresentatives, nullptr, &allRepresentativesCount, &unfilteredMissing, debug, inputFilePrefix, filePostfix, false)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}

	// 2. Parse generated D-proofs and keep their conclusion representation strings.
	for (uint32_t wordLengthLimit = 1; wordLengthLimit < allRepresentatives.size(); wordLengthLimit += 2) {
		const vector<string>& representativesOfWordLengthLimit = allRepresentatives[wordLengthLimit];
		ProgressData parseProgress(wordLengthLimit >= 27 ? 5 : wordLengthLimit >= 25 ? 10 : 20, representativesOfWordLengthLimit.size());
		if (debug)
			startTime = chrono::steady_clock::now();
		tbb::concurrent_unordered_map<string, string> representativeProofs = parseDProofRepresentatives(representativesOfWordLengthLimit, wordLengthLimit > 15 ? &parseProgress : nullptr);
		map<string, string, cmpStringGrow> result;
		for (const pair<const string, string>& p : representativeProofs)
			result.emplace(p.second, p.first);
		if (debug) {
			cout << wordLengthLimit << ": Parsed " << representativeProofs.size() << " generated D-proofs in " << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << "." << endl;
			//#cout << FctHelper::mapStringF(result, [](const pair<const string, string>& p) { return p.first + ":" + p.second; }, { }, { }, "\n");
		}

		// 3. Store generated D-proofs together with their conclusions permanently. Not using FctHelper::writeToFile() in order to write huge files without huge string acquisition.
		startTime = chrono::steady_clock::now();
		string file = outputFilePrefix + to_string(wordLengthLimit) + (wordLengthLimit < filteredMissing ? ".txt" : filePostfix);
		string::size_type bytes = 0;
		{
			while (!boost::filesystem::exists(file) && !FctHelper::ensureDirExists(file))
				cerr << "Failed to create file at \"" << file << "\", trying again." << endl;
			cout << myTime() << ": Starting to write " << result.size() << " entries to " << file << "." << endl;
			ofstream fout(file, fstream::out | fstream::binary);
			bool first = true;
			for (const pair<const string, string>& p : result) {
				const string& dProof = p.first;
				const string& conclusion = p.second;
				if (first) {
					bytes += dProof.length() + conclusion.length() + 1;
					fout << dProof << ":" << conclusion;
					first = false;
				} else {
					bytes += dProof.length() + conclusion.length() + 2;
					fout << "\n" << dProof << ":" << conclusion;
				}
			}
		}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << bytes << " bytes of representative condensed detachment proof strings to " << file << "." << endl;

		//#if (wordLengthLimit <= 15)
		//#	cout << "const vector<string> Resources::dProofConclusions" << wordLengthLimit << " = " << FctHelper::mapStringF(result, [](const pair<const string, string>& p) { return p.second; }, "{ \"", "\" };", "\", \"") << endl;
	}
}

void DlProofEnumerator::createGeneratorFilesWithoutConclusions(const string& inputFilePrefix, const string& outputFilePrefix, bool debug) {
	chrono::time_point<chrono::steady_clock> startTime;
	if (debug)
		startTime = chrono::steady_clock::now();

	// 1. Load generated D-proofs.
	string filePostfix = ".txt";
	vector<vector<string>> allRepresentatives;
	uint64_t allRepresentativesCount;
	uint32_t filteredMissing;
	if (!loadDProofRepresentatives(allRepresentatives, nullptr, &allRepresentativesCount, &filteredMissing, debug, inputFilePrefix)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}
	filePostfix = "-unfiltered" + to_string(filteredMissing) + "+.txt";
	uint32_t unfilteredMissing;
	if (!loadDProofRepresentatives(allRepresentatives, nullptr, &allRepresentativesCount, &unfilteredMissing, debug, inputFilePrefix, filePostfix, false)) {
		cerr << "Failed to load generated D-proof data." << endl;
		return;
	}

	// 2. Store generated D-proofs without their conclusions permanently. Not using FctHelper::writeToFile() in order to write huge files without huge string acquisition.
	for (uint32_t wordLengthLimit = 1; wordLengthLimit < allRepresentatives.size(); wordLengthLimit += 2) {
		startTime = chrono::steady_clock::now();
		string file = outputFilePrefix + to_string(wordLengthLimit) + (wordLengthLimit < filteredMissing ? ".txt" : filePostfix);
		string::size_type bytes = 0;
		{
			while (!boost::filesystem::exists(file) && !FctHelper::ensureDirExists(file))
				cerr << "Failed to create file at \"" << file << "\", trying again." << endl;
			cout << myTime() << ": Starting to write " << allRepresentatives[wordLengthLimit].size() << " entries to " << file << "." << endl;
			ofstream fout(file, fstream::out | fstream::binary);
			bool first = true;
			for (const string& s : allRepresentatives[wordLengthLimit])
				if (first) {
					bytes += s.length();
					fout << s;
					first = false;
				} else {
					bytes += s.length() + 1;
					fout << "\n" << s;
				}
		}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << bytes << " bytes of representative condensed detachment proof strings to " << file << "." << endl;
	}
}

void DlProofEnumerator::printConclusionLengthPlotData(bool measureSymbolicLength, bool table, int64_t cutX, int64_t cutY, const string& inputFilePrefix, ostream* mout, bool debug) {
	ostream& _mout = mout ? *mout : cout;
	chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	vector<vector<string>> allRepresentatives;
	vector<vector<string>> allConclusions;
	uint64_t allRepresentativesCount;
	uint32_t firstMissingIndex;
	if (!loadDProofRepresentatives(allRepresentatives, &allConclusions, &allRepresentativesCount, &firstMissingIndex, debug, inputFilePrefix)) {
		cerr << "Failed to load generated D-proof data after " << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << "." << endl; //
		return;
	}
	if (debug) // e.g. Loaded 5181578 D-proof representatives and conclusions in 2249.86 ms (2 s 249.85 ms). firstMissingIndex = 31
		cout << "Loaded " << allRepresentativesCount << " D-proof representatives and conclusions in " << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << ". firstMissingIndex = " << firstMissingIndex << endl;
	for (uint32_t wordLengthLimit = 1; wordLengthLimit < allRepresentatives.size(); wordLengthLimit += 2) {
		const vector<string>& conclusions = allConclusions[wordLengthLimit];
		map<size_t, size_t> allAmounts;
		size_t totalLen = 0;
		//#size_t index = 0;
		for (const string& conclusion : conclusions) {
			size_t len = measureSymbolicLength ? DlCore::symbolicLen_polishNotation_noRename_numVars(conclusion) : conclusion.length(); // formula symbolic length (i.e. amount of nodes in syntax tree) in case 'measureSymbolicLength' is true ; formula representation length, otherwise
			allAmounts[len]++;
			totalLen += len;
			//#if (conclusion == "C0CCNC1C2.3NC4C5C6C7C8C9CCC10C11.12C10.11CC10C11.12C10.12CC1.2C1.3")
			//#	_mout << wordLengthLimit << ": " << allRepresentatives[wordLengthLimit][index] << ":" << conclusion << ", formula representation length: " << conclusion.length() << ", len = " << len << endl;
			//#index++;
		}
		_mout << wordLengthLimit << ": Average " << (measureSymbolicLength ? "symbolic " : "") << "conclusion " << (measureSymbolicLength ? "" : "representation ") << "length is " << totalLen << "/" << conclusions.size() << " ≈ " << FctHelper::round(static_cast<long double>(totalLen) / static_cast<long double>(conclusions.size()), 2) << "." << endl;
		//  1: Average symbolic conclusion length is        27/      3 ≈   9.00.
		//  3: Average symbolic conclusion length is        74/      6 ≈  12.33.
		//  5: Average symbolic conclusion length is       180/     12 ≈  15.00.
		//  7: Average symbolic conclusion length is       641/     38 ≈  16.87.
		//  9: Average symbolic conclusion length is      1974/     89 ≈  22.18.
		// 11: Average symbolic conclusion length is      6142/    229 ≈  26.82.
		// 13: Average symbolic conclusion length is     20894/    672 ≈  31.09.
		// 15: Average symbolic conclusion length is     69153/   1844 ≈  37.50.
		// 17: Average symbolic conclusion length is    229265/   5221 ≈  43.91.
		// 19: Average symbolic conclusion length is    777218/  15275 ≈  50.88.
		// 21: Average symbolic conclusion length is   2619118/  44206 ≈  59.25.
		// 23: Average symbolic conclusion length is   8848047/ 129885 ≈  68.12.
		// 25: Average symbolic conclusion length is  30064575/ 385789 ≈  77.93.
		// 27: Average symbolic conclusion length is 102125860/1149058 ≈  88.88.
		// 29: Average symbolic conclusion length is 347393279/3449251 ≈ 100.72.
		// https://www.wolframalpha.com/input?key=&i=plot[(1,9.00),(3,12.33),(5,15.00),(7,16.87),(9,22.18),(11,26.82),(13,31.09),(15,37.50),(17,43.91),(19,50.88),(21,59.25),(23,68.12),(25,77.93),(27,88.88),(29,100.72)]
		// Plot data: 1 9.00 3 12.33 5 15.00 7 16.87 9 22.18 11 26.82 13 31.09 15 37.50 17 43.91 19 50.88 21 59.25 23 68.12 25 77.93 27 88.88 29 100.72
		// Polynomial regression result: 0.0009958x³ + 0.046x² + 1.027x + 8.235
		//  1: Average conclusion representation length is        32/      3 ≈  10.67.
		//  3: Average conclusion representation length is        87/      6 ≈  14.50.
		//  5: Average conclusion representation length is       209/     12 ≈  17.42.
		//  7: Average conclusion representation length is       751/     38 ≈  19.76.
		//  9: Average conclusion representation length is      2324/     89 ≈  26.11.
		// 11: Average conclusion representation length is      7231/    229 ≈  31.58.
		// 13: Average conclusion representation length is     24616/    672 ≈  36.63.
		// 15: Average conclusion representation length is     81554/   1844 ≈  44.23.
		// 17: Average conclusion representation length is    270214/   5221 ≈  51.76.
		// 19: Average conclusion representation length is    915915/  15275 ≈  59.96.
		// 21: Average conclusion representation length is   3086761/  44206 ≈  69.83.
		// 23: Average conclusion representation length is  10426278/ 129885 ≈  80.27.
		// 25: Average conclusion representation length is  35431952/ 385789 ≈  91.84.
		// 27: Average conclusion representation length is 120402334/1149058 ≈ 104.78.
		// 29: Average conclusion representation length is 409793912/3449251 ≈ 118.81.
		// https://www.wolframalpha.com/input?key=&i=plot[(1,10.67),(3,14.50),(5,17.42),(7,19.76),(9,26.11),(11,31.58),(13,36.63),(15,44.23),(17,51.76),(19,59.96),(21,69.83),(23,80.27),(25,91.84),(27,104.78),(29,118.81)]
		// Plot data: 1 10.67 3 14.50 5 17.42 7 19.76 9 26.11 11 31.58 13 36.63 15 44.23 17 51.76 19 59.96 21 69.83 23 80.27 25 91.84 27 104.78 29 118.81
		// Polynomial regression result: 0.001137x³ + 0.056x² + 1.188x + 9.707

		size_t amountEvenConclusionLen = 0;
		for (map<size_t, size_t>::const_iterator it = allAmounts.begin(); it != allAmounts.end(); ++it)
			if (it->first % 2 == 0)
				amountEvenConclusionLen += it->second;
		size_t amountOddConclusionLen = conclusions.size() - amountEvenConclusionLen;
		_mout << string(FctHelper::digitsNum_uint32(wordLengthLimit), ' ') << "  There are " << amountEvenConclusionLen << " minimal D-proofs with conclusion" << (measureSymbolicLength ? "" : " representation") << "s of even " << (measureSymbolicLength ? "symbolic " : "") << "length, and " << amountOddConclusionLen << " minimal D-proofs with conclusion" << (measureSymbolicLength ? "" : " representation") << "s of odd " << (measureSymbolicLength ? "symbolic " : "") << "length. [" << amountEvenConclusionLen << "/" << conclusions.size() << " ≈ " << FctHelper::round(static_cast<long double>(amountEvenConclusionLen * 100) / static_cast<long double>(conclusions.size()), 2) << "% even]" << endl;
		// 'measureSymbolicLength' true:
		//  1:     0/      3 ≈ 0.00% even
		//  3:     0/      6 ≈ 0.00% even
		//  5:     0/     12 ≈ 0.00% even
		//  7:     1/     38 ≈ 2.63% even
		//  9:     1/     89 ≈ 1.12% even
		// 11:     5/    229 ≈ 2.18% even
		// 13:    18/    672 ≈ 2.68% even
		// 15:    45/   1844 ≈ 2.44% even
		// 17:   130/   5221 ≈ 2.49% even
		// 19:   371/  15275 ≈ 2.43% even
		// 21:  1046/  44206 ≈ 2.37% even
		// 23:  3106/ 129885 ≈ 2.39% even
		// 25:  9376/ 385789 ≈ 2.43% even
		// 27: 28232/1149058 ≈ 2.46% even
		// 29: 85734/3449251 ≈ 2.49% even
		// Plot data:  1, 0, 3, 0, 5, 0, 7, 0.0263, 9, 0.0112, 11, 0.0218, 13, 0.0268, 15, 0.0244, 17, 0.0249, 19, 0.0243, 21, 0.0237, 23, 0.0239, 25, 0.0243, 27, 0.0246, 29, 0.0249
		// 'measureSymbolicLength' false:
		//  1:       3/      3 ≈ 100.00% even
		//  3:       3/      6 ≈  50.00% even
		//  5:       7/     12 ≈  58.33% even
		//  7:      19/     38 ≈  50.00% even
		//  9:      39/     89 ≈  43.82% even
		// 11:     102/    229 ≈  44.54% even
		// 13:     286/    672 ≈  42.56% even
		// 15:     744/   1844 ≈  40.35% even
		// 17:    2131/   5221 ≈  40.82% even
		// 19:    6246/  15275 ≈  40.89% even
		// 21:   18055/  44206 ≈  40.84% even
		// 23:   53449/ 129885 ≈  41.15% even
		// 25:  158883/ 385789 ≈  41.18% even
		// 27:  474534/1149058 ≈  41.30% even
		// 29: 1430031/3449251 ≈  41.46% even
		// Plot data: 1, 1, 3, 0.5, 5, 0.5833, 7, 0.5, 9, 0.4382, 11, 0.4454, 13, 0.4256, 15, 0.4035, 17, 0.4082, 19, 0.4089, 21, 0.4084, 23, 0.4115, 25, 0.4118, 27, 0.4130, 29, 0.4146

		size_t maxLen = prev(allAmounts.end())->first;
		if (cutX >= 0) {
			maxLen = min(maxLen, static_cast<size_t>(cutX));
			for (size_t i = 1; i <= maxLen; i++)
				allAmounts[i];
			if (cutX > 0)
				allAmounts.erase(next(allAmounts.find(maxLen)), allAmounts.end());
			else
				allAmounts.clear();
		} else
			for (size_t i = 1; i <= maxLen; i++)
				allAmounts[i];
		if (cutY >= 0)
			for (map<size_t, size_t>::const_iterator it = allAmounts.begin(); it != allAmounts.end();) {
				if (it->second > static_cast<size_t>(cutY))
					it = allAmounts.erase(it);
				else
					++it;
			}
		if (table)
			_mout << FctHelper::mapStringF(allAmounts, [](const pair<size_t, size_t>& p) { return to_string(p.first) + "\t" + to_string(p.second); }, { }, "\n", "\n") << endl;
		else
			_mout << FctHelper::mapStringF(allAmounts, [](const pair<size_t, size_t>& p) { return to_string(p.first) + " " + to_string(p.second); }, { }, "\n", " ") << endl;
		// formula representation lengths: ([1,1000] data) [x <= 500] https://www.desmos.com/calculator/b9qvvkinal, https://i.imgur.com/IMFY84S.png ; [x,y <= 1000] https://www.desmos.com/calculator/tjej0cpyju, https://i.imgur.com/1Z4WjJa.png ; [x <= 1000, y <= 100] https://www.desmos.com/calculator/zpe5zw41cm, https://i.imgur.com/6aCR6iq.png
		// formula symbolic lengths:       ([1,1000] data) [x <= 500] https://www.desmos.com/calculator/ghdmsv1x0j, https://i.imgur.com/OoYz14L.png ; [x,y <= 1000] https://www.desmos.com/calculator/0fra8us8af, https://i.imgur.com/VBtlRJR.png ; [x <= 1000, y <= 100] https://www.desmos.com/calculator/fdlj86pp3f, https://i.imgur.com/GMnPub1.png
		// Plot data [1,500] (e.g. for https://www.rapidtables.com/tools/scatter-plot.html):
		// 1. representation lengths
		//    23: 1 0 2 0 3 0 4 0 5 0 6 0 7 0 8 0 9 1 10 3 11 3 12 8 13 7 14 24 15 43 16 79 17 94 18 95 19 160 20 330 21 476 22 493 23 421 24 513 25 977 26 1152 27 1132 28 831 29 1189 30 1640 31 2119 32 1567 33 1336 34 1430 35 2325 36 2264 37 2146 38 1373 39 1780 40 2273 41 2512 42 1992 43 1750 44 1513 45 2124 46 2077 47 2045 48 1374 49 1674 50 1510 51 2134 52 1516 53 1762 54 1276 55 1778 56 1298 57 1825 58 1169 59 1625 60 1146 61 1695 62 997 63 1670 64 919 65 1538 66 884 67 1577 68 899 69 1407 70 794 71 1521 72 813 73 1459 74 791 75 1380 76 704 77 1270 78 676 79 1190 80 716 81 1171 82 641 83 1260 84 570 85 1049 86 631 87 883 88 504 89 905 90 486 91 906 92 518 93 918 94 467 95 925 96 491 97 719 98 528 99 762 100 421 101 797 102 436 103 758 104 425 105 676 106 360 107 752 108 340 109 548 110 394 111 590 112 338 113 651 114 299 115 569 116 344 117 481 118 272 119 600 120 284 121 377 122 280 123 428 124 206 125 422 126 218 127 349 128 264 129 319 130 165 131 346 132 194 133 326 134 217 135 310 136 191 137 345 138 170 139 329 140 194 141 274 142 152 143 342 144 169 145 279 146 167 147 271 148 180 149 246 150 153 151 248 152 171 153 240 154 122 155 240 156 172 157 202 158 137 159 177 160 110 161 246 162 111 163 181 164 155 165 160 166 124 167 187 168 115 169 152 170 108 171 134 172 69 173 193 174 77 175 118 176 102 177 132 178 111 179 146 180 69 181 135 182 83 183 118 184 56 185 122 186 107 187 129 188 75 189 95 190 61 191 142 192 63 193 103 194 74 195 103 196 58 197 82 198 67 199 105 200 67 201 87 202 38 203 114 204 47 205 93 206 73 207 74 208 47 209 82 210 33 211 79 212 41 213 67 214 28 215 86 216 45 217 55 218 52 219 82 220 34 221 73 222 50 223 76 224 46 225 57 226 39 227 94 228 40 229 48 230 44 231 75 232 27 233 81 234 48 235 54 236 55 237 44 238 30 239 49 240 25 241 62 242 35 243 38 244 28 245 49 246 38 247 43 248 35 249 42 250 21 251 36 252 26 253 53 254 30 255 29 256 32 257 31 258 27 259 38 260 21 261 34 262 32 263 43 264 27 265 39 266 27 267 28 268 16 269 33 270 16 271 27 272 19 273 48 274 19 275 37 276 21 277 27 278 24 279 29 280 19 281 60 282 15 283 22 284 18 285 22 286 24 287 31 288 14 289 25 290 10 291 26 292 12 293 25 294 11 295 19 296 19 297 22 298 13 299 35 300 8 301 20 302 20 303 18 304 10 305 24 306 19 307 14 308 16 309 9 310 8 311 19 312 16 313 20 314 15 315 14 316 16 317 15 318 8 319 8 320 15 321 19 322 9 323 13 324 13 325 14 326 15 327 10 328 8 329 15 330 5 331 10 332 8 333 6 334 4 335 16 336 5 337 7 338 13 339 15 340 10 341 18 342 9 343 12 344 10 345 12 346 10 347 14 348 5 349 7 350 7 351 18 352 7 353 19 354 6 355 7 356 10 357 9 358 9 359 18 360 5 361 11 362 5 363 7 364 9 365 18 366 3 367 9 368 13 369 8 370 5 371 10 372 5 373 12 374 5 375 7 376 7 377 21 378 6 379 8 380 5 381 10 382 10 383 8 384 7 385 11 386 8 387 6 388 10 389 5 390 1 391 6 392 8 393 8 394 3 395 8 396 6 397 3 398 3 399 8 400 3 401 8 402 4 403 12 404 2 405 3 406 5 407 4 408 2 409 8 410 5 411 2 412 4 413 5 414 2 415 7 416 12 417 8 418 2 419 7 420 1 421 4 422 5 423 4 424 2 425 8 426 1 427 4 428 2 429 7 430 2 431 7 432 2 433 3 434 2 435 6 436 5 437 4 438 3 439 6 440 7 441 8 442 3 443 8 444 5 445 3 446 4 447 5 448 2 449 6 450 2 451 5 452 4 453 2 454 2 455 4 456 3 457 3 458 1 459 4 460 1 461 4 462 1 463 2 464 2 465 1 466 2 467 4 468 5 469 5 470 3 471 2 472 0 473 2 474 2 475 3 476 2 477 0 478 3 479 3 480 2 481 10 482 2 483 2 484 4 485 3 486 2 487 2 488 3 489 2 490 0 491 3 492 2 493 1 494 2 495 1 496 1 497 3 498 1 499 2 500 0
		//    25: 1 0 2 0 3 0 4 0 5 0 6 1 7 1 8 1 9 2 10 3 11 6 12 12 13 23 14 41 15 45 16 77 17 129 18 258 19 308 20 330 21 413 22 716 23 1153 24 1301 25 1137 26 1240 27 2164 28 2798 29 3084 30 2354 31 2721 32 3684 33 5151 34 4297 35 3737 36 3395 37 5055 38 5870 39 5780 40 3896 41 4257 42 5392 43 6234 44 5488 45 5034 46 4056 47 5398 48 5506 49 5746 50 4218 51 4649 52 3977 53 5569 54 4553 55 4809 56 3708 57 5043 58 3585 59 5095 60 3461 61 4442 62 3452 63 4466 64 3040 65 4722 66 2725 67 4390 68 2658 69 4429 70 2670 71 4211 72 2375 73 3947 74 2528 75 4124 76 2342 77 4134 78 2206 79 3895 80 2191 81 3513 82 2072 83 3383 84 1965 85 3240 86 1895 87 3413 88 1753 89 3170 90 1660 91 2970 92 1615 93 2701 94 1540 95 2842 96 1424 97 2675 98 1652 99 2662 100 1398 101 2546 102 1387 103 2355 104 1440 105 2255 106 1183 107 2446 108 1252 109 2192 110 1311 111 1950 112 974 113 2017 114 1100 115 1894 116 1096 117 1655 118 986 119 1868 120 911 121 1651 122 1010 123 1424 124 761 125 1628 126 809 127 1390 128 899 129 1207 130 707 131 1531 132 604 133 1037 134 750 135 1141 136 654 137 1180 138 703 139 1067 140 773 141 1014 142 538 143 1213 144 547 145 923 146 736 147 1022 148 486 149 1026 150 605 151 1014 152 640 153 838 154 504 155 1042 156 519 157 739 158 624 159 713 160 436 161 817 162 422 163 808 164 453 165 598 166 475 167 743 168 413 169 576 170 460 171 733 172 339 173 620 174 301 175 586 176 441 177 496 178 347 179 643 180 382 181 500 182 323 183 518 184 253 185 540 186 298 187 419 188 355 189 444 190 240 191 500 192 264 193 398 194 291 195 394 196 338 197 415 198 223 199 358 200 268 201 439 202 208 203 444 204 179 205 353 206 270 207 305 208 194 209 358 210 187 211 387 212 185 213 282 214 152 215 315 216 196 217 327 218 207 219 245 220 167 221 366 222 151 223 254 224 177 225 251 226 211 227 284 228 145 229 250 230 170 231 230 232 131 233 290 234 135 235 257 236 211 237 199 238 143 239 227 240 126 241 246 242 137 243 228 244 110 245 180 246 144 247 182 248 156 249 216 250 114 251 255 252 98 253 127 254 103 255 174 256 124 257 204 258 107 259 126 260 123 261 151 262 78 263 167 264 111 265 159 266 143 267 139 268 85 269 121 270 62 271 161 272 79 273 126 274 64 275 178 276 108 277 124 278 85 279 95 280 76 281 152 282 88 283 151 284 79 285 97 286 80 287 107 288 78 289 122 290 86 291 134 292 44 293 125 294 55 295 96 296 76 297 119 298 42 299 126 300 57 301 116 302 50 303 84 304 55 305 110 306 84 307 84 308 61 309 68 310 44 311 78 312 48 313 79 314 54 315 86 316 68 317 71 318 50 319 66 320 56 321 60 322 43 323 80 324 36 325 63 326 64 327 45 328 41 329 74 330 46 331 76 332 42 333 40 334 22 335 56 336 47 337 79 338 60 339 55 340 38 341 70 342 33 343 66 344 41 345 56 346 49 347 56 348 35 349 50 350 30 351 53 352 29 353 72 354 40 355 59 356 67 357 49 358 39 359 35 360 29 361 56 362 32 363 48 364 32 365 45 366 35 367 55 368 30 369 42 370 29 371 55 372 18 373 39 374 31 375 39 376 39 377 76 378 26 379 46 380 47 381 38 382 28 383 37 384 21 385 46 386 36 387 34 388 26 389 32 390 32 391 31 392 23 393 35 394 23 395 48 396 21 397 38 398 30 399 21 400 11 401 36 402 19 403 28 404 15 405 33 406 29 407 28 408 21 409 34 410 24 411 42 412 13 413 28 414 15 415 20 416 20 417 38 418 22 419 40 420 15 421 35 422 12 423 25 424 14 425 37 426 19 427 33 428 13 429 23 430 7 431 33 432 11 433 20 434 19 435 21 436 14 437 24 438 11 439 20 440 20 441 33 442 31 443 31 444 13 445 27 446 25 447 17 448 15 449 27 450 13 451 27 452 12 453 20 454 12 455 38 456 15 457 23 458 11 459 16 460 7 461 24 462 5 463 17 464 8 465 14 466 18 467 16 468 14 469 11 470 19 471 21 472 8 473 29 474 5 475 9 476 13 477 10 478 6 479 13 480 9 481 17 482 21 483 26 484 9 485 14 486 13 487 7 488 11 489 21 490 12 491 13 492 2 493 6 494 14 495 7 496 11 497 19 498 4 499 11 500 12
		//    27: 1 0 2 0 3 0 4 0 5 0 6 0 7 0 8 3 9 3 10 2 11 7 12 13 13 24 14 39 15 71 16 122 17 152 18 211 19 345 20 650 21 849 22 932 23 1076 24 1684 25 2893 26 3474 27 3248 28 3105 29 4906 30 6541 31 7989 32 6376 33 6467 34 8369 35 11880 36 11239 37 10355 38 8676 39 11367 40 14384 41 15447 42 11622 43 10966 44 12870 45 15440 46 15053 47 13672 48 11061 49 13859 50 13925 51 14867 52 12744 53 12828 54 10703 55 14432 56 12390 57 13172 58 10916 59 12666 60 10635 61 13998 62 9580 63 12923 64 9650 65 12270 66 9079 67 12498 68 8358 69 12044 70 7838 71 12483 72 7858 73 12235 74 7482 75 11497 76 7212 77 11218 78 7051 79 11056 80 6669 81 11036 82 6642 83 11251 84 6238 85 10038 86 6346 87 9558 88 5635 89 9427 90 5360 91 9282 92 5349 93 9142 94 4871 95 9014 96 4859 97 8083 98 4958 99 8047 100 4568 101 8285 102 4426 103 7949 104 4572 105 7564 106 4198 107 7543 108 3890 109 6543 110 4173 111 6878 112 3629 113 6859 114 3531 115 6331 116 3932 117 5838 118 3268 119 6189 120 3272 121 5345 122 3334 123 5595 124 2783 125 5074 126 2901 127 4830 128 2981 129 4457 130 2447 131 4920 132 2516 133 4249 134 2638 135 4014 136 2189 137 4191 138 2296 139 3896 140 2452 141 3507 142 2108 143 4195 144 2028 145 3369 146 2373 147 3559 148 2093 149 3546 150 1899 151 3235 152 2156 153 3021 154 1744 155 3319 156 1878 157 2894 158 1939 159 2926 160 1628 161 3019 162 1607 163 2705 164 1894 165 2468 166 1467 167 2718 168 1644 169 2147 170 1582 171 2212 172 1261 173 2552 174 1216 175 1998 176 1474 177 1926 178 1288 179 2242 180 1091 181 1953 182 1410 183 1798 184 991 185 1957 186 1202 187 1767 188 1230 189 1509 190 970 191 2040 192 925 193 1683 194 1065 195 1539 196 966 197 1591 198 1032 199 1451 200 894 201 1377 202 822 203 1728 204 739 205 1273 206 1100 207 1314 208 804 209 1310 210 786 211 1426 212 759 213 1230 214 633 215 1308 216 734 217 1054 218 779 219 1166 220 584 221 1218 222 636 223 1173 224 657 225 906 226 680 227 1302 228 672 229 908 230 620 231 1130 232 534 233 1134 234 602 235 955 236 808 237 902 238 590 239 961 240 487 241 868 242 557 243 877 244 423 245 909 246 517 247 751 248 570 249 709 250 430 251 996 252 459 253 741 254 485 255 576 256 480 257 734 258 425 259 730 260 455 261 630 262 405 263 731 264 328 265 584 266 561 267 610 268 412 269 585 270 332 271 553 272 382 273 645 274 297 275 583 276 392 277 551 278 396 279 515 280 286 281 658 282 328 283 540 284 363 285 534 286 394 287 555 288 294 289 462 290 336 291 483 292 251 293 524 294 219 295 397 296 329 297 378 298 242 299 560 300 194 301 443 302 291 303 385 304 212 305 468 306 305 307 388 308 290 309 333 310 185 311 418 312 200 313 422 314 237 315 380 316 254 317 388 318 255 319 309 320 217 321 365 322 190 323 347 324 176 325 281 326 267 327 277 328 187 329 350 330 161 331 293 332 190 333 258 334 144 335 273 336 186 337 244 338 193 339 266 340 146 341 294 342 156 343 250 344 168 345 274 346 222 347 278 348 158 349 210 350 163 351 253 352 109 353 319 354 138 355 228 356 215 357 216 358 168 359 255 360 130 361 264 362 155 363 187 364 146 365 213 366 176 367 185 368 126 369 203 370 115 371 252 372 98 373 182 374 126 375 157 376 144 377 246 378 123 379 230 380 131 381 215 382 120 383 196 384 113 385 192 386 152 387 146 388 105 389 190 390 105 391 146 392 133 393 180 394 96 395 190 396 121 397 132 398 124 399 144 400 95 401 173 402 74 403 188 404 81 405 130 406 105 407 181 408 81 409 167 410 91 411 141 412 73 413 153 414 65 415 104 416 152 417 112 418 63 419 165 420 74 421 137 422 84 423 119 424 51 425 145 426 93 427 107 428 85 429 127 430 55 431 122 432 54 433 139 434 74 435 85 436 77 437 103 438 60 439 89 440 77 441 138 442 74 443 146 444 83 445 106 446 84 447 109 448 55 449 110 450 53 451 106 452 65 453 92 454 46 455 125 456 60 457 111 458 81 459 90 460 31 461 106 462 40 463 79 464 43 465 88 466 57 467 73 468 90 469 67 470 70 471 81 472 53 473 113 474 44 475 86 476 54 477 47 478 43 479 63 480 38 481 161 482 55 483 68 484 60 485 94 486 61 487 68 488 60 489 68 490 39 491 81 492 51 493 61 494 61 495 40 496 57 497 68 498 46 499 66 500 43
		//    29: 1 0 2 0 3 0 4 0 5 0 6 0 7 0 8 1 9 0 10 8 11 10 12 9 13 29 14 45 15 74 16 110 17 231 18 391 19 538 20 622 21 964 22 1747 23 2510 24 2890 25 3014 26 3999 27 6951 28 8725 29 9058 30 8208 31 11131 32 15571 33 20033 34 17605 35 16788 36 19883 37 27764 38 29300 39 28117 40 23630 41 26845 42 34649 43 38644 44 33507 45 30314 46 31122 47 37903 48 39814 49 37192 50 31108 51 35735 52 35839 53 39528 54 35371 55 35620 56 31398 57 38159 58 32832 59 37960 60 31024 61 34731 62 30482 63 36779 64 28619 65 36055 66 26625 67 35378 68 26289 69 34809 70 24988 71 33489 72 23657 73 33095 74 23183 75 33534 76 22009 77 33060 78 21680 79 32181 80 21435 81 30623 82 19677 83 30239 84 19970 85 30506 86 18943 87 29858 88 18223 89 28999 90 17523 91 27078 92 16949 93 25822 94 15844 95 27245 96 14972 97 26465 98 15424 99 25127 100 14521 101 24407 102 14374 103 23640 104 14248 105 23371 106 13132 107 23977 108 13273 109 22207 110 13347 111 21105 112 12083 113 21571 114 11872 115 20023 116 11895 117 19296 118 11215 119 20091 120 10717 121 18019 122 11407 123 17561 124 9702 125 18107 126 9662 127 16205 128 10267 129 15255 130 8656 131 16245 132 8238 133 14112 134 8984 135 14084 136 7587 137 14415 138 7756 139 12921 140 8647 141 12352 142 6987 143 13926 144 6976 145 11567 146 8180 147 11984 148 6553 149 12192 150 7024 151 11303 152 7221 153 10592 154 6359 155 12106 156 6186 157 9542 158 7323 159 9790 160 5488 161 10426 162 5571 163 9613 164 5998 165 8367 166 5597 167 9837 168 5088 169 7984 170 6030 171 8671 172 4500 173 8500 174 4621 175 7852 176 5291 177 6704 178 4444 179 8081 180 4249 181 6780 182 4659 183 7039 184 3852 185 7127 186 4109 187 6464 188 4447 189 5858 190 3478 191 7064 192 3434 193 5687 194 3991 195 5824 196 3790 197 5834 198 3296 199 5317 200 3731 201 5309 202 2864 203 6281 204 2807 205 4873 206 3514 207 4783 208 3021 209 5299 210 2870 211 4893 212 3087 213 4369 214 2343 215 5117 216 2995 217 4256 218 2978 219 3936 220 2297 221 5044 222 2278 223 4004 224 2602 225 3723 226 2697 227 4255 228 2231 229 3781 230 2482 231 3691 232 1968 233 4237 234 2082 235 3772 236 2683 237 3108 238 2258 239 3869 240 1992 241 3559 242 2123 243 3179 244 1733 245 3282 246 2222 247 2999 248 2187 249 2773 250 1684 251 3557 252 1614 253 2694 254 1812 255 2665 256 1820 257 2984 258 1677 259 2461 260 1762 261 2502 262 1410 263 2789 264 1470 265 2337 266 2008 267 2192 268 1499 269 2454 270 1383 271 2582 272 1466 273 2004 274 1241 275 2539 276 1533 277 1898 278 1525 279 1953 280 1247 281 2440 282 1154 283 2212 284 1276 285 1683 286 1382 287 2166 288 1217 289 1969 290 1384 291 1943 292 1032 293 1986 294 964 295 1757 296 1369 297 1745 298 1010 299 1977 300 963 301 1928 302 970 303 1633 304 924 305 1757 306 1157 307 1545 308 1146 309 1343 310 856 311 1785 312 861 313 1447 314 932 315 1481 316 979 317 1439 318 865 319 1286 320 938 321 1397 322 746 323 1579 324 662 325 1168 326 1103 327 1081 328 729 329 1493 330 720 331 1349 332 814 333 966 334 597 335 1243 336 834 337 1196 338 855 339 1021 340 592 341 1341 342 651 343 1114 344 750 345 1112 346 815 347 1212 348 667 349 914 350 698 351 979 352 546 353 1173 354 590 355 977 356 830 357 852 358 631 359 994 360 640 361 1035 362 593 363 983 364 539 365 860 366 677 367 828 368 689 369 912 370 456 371 1105 372 478 373 788 374 542 375 737 376 594 377 1068 378 502 379 785 380 658 381 857 382 422 383 886 384 470 385 723 386 650 387 678 388 449 389 721 390 525 391 758 392 514 393 703 394 395 395 804 396 468 397 592 398 529 399 603 400 399 401 815 402 420 403 671 404 385 405 552 406 476 407 620 408 335 409 664 410 398 411 694 412 312 413 625 414 293 415 520 416 553 417 571 418 386 419 606 420 299 421 555 422 352 423 500 424 315 425 716 426 376 427 555 428 368 429 523 430 318 431 623 432 309 433 517 434 328 435 458 436 337 437 453 438 273 439 397 440 315 441 540 442 390 443 561 444 270 445 473 446 437 447 435 448 293 449 526 450 233 451 511 452 287 453 425 454 221 455 581 456 296 457 493 458 322 459 392 460 237 461 505 462 215 463 361 464 265 465 360 466 289 467 400 468 256 469 320 470 319 471 384 472 235 473 510 474 208 475 363 476 242 477 314 478 180 479 350 480 187 481 356 482 230 483 427 484 203 485 328 486 275 487 322 488 260 489 358 490 196 491 388 492 165 493 271 494 279 495 230 496 260 497 366 498 169 499 243 500 237
		// 2. symbolic lengths
		//    23: 1 0 2 0 3 0 4 0 5 0 6 0 7 0 8 0 9 5 10 6 11 13 12 22 13 52 14 66 15 214 16 50 17 373 18 281 19 1109 20 96 21 1054 22 281 23 3036 24 138 25 1655 26 261 27 5179 28 146 29 2405 30 167 31 6250 32 139 33 2970 34 104 35 6428 36 88 37 3402 38 98 39 5177 40 95 41 3390 42 56 43 4467 44 103 45 3407 46 64 47 3893 48 57 49 3263 50 52 51 3271 52 73 53 3121 54 38 55 3071 56 47 57 2681 58 35 59 2596 60 33 61 2767 62 64 63 2492 64 37 65 2374 66 41 67 2109 68 21 69 2141 70 12 71 2341 72 14 73 1787 74 21 75 1618 76 15 77 1821 78 12 79 1696 80 11 81 1405 82 8 83 1516 84 10 85 1372 86 16 87 1376 88 14 89 1397 90 9 91 1112 92 9 93 1040 94 10 95 1203 96 17 97 1004 98 10 99 947 100 4 101 1018 102 5 103 807 104 10 105 693 106 9 107 767 108 10 109 662 110 8 111 624 112 4 113 735 114 2 115 557 116 6 117 558 118 2 119 643 120 1 121 546 122 3 123 509 124 4 125 571 126 5 127 397 128 4 129 435 130 1 131 407 132 1 133 357 134 2 135 347 136 5 137 505 138 4 139 296 140 8 141 245 142 5 143 392 144 2 145 269 146 0 147 307 148 1 149 314 150 4 151 222 152 2 153 207 154 0 155 243 156 1 157 295 158 1 159 231 160 4 161 251 162 1 163 180 164 0 165 167 166 4 167 249 168 2 169 142 170 0 171 212 172 0 173 167 174 1 175 156 176 1 177 162 178 0 179 173 180 0 181 122 182 2 183 148 184 0 185 118 186 1 187 141 188 1 189 133 190 1 191 138 192 1 193 103 194 0 195 103 196 0 197 127 198 1 199 98 200 1 201 93 202 1 203 143 204 1 205 90 206 1 207 98 208 1 209 85 210 1 211 73 212 0 213 57 214 0 215 94 216 0 217 88 218 2 219 77 220 3 221 67 222 2 223 54 224 1 225 53 226 0 227 90 228 1 229 49 230 0 231 70 232 0 233 58 234 1 235 71 236 2 237 60 238 0 239 66 240 2 241 39 242 0 243 41 244 1 245 26 246 0 247 56 248 1 249 32 250 0 251 91 252 0 253 42 254 0 255 47 256 0 257 42 258 0 259 40 260 0 261 20 262 0 263 39 264 0 265 17 266 0 267 46 268 0 269 34 270 0 271 31 272 0 273 17 274 0 275 32 276 0 277 26 278 0 279 35 280 0 281 26 282 0 283 35 284 0 285 26 286 0 287 30 288 0 289 12 290 0 291 23 292 0 293 31 294 0 295 10 296 0 297 16 298 0 299 47 300 0 301 13 302 0 303 40 304 0 305 27 306 0 307 20 308 0 309 15 310 0 311 22 312 0 313 13 314 0 315 23 316 0 317 18 318 0 319 11 320 0 321 19 322 0 323 25 324 0 325 10 326 0 327 11 328 0 329 14 330 0 331 27 332 0 333 12 334 1 335 18 336 0 337 12 338 0 339 9 340 0 341 7 342 0 343 6 344 0 345 16 346 0 347 15 348 0 349 7 350 0 351 10 352 0 353 10 354 0 355 18 356 0 357 9 358 0 359 9 360 0 361 8 362 0 363 16 364 0 365 11 366 0 367 16 368 0 369 9 370 0 371 10 372 0 373 7 374 0 375 11 376 0 377 2 378 0 379 9 380 0 381 6 382 0 383 11 384 0 385 5 386 0 387 11 388 0 389 3 390 0 391 5 392 0 393 7 394 0 395 10 396 0 397 6 398 0 399 7 400 0 401 9 402 0 403 6 404 0 405 14 406 0 407 13 408 0 409 6 410 0 411 4 412 0 413 3 414 0 415 2 416 1 417 3 418 0 419 5 420 0 421 6 422 0 423 3 424 0 425 2 426 0 427 4 428 0 429 3 430 0 431 4 432 0 433 4 434 0 435 4 436 0 437 1 438 0 439 2 440 0 441 5 442 0 443 4 444 0 445 3 446 0 447 8 448 0 449 3 450 0 451 3 452 0 453 3 454 0 455 2 456 0 457 4 458 0 459 7 460 0 461 2 462 0 463 1 464 0 465 0 466 0 467 10 468 0 469 3 470 0 471 2 472 0 473 2 474 0 475 8 476 0 477 2 478 0 479 3 480 0 481 1 482 0 483 1 484 0 485 3 486 0 487 2 488 0 489 0 490 0 491 5 492 0 493 2 494 0 495 2 496 0 497 2 498 0 499 2 500 0
		//    25: 1 0 2 0 3 0 4 0 5 1 6 0 7 2 8 3 9 5 10 8 11 31 12 36 13 89 14 66 15 229 16 201 17 741 18 156 19 1058 20 682 21 2875 22 264 23 2750 24 758 25 7804 26 396 27 4442 28 739 29 12846 30 409 31 6278 32 501 33 15642 34 378 35 7671 36 292 37 16095 38 260 39 9232 40 279 41 14163 42 283 43 9513 44 204 45 12026 46 302 47 9594 48 197 49 10590 50 239 51 9480 52 148 53 8823 54 216 55 8836 56 149 57 8078 58 138 59 8937 60 97 61 6664 62 118 63 8091 64 143 65 6921 66 107 67 7996 68 143 69 5645 70 70 71 6886 72 58 73 5725 74 77 75 6770 76 61 77 4782 78 56 79 5617 80 70 81 4445 82 55 83 6034 84 43 85 3882 86 49 87 4585 88 44 89 4058 90 47 91 4616 92 51 93 3082 94 37 95 4284 96 31 97 2958 98 44 99 3634 100 35 101 2908 102 39 103 3182 104 22 105 2251 106 21 107 3542 108 22 109 2054 110 29 111 2537 112 26 113 2203 114 13 115 2295 116 17 117 1774 118 24 119 2601 120 10 121 1573 122 23 123 2089 124 7 125 1757 126 19 127 2087 128 20 129 1317 130 11 131 2045 132 15 133 1227 134 16 135 1610 136 9 137 1331 138 13 139 1466 140 20 141 979 142 19 143 1504 144 10 145 1041 146 12 147 1381 148 7 149 1110 150 7 151 1119 152 11 153 773 154 7 155 1219 156 3 157 800 158 8 159 1052 160 3 161 848 162 10 163 861 164 7 165 597 166 3 167 1171 168 9 169 620 170 5 171 690 172 6 173 719 174 2 175 612 176 6 177 616 178 2 179 785 180 5 181 478 182 5 183 596 184 3 185 565 186 2 187 719 188 4 189 396 190 1 191 612 192 4 193 422 194 3 195 474 196 0 197 464 198 2 199 442 200 1 201 340 202 1 203 531 204 2 205 374 206 4 207 470 208 3 209 335 210 3 211 322 212 7 213 280 214 3 215 402 216 2 217 301 218 3 219 422 220 5 221 310 222 7 223 246 224 3 225 220 226 2 227 404 228 2 229 234 230 1 231 248 232 3 233 248 234 1 235 234 236 1 237 266 238 2 239 271 240 0 241 174 242 4 243 214 244 2 245 201 246 1 247 218 248 0 249 170 250 1 251 334 252 1 253 212 254 0 255 177 256 0 257 245 258 3 259 162 260 0 261 123 262 1 263 171 264 0 265 122 266 0 267 179 268 1 269 140 270 0 271 140 272 0 273 107 274 0 275 145 276 0 277 175 278 0 279 136 280 0 281 125 282 0 283 156 284 0 285 133 286 0 287 164 288 1 289 104 290 0 291 98 292 0 293 103 294 1 295 114 296 0 297 103 298 0 299 106 300 1 301 96 302 1 303 99 304 0 305 113 306 0 307 101 308 1 309 89 310 1 311 86 312 0 313 66 314 1 315 107 316 0 317 86 318 0 319 83 320 1 321 82 322 0 323 98 324 0 325 74 326 0 327 90 328 0 329 93 330 0 331 67 332 0 333 77 334 2 335 63 336 1 337 73 338 0 339 47 340 0 341 65 342 0 343 54 344 0 345 37 346 0 347 118 348 0 349 45 350 0 351 44 352 0 353 43 354 0 355 53 356 0 357 60 358 0 359 75 360 0 361 30 362 2 363 67 364 0 365 52 366 0 367 56 368 0 369 48 370 0 371 39 372 0 373 39 374 0 375 38 376 0 377 53 378 1 379 34 380 1 381 60 382 0 383 38 384 1 385 27 386 0 387 41 388 1 389 45 390 0 391 26 392 1 393 27 394 0 395 49 396 0 397 34 398 0 399 31 400 0 401 27 402 0 403 29 404 0 405 50 406 0 407 47 408 0 409 36 410 0 411 34 412 0 413 24 414 0 415 21 416 1 417 35 418 1 419 30 420 0 421 24 422 0 423 19 424 0 425 25 426 0 427 30 428 0 429 16 430 0 431 19 432 0 433 31 434 0 435 22 436 0 437 22 438 0 439 13 440 0 441 16 442 0 443 29 444 0 445 13 446 0 447 28 448 0 449 23 450 0 451 22 452 0 453 15 454 0 455 16 456 0 457 20 458 0 459 39 460 0 461 18 462 0 463 16 464 0 465 10 466 0 467 11 468 0 469 22 470 0 471 16 472 0 473 12 474 0 475 20 476 0 477 25 478 0 479 16 480 0 481 9 482 0 483 15 484 0 485 24 486 0 487 19 488 0 489 35 490 0 491 21 492 0 493 19 494 0 495 11 496 0 497 10 498 0 499 11 500 0
		//    27: 1 0 2 0 3 0 4 0 5 0 6 0 7 3 8 2 9 7 10 18 11 20 12 37 13 113 14 110 15 324 16 179 17 710 18 593 19 2091 20 408 21 3012 22 1767 23 8037 24 738 25 7160 26 1981 27 19712 28 1011 29 11548 30 1902 31 31828 32 1087 33 16454 34 1382 35 39970 36 1029 37 20778 38 988 39 41654 40 790 41 24153 42 845 43 37639 44 852 45 25390 46 670 47 33141 48 799 49 24974 50 572 51 29299 52 691 53 25553 54 498 55 26270 56 664 57 23011 58 424 59 23667 60 442 61 23752 62 474 63 22236 64 378 65 21354 66 447 67 20078 68 382 69 20858 70 405 71 21073 72 266 73 17854 74 304 75 17487 76 201 77 18105 78 251 79 17888 80 250 81 14601 82 187 83 15834 84 175 85 14665 86 217 87 15212 88 147 89 13781 90 155 91 12819 92 178 93 11950 94 133 95 13650 96 116 97 10746 98 150 99 11040 100 114 101 11323 102 119 103 10644 104 119 105 8663 106 81 107 9869 108 81 109 8327 110 119 111 8362 112 117 113 8849 114 78 115 7587 116 68 117 6664 118 68 119 8351 120 74 121 6513 122 70 123 6683 124 58 125 7135 126 58 127 5896 128 72 129 5619 130 53 131 6212 132 64 133 5106 134 69 135 5039 136 42 137 6145 138 53 139 4779 140 70 141 4051 142 70 143 5172 144 59 145 3793 146 48 147 4313 148 35 149 4496 150 23 151 3589 152 59 153 3352 154 30 155 3914 156 23 157 3691 158 30 159 3349 160 22 161 3588 162 36 163 2985 164 40 165 2647 166 32 167 3446 168 16 169 2710 170 27 171 2918 172 27 173 2658 174 16 175 2506 176 12 177 2603 178 19 179 2843 180 15 181 1997 182 26 183 2295 184 13 185 2135 186 19 187 2307 188 12 189 1869 190 14 191 2457 192 13 193 1734 194 21 195 1893 196 13 197 2235 198 14 199 1622 200 12 201 1389 202 16 203 2179 204 14 205 1424 206 13 207 1757 208 12 209 1596 210 16 211 1290 212 16 213 1054 214 18 215 1718 216 14 217 1454 218 6 219 1437 220 9 221 1363 222 16 223 1229 224 15 225 901 226 10 227 1432 228 11 229 997 230 13 231 1094 232 8 233 1039 234 10 235 1238 236 4 237 1058 238 12 239 1266 240 13 241 819 242 10 243 1007 244 14 245 801 246 9 247 928 248 8 249 670 250 4 251 1115 252 8 253 776 254 8 255 911 256 3 257 893 258 2 259 779 260 7 261 566 262 5 263 832 264 3 265 517 266 3 267 1039 268 2 269 675 270 3 271 605 272 5 273 499 274 2 275 731 276 1 277 588 278 2 279 648 280 1 281 484 282 4 283 636 284 2 285 451 286 2 287 711 288 2 289 424 290 4 291 466 292 4 293 466 294 3 295 427 296 1 297 432 298 1 299 689 300 2 301 296 302 3 303 532 304 2 305 432 306 2 307 515 308 1 309 355 310 4 311 492 312 5 313 286 314 1 315 450 316 5 317 452 318 1 319 319 320 1 321 298 322 1 323 428 324 1 325 300 326 2 327 374 328 0 329 276 330 2 331 484 332 2 333 251 334 0 335 353 336 5 337 293 338 4 339 329 340 1 341 275 342 2 343 245 344 1 345 198 346 2 347 378 348 1 349 263 350 4 351 227 352 0 353 190 354 1 355 319 356 2 357 260 358 3 359 275 360 2 361 169 362 2 363 297 364 2 365 213 366 1 367 252 368 0 369 173 370 1 371 234 372 1 373 150 374 1 375 202 376 0 377 216 378 0 379 225 380 1 381 139 382 1 383 242 384 1 385 137 386 1 387 242 388 0 389 151 390 1 391 180 392 1 393 107 394 3 395 242 396 0 397 182 398 0 399 145 400 0 401 144 402 0 403 135 404 0 405 133 406 0 407 318 408 0 409 144 410 0 411 195 412 0 413 140 414 0 415 153 416 0 417 133 418 1 419 143 420 3 421 92 422 4 423 115 424 0 425 102 426 0 427 178 428 2 429 84 430 0 431 128 432 0 433 109 434 0 435 103 436 1 437 126 438 0 439 88 440 0 441 60 442 0 443 163 444 0 445 77 446 0 447 155 448 0 449 101 450 0 451 109 452 1 453 84 454 0 455 96 456 0 457 86 458 0 459 168 460 0 461 98 462 0 463 68 464 0 465 65 466 2 467 111 468 0 469 62 470 0 471 98 472 0 473 61 474 1 475 122 476 1 477 104 478 1 479 104 480 0 481 50 482 0 483 59 484 0 485 80 486 0 487 92 488 0 489 60 490 0 491 124 492 1 493 60 494 1 495 73 496 0 497 55 498 0 499 68 500 1
		//    29: 1 0 2 0 3 0 4 0 5 0 6 0 7 1 8 2 9 10 10 10 11 28 12 57 13 97 14 128 15 385 16 392 17 1164 18 566 19 2315 20 1766 21 6486 22 1214 23 8459 24 4381 25 21387 26 2040 27 18980 28 5201 29 50571 30 2735 31 31262 32 5198 33 80942 34 3069 35 44169 36 4048 37 102450 38 2949 39 55475 40 2875 41 108273 42 2350 43 64446 44 2460 45 100277 46 2416 47 69647 48 1883 49 91413 50 2417 51 70478 52 1692 53 79598 54 2016 55 70998 56 1559 57 72249 58 1957 59 69450 60 1341 61 62577 62 1547 63 67034 64 1304 65 60526 66 1316 67 67274 68 1421 69 52688 70 1129 71 61364 72 1082 73 54022 74 1092 75 61277 76 876 77 47537 78 682 79 53937 80 926 81 45608 82 807 83 55760 84 634 85 40160 86 745 87 46385 88 627 89 42130 90 526 91 47809 92 686 93 34283 94 541 95 43754 96 459 97 34142 98 591 99 39937 100 418 101 32866 102 507 103 35080 104 491 105 28198 106 385 107 37840 108 299 109 25463 110 399 111 29989 112 322 113 26498 114 356 115 27966 116 332 117 21336 118 293 119 29567 120 239 121 20321 122 373 123 24178 124 200 125 21542 126 258 127 23844 128 240 129 17445 130 229 131 24586 132 226 133 16268 134 287 135 19868 136 173 137 17228 138 180 139 18223 140 209 141 13367 142 249 143 19645 144 174 145 13497 146 223 147 16086 148 126 149 14599 150 167 151 15003 152 147 153 10984 154 141 155 16021 156 108 157 10706 158 146 159 13680 160 99 161 11771 162 145 163 11601 164 117 165 8866 166 115 167 14287 168 103 169 8970 170 117 171 10442 172 91 173 10320 174 113 175 9410 176 86 177 8134 178 64 179 11146 180 72 181 7417 182 116 183 9026 184 74 185 8067 186 66 187 9428 188 87 189 6642 190 50 191 8703 192 70 193 6615 194 68 195 7083 196 53 197 7261 198 61 199 7124 200 61 201 5210 202 56 203 7662 204 52 205 5527 206 60 207 7431 208 45 209 6056 210 42 211 5146 212 96 213 4420 214 44 215 6081 216 62 217 4987 218 57 219 5833 220 40 221 4945 222 53 223 4761 224 58 225 3800 226 50 227 6014 228 44 229 3734 230 46 231 4435 232 54 233 4158 234 30 235 3891 236 40 237 4077 238 33 239 4622 240 27 241 3310 242 42 243 3626 244 32 245 3587 246 45 247 3814 248 32 249 2880 250 34 251 4658 252 32 253 3077 254 27 255 3378 256 15 257 3934 258 28 259 2961 260 25 261 2373 262 31 263 3300 264 35 265 2213 266 21 267 3105 268 16 269 2925 270 16 271 2369 272 22 273 2084 274 9 275 2768 276 13 277 2646 278 12 279 2454 280 11 281 2302 282 6 283 2684 284 13 285 2020 286 10 287 3023 288 10 289 2026 290 14 291 2041 292 16 293 2090 294 13 295 1860 296 9 297 1839 298 12 299 2255 300 13 301 1651 302 20 303 1859 304 10 305 1964 306 9 307 1826 308 10 309 1648 310 8 311 1872 312 16 313 1424 314 14 315 1980 316 14 317 1798 318 19 319 1554 320 13 321 1300 322 15 323 1758 324 9 325 1164 326 8 327 1669 328 9 329 1627 330 3 331 1451 332 16 333 1365 334 5 335 1421 336 10 337 1450 338 14 339 1177 340 10 341 1293 342 12 343 1075 344 9 345 887 346 7 347 1813 348 5 349 1047 350 6 351 1150 352 7 353 955 354 7 355 986 356 4 357 1184 358 3 359 1347 360 6 361 857 362 6 363 1166 364 5 365 976 366 14 367 1026 368 12 369 824 370 1 371 960 372 3 373 810 374 8 375 881 376 2 377 1026 378 3 379 1000 380 2 381 967 382 6 383 953 384 12 385 757 386 7 387 888 388 6 389 833 390 8 391 697 392 6 393 679 394 5 395 1019 396 7 397 746 398 6 399 714 400 4 401 704 402 3 403 604 404 3 405 598 406 3 407 927 408 4 409 699 410 4 411 788 412 2 413 727 414 3 415 626 416 2 417 633 418 3 419 644 420 8 421 495 422 7 423 563 424 5 425 534 426 6 427 699 428 3 429 476 430 4 431 578 432 1 433 696 434 7 435 466 436 4 437 597 438 3 439 487 440 4 441 340 442 4 443 602 444 1 445 411 446 3 447 625 448 1 449 511 450 0 451 434 452 4 453 387 454 1 455 482 456 2 457 451 458 2 459 567 460 1 461 446 462 2 463 398 464 0 465 314 466 1 467 492 468 6 469 317 470 2 471 383 472 2 473 391 474 1 475 407 476 1 477 429 478 4 479 411 480 2 481 298 482 2 483 295 484 2 485 477 486 1 487 383 488 0 489 369 490 1 491 474 492 1 493 364 494 1 495 314 496 3 497 375 498 2 499 236 500 0
	}
}

void DlProofEnumerator::_findProvenFormulas(tbb::concurrent_unordered_map<string, string>& representativeProofs, uint32_t wordLengthLimit, DlProofEnumeratorMode mode, ProgressData* const progressData, uint64_t* optOut_counter, uint64_t* optOut_conclusionCounter, uint64_t* optOut_redundantCounter, uint64_t* optOut_invalidCounter, const vector<uint32_t>* genIn_stack, const uint32_t* genIn_n, const vector<vector<string>>* genIn_allRepresentativesLookup) {
	atomic<uint64_t> counter { 0 };
	atomic<uint64_t> conclusionCounter { 0 };
	atomic<uint64_t> redundantCounter { 0 };
	atomic<uint64_t> invalidCounter { 0 };
	auto process = [&representativeProofs, &progressData, &counter, &conclusionCounter, &redundantCounter, &invalidCounter](string& sequence) {
		counter++;
		vector<pair<string, tuple<vector<shared_ptr<DlFormula>>, vector<string>, map<size_t, vector<unsigned>>>>> rawParseData;
		if (!(rawParseData = DRuleParser::parseDProof_raw_permissive(sequence)).empty()) {
			const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
			pair<tbb::concurrent_unordered_map<string, string>::iterator, bool> emplaceResult = representativeProofs.emplace(DlCore::toPolishNotation_noRename(conclusion), sequence);
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
		if (progressData && progressData->nextStep()) {
			uint64_t percentage;
			string progress;
			string etc;
			if (progressData->nextState(percentage, progress, etc))
				cout << myTime() << ": Iterated " << (progressData->maximumEstimated ? "≈" : "") << (percentage < 10 ? " " : "") << percentage << "% of D-proof candidates. [" << progress << "] (" << etc << ")" << endl;
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

void DlProofEnumerator::_removeRedundantConclusionsForProofsOfMaxLength(const uint32_t maxLength, tbb::concurrent_unordered_map<string, string>& representativeProofs, ProgressData* const progressData, uint64_t& conclusionCounter, uint64_t& redundantCounter) {
	//#chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>> formulasByStandardLength;
	tbb::parallel_for(representativeProofs.range(), [&formulasByStandardLength](tbb::concurrent_unordered_map<string, string>::range_type& range) {
		for (tbb::concurrent_unordered_map<string, string>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& formula = it->first;
			formulasByStandardLength[DlCore::standardLen_polishNotation_noRename_numVars(formula)].push_back(&formula);
		}
	});
	//#cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken to create " << formulasByStandardLength.size() << " classes of formulas by their standard length." << endl;
	//#cout << [](tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>>& m) { stringstream ss; for (const pair<const size_t, tbb::concurrent_vector<const string*>>& p : m) { ss << p.first << ":" << p.second.size() << ", "; } return ss.str(); }(formulasByStandardLength) << endl;
	tbb::concurrent_unordered_map<const string*, tbb::concurrent_unordered_map<string, string>::const_iterator> toErase;
	if (progressData)
		progressData->setStartTime();
	tbb::parallel_for(representativeProofs.range(), [&maxLength, &progressData, &formulasByStandardLength, &toErase](tbb::concurrent_unordered_map<string, string>::range_type& range) {
		for (tbb::concurrent_unordered_map<string, string>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string::size_type dProofLen = it->second.length();
			if (dProofLen == maxLength) {
				const string& formula = it->first;
				atomic<bool> redundant { false };
				size_t formulaLen = DlCore::standardLen_polishNotation_noRename_numVars(formula);
				tbb::parallel_for(formulasByStandardLength.range(), [&formulaLen, &redundant, &formula](tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>>::range_type& range) {
					for (tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>>::const_iterator it = range.begin(); it != range.end(); ++it)
						if (redundant)
							return;
						else if (it->first <= formulaLen)
							for (const string* const potentialSchema : it->second)
								if (formula != *potentialSchema && DlCore::isSchemaOf_polishNotation_noRename_numVars(*potentialSchema, formula)) { // formula redundant
									redundant = true;
									return;
								}
				});
				if (redundant) {
					toErase.emplace(&it->first, it);

					// Show progress if requested
					if (progressData && progressData->nextStep()) {
						uint64_t percentage;
						string progress;
						string etc;
						if (progressData->nextState(percentage, progress, etc))
							cout << myTime() << ": Removed " << (progressData->maximumEstimated ? "≈" : "") << (percentage < 10 ? " " : "") << percentage << "% of redundant conclusions. [" << progress << "] (" << etc << ")" << endl;
					}
				}
			}
		}
	});
	conclusionCounter -= toErase.size();
	redundantCounter += toErase.size();
	//#cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken for data iteration." << endl;
	//#startTime = chrono::steady_clock::now();
	for (const pair<const string* const, tbb::concurrent_unordered_map<string, string>::const_iterator>& p : toErase)
		representativeProofs.unsafe_erase(p.second);
	//#cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) << " ms taken for erasure of " << toErase.size() << " elements." << endl;
}

tbb::concurrent_unordered_set<uint64_t> DlProofEnumerator::_mpi_findRedundantConclusionsForProofsOfMaxLength(int mpi_rank, int mpi_size, const uint32_t maxLength, tbb::concurrent_unordered_map<string, string>& representativeProofs, const vector<string>& recentConclusionSequence, helper::ProgressData* const progressData, bool smoothProgress) {
	bool isMainProc = mpi_rank == 0;
	size_t n = recentConclusionSequence.size();

	// Reorders indices according to affine ciphered values (https://en.wikipedia.org/wiki/Affine_cipher),
	// using a factor with good spectral results (https://en.wikipedia.org/wiki/Spectral_test).
	auto distributeIndices = [](uint64_t size) -> vector<uint64_t> {
		// NOTE: 0x9e3779b97f4a7c15 = 0b1001111000110111011110011011100101111111010010100111110000010101 = 11400714819323198485 = 5*139*199*82431689521877
		//       is coprime with 2^64 (as required for 64-bit affine cipher), and has well-distributed bits ; 2^64 / golden ratio = 1.14007148193231984859...
		auto ac = [](uint64_t x) -> uint64_t { return 0x9e3779b97f4a7c15uLL * x + 1; };
		auto cmp_ac = [&ac](uint64_t a, uint64_t b) -> bool { return ac(a) < ac(b); };
		vector<uint64_t> v(size);
		tbb::parallel_for(uint64_t(0), size, [&v](uint64_t i) { v[i] = i; });
		tbb::parallel_sort(v.begin(), v.end(), cmp_ac);
		return v;
	};
	//#chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	const vector<uint64_t> indexDistribution = smoothProgress ? distributeIndices(n) : vector<uint64_t> { };
	//#if (smoothProgress) cout << "[Rank " + to_string(mpi_rank) + "] " + FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) + " ms taken to prepare index distribution of size " + to_string(n) + "." << endl;
	// e.g. (..., 27, 29, 31): (..., 18.83, 55.38, 166.21) ms taken to prepare index distribution of size (6649, 19416, 56321, 165223, 490604, 1459555, 4375266, 13194193).

	// To register what workload is reservable, and / or to assign a new workload.
	auto split = [](size_t first, size_t end, array<uint64_t, 2>* reg, array<uint64_t, 2>* load) {
		// NOTE: The balancing strategy involves to request reservable workloads from other processes when the own workload is complete, and to grant reservable workloads to others whenever they request them.
		//       Reservable workloads are set to 1/d parts of the available owned index range, for d := 'reserveDenominator', but they are omitted when smaller than m := 'minWorkloadSize'.
		//       For instance, when process P requests indices from process Q, and the reservable range is [a, b), P sends a pair { a, b } to Q, and Q responds with a boolean whether the request is granted.
		//       If it is granted, P now reduces its reservable range from [a, b) to [b-floor((b-a)/d), b), except when floor((b-a)/d) < m, in which case it is reduced to empty.
		//       Q also updates knowledge about P's reservable range by doing the same calculation, and starts working on [a, b-floor((b-a)/d)) or [a, b), respectively.
		//       Note that P, due to Q's request, also updates knowledge about Q's reservable range, which is thereby empty.
		//       Whenever a process completes its own index range, it requests to update reservable ranges from all other processes that according to its own list, may still have non-empty reservable ranges.
		//       Then, after receiving all responses and updating its own list, it starts with requesting the biggest reservable range. Upon rejection, it updates the requested range as if it was requested
		//       once in the meantime, then again requests the biggest reservable range. This is repeated until a request is approved, or all reservable ranges are known to be empty.
		//       Since for each process, communication is only performed by the main thread, all kinds of requests and responses are asynchronous and looped.
		uint64_t minWorkloadSize = 400;
		uint64_t reserveDenominator = 3;
		size_t size = end - first;
		size_t reservableSize = size / reserveDenominator;
		if (reservableSize < minWorkloadSize) { // no splitting
			if (load) {
				(*load)[0] = first;
				(*load)[1] = end;
			}
			if (reg) {
				(*reg)[0] = UINT64_MAX; // no reservable workload
				(*reg)[1] = 0;
			}
		} else { // splitting
			size_t workloadSize = size - reservableSize;
			if (load) {
				(*load)[0] = first;
				(*load)[1] = first + workloadSize;
			}
			if (reg) {
				(*reg)[0] = first + workloadSize;
				(*reg)[1] = end;
			}
		}
	};
	array<uint64_t, 2> workload;
	vector<array<uint64_t, 2>> reservableWorkloads(mpi_size);
	mutex mtx_reservations;
	atomic<bool> checkRequests { false };
	atomic<bool> loading { false };
	//#MPI_Barrier(MPI_COMM_WORLD);
	for (int rank = 0; rank < mpi_size; rank++) {
		size_t first = rank * n / mpi_size;
		size_t end = rank + 1 == mpi_size ? n : (rank + 1) * n / mpi_size; // first index that is not contained
		split(first, end, &reservableWorkloads[rank], rank == mpi_rank ? &workload : nullptr); // initialize 'workload' and 'reservableWorkloads'
		//#if (rank == mpi_rank) cout << "[Rank " + to_string(mpi_rank) + ", n = " + to_string(n) + "] Interval: [" + to_string(first) + ", " + (end ? to_string(end - 1) : "-1") + "] (size " + to_string(end - first) + ")" << endl;
	}
	//#cout << "[Rank " + to_string(mpi_rank) + ", n = " + to_string(n) + "] Workload: [" + to_string(workload[0]) + ", " + (workload[1] ? to_string(workload[1] - 1) : "-1") + "]" << endl;
	if (isMainProc) {
		int r = 0;
		cout << "Reservable workloads: " + FctHelper::vectorStringF(reservableWorkloads, [&](const array<uint64_t, 2>& a) { return to_string(r++) + ":[" + to_string(a[0]) + ", " + (a[1] ? to_string(a[1] - 1) : "-1") + "]"; }, "{ ", " }") << endl;
	}
	//#startTime = chrono::steady_clock::now();
	tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>> formulasByStandardLength;
	tbb::parallel_for(representativeProofs.range(), [&formulasByStandardLength](tbb::concurrent_unordered_map<string, string>::range_type& range) {
		for (tbb::concurrent_unordered_map<string, string>::const_iterator it = range.begin(); it != range.end(); ++it) {
			const string& formula = it->first;
			formulasByStandardLength[DlCore::standardLen_polishNotation_noRename_numVars(formula)].push_back(&formula);
		}
	});
	//#if (isMainProc) cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) + " ms taken to create " + to_string(formulasByStandardLength.size()) + " classes of formulas by their standard length." << endl;
	//#if (isMainProc) cout << [](tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>>& m) { stringstream ss; for (const pair<const size_t, tbb::concurrent_vector<const string*>>& p : m) { ss << p.first << ":" << p.second.size() << ", "; } return ss.str(); }(formulasByStandardLength) << endl;
	tbb::concurrent_queue<uint64_t> toErase;
	tbb::concurrent_unordered_set<uint64_t> toErase_mainProc;
	mutex mtx;
	unique_lock<mutex> condLock(mtx);
	condition_variable cond;
	atomic<bool> communicate { true };
	atomic<bool> waitTermination { false };
	atomic<bool> workerDone { false };
	atomic<uint64_t> localCounter { 0 };
	if (progressData)
		progressData->setStartTime();
	auto worker = [&recentConclusionSequence, &indexDistribution, &split](int mpi_rank, array<uint64_t, 2>& workload, vector<array<uint64_t, 2>>& reservableWorkloads, mutex& mtx_reservations, atomic<bool>& checkRequests, atomic<bool>& loading, size_t n, bool smoothProgress, bool isMainProc, atomic<uint64_t>& localCounter, condition_variable& cond, atomic<bool>& communicate, atomic<bool>& workerDone, tbb::concurrent_queue<uint64_t>& toErase, tbb::concurrent_unordered_set<uint64_t>& toErase_mainProc, tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>>& formulasByStandardLength, helper::ProgressData* const progressData) {
		// The main thread also reads and writes 'workload' and 'reservableWorkloads', which thereby require locks.
		// When 'workload' is modified by the main thread, the worker requested more work and is looping in 'loading' state, so reading it here is fine.
		uint64_t first = workload[0];
		uint64_t end = workload[1];
		auto moreWork = [&](uint64_t& first, uint64_t& end) -> bool {
			//#cout << "[Rank " + to_string(mpi_rank) + "] Completed workload [" + to_string(workload[0]) + ", " + (workload[1] ? to_string(workload[1] - 1) : "-1") + "]." << endl;
			{
				unique_lock<mutex> lock(mtx_reservations);
				array<uint64_t, 2>& owned = reservableWorkloads[mpi_rank];
				if (owned[0] == UINT64_MAX) {
					loading = true; // tell the main thread that the worker requires updating
					//#cout << "[Rank " + to_string(mpi_rank) + "] Workload complete. Requesting more from other processes." << endl;
					//#chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
					lock.unlock();

					// Tell the main thread to check requests immediately.
					checkRequests = true;
					if (!isMainProc)
						cond.notify_one();

					// Wait for update.
					while (loading && communicate) // no request will be answered when communication is already disabled, so need to check that as well
						this_thread::yield();
					lock.lock(); // the update was performed or unnecessary
					//#cout << "[Rank " + to_string(mpi_rank) + "] " + FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) + " ms taken to gather and request workloads from other process." << endl;

					// NOTE: Current workload was updated by the main thread.
					if (workload[0] == UINT64_MAX || !communicate)
						return false; // still nothing to do => the worker is done
				} else
					split(owned[0], owned[1], &owned, &workload); // update current workload and owned reservable workload
				first = workload[0];
				end = workload[1];
			}
			return true;
		};
		do
			tbb::parallel_for(first, end, [&recentConclusionSequence, &indexDistribution, &smoothProgress, &isMainProc, &localCounter, &cond, &progressData, &formulasByStandardLength, &toErase, &toErase_mainProc](size_t i) {
				uint64_t index = smoothProgress ? indexDistribution[i] : i;
				const string& formula = recentConclusionSequence[index];
				atomic<bool> redundant { false };
				size_t formulaLen = DlCore::standardLen_polishNotation_noRename_numVars(formula);
				tbb::parallel_for(formulasByStandardLength.range(), [&formulaLen, &redundant, &formula](tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>>::range_type& range) {
					for (tbb::concurrent_map<size_t, tbb::concurrent_vector<const string*>>::const_iterator it = range.begin(); it != range.end(); ++it)
						if (redundant)
							return;
						else if (it->first <= formulaLen)
							for (const string* const potentialSchema : it->second)
								if (formula != *potentialSchema && DlCore::isSchemaOf_polishNotation_noRename_numVars(*potentialSchema, formula)) { // formula redundant
									redundant = true;
									return;
								}
				});
				if (redundant) {
					localCounter++;
					if (isMainProc)
						toErase_mainProc.insert(index);
					else {
						toErase.push(index);
						cond.notify_one();
					}

					// Show progress if requested ; NOTE: Shouldn't be requested for non-main processes.
					if (progressData && progressData->nextStep()) {
						uint64_t percentage;
						string progress;
						string etc;
						if (progressData->nextState(percentage, progress, etc))
							cout << myTime() + ": Removed " + (progressData->maximumEstimated ? "≈" : "") + (percentage < 10 ? " " : "") + to_string(percentage) + "% of redundant conclusions. [" + progress + "] (" + etc + ")" << endl;
					}
				} else if (!isMainProc && !toErase.empty())
					cond.notify_one();
			});
		while (moreWork(first, end));
		workerDone = true;
		//#cout << "[Rank " + to_string(mpi_rank) + "] Worker complete." << endl;
	};
	thread workerThread(worker, mpi_rank, ref(workload), ref(reservableWorkloads), ref(mtx_reservations), ref(checkRequests), ref(loading), n, smoothProgress, isMainProc, ref(localCounter), ref(cond), ref(communicate), ref(workerDone), ref(toErase), ref(toErase_mainProc), ref(formulasByStandardLength), progressData);
	auto queryTimer = [](bool isMainProc, condition_variable& cond, atomic<bool>& communicate, atomic<bool>& checkRequests) {
		// Only the main thread should make MPI queries. When not on the main process, the main thread has to be notified whenever communication
		//  should happen. Each main thread should check for incoming balancing requests from other processes up to 20 times a second.
		while (communicate) {
			this_thread::sleep_for(chrono::milliseconds(50));
			checkRequests = true;
			if (!isMainProc)
				cond.notify_one();
		}
	};
	thread timerThread(queryTimer, isMainProc, ref(cond), ref(communicate), ref(checkRequests));
	constexpr int mpi_tag_request_reservable = 0;
	constexpr int mpi_tag_respond_reservable = 1;
	constexpr int mpi_tag_attempt_reservation = 2;
	constexpr int mpi_tag_respond_reservation = 3;
	constexpr int mpi_tag_terminate = 4;
	auto handleBalancingRequests = [&]() {
		// NOTE: It might be preferable to use collective operations, but they require all members of the communicator to participate, thus
		//       cannot be probed for. But apart from merely listening, gathering operations should rarely occur. Consequently, without
		//       global synchronization and periodical network transactions, we are bound to using MPI_Send and MPI_Recv (with MPI_Iprobe).
		checkRequests = false;
		if (unique_lock<mutex> lock = unique_lock<mutex>(mtx_reservations, try_to_lock)) {
			array<uint64_t, 2>& owned = reservableWorkloads[mpi_rank];
			bool needToRequest = loading;
			set<int> pendingSources;
			int requestedSource = -1;
			array<uint64_t, 2> requestingWorkload;
			do {
				bool sink;
				if (waitTermination && FctHelper::mpi_tryRecvBool(mpi_rank, 0, sink, FctHelper::mpi_tag_custom + mpi_tag_terminate)) {
					//#cout << "[Rank " + to_string(mpi_rank) + "] WHO'S \"THE FUCK\"?" << endl;
					communicate = false; // the main process is shutting down communication for all processes => the task is complete
					return;
				}

				// NOTE: Communication strategy explained in the 'split' lambda function above.

				// 1. Answer any requests from other processes.
				{
					// 1.1 Requests to gain ownership of the reservable workload of this process
					array<uint64_t, 2> requestedWorkload;
					MPI_Status status;
					while (FctHelper::mpi_tryRecvPairUint64(mpi_rank, MPI_ANY_SOURCE, requestedWorkload, FctHelper::mpi_tag_custom + mpi_tag_attempt_reservation, &status)) {
						if (requestedWorkload == owned) {
							FctHelper::mpi_sendBool(mpi_rank, true, status.MPI_SOURCE, FctHelper::mpi_tag_custom + mpi_tag_respond_reservation); // transfer workload
							split(owned[0], owned[1], &owned, nullptr); // update owned reservable workload
						} else
							FctHelper::mpi_sendBool(mpi_rank, false, status.MPI_SOURCE, FctHelper::mpi_tag_custom + mpi_tag_respond_reservation);

						// Update reservable workload that is owned by the requesting process to empty.
						array<uint64_t, 2>& reservableInfo = reservableWorkloads[status.MPI_SOURCE];
						reservableInfo[0] = UINT64_MAX;
						reservableInfo[1] = 0;
					}
				}
				{
					// 1.2 Requests of what is reservable
					MPI_Status status;
					while (FctHelper::mpi_tryRecvBool(mpi_rank, MPI_ANY_SOURCE, sink, FctHelper::mpi_tag_custom + mpi_tag_request_reservable, &status)) {
						FctHelper::mpi_sendPairUint64(mpi_rank, owned, status.MPI_SOURCE, FctHelper::mpi_tag_custom + mpi_tag_respond_reservable);

						// Update reservable workload that is owned by the requesting process to empty.
						array<uint64_t, 2>& reservableInfo = reservableWorkloads[status.MPI_SOURCE];
						reservableInfo[0] = UINT64_MAX;
						reservableInfo[1] = 0;
					}
				}

				// 2. Gather workloads from other processes and request reservation when required.
				if (loading) {
					if (needToRequest) {
						// 2.1 Request workloads from other processes
						for (int source = 0; source < mpi_size; source++)
							if (source != mpi_rank && reservableWorkloads[source][0] != UINT64_MAX) {
								FctHelper::mpi_sendBool(mpi_rank, true, source, FctHelper::mpi_tag_custom + mpi_tag_request_reservable);
								pendingSources.insert(source);
							}
						needToRequest = false;
						//#int r = 0; cout << "[Rank " + to_string(mpi_rank) + "] Requested workloads from ranks " + FctHelper::setString(pendingSources) + ". Old reservable workloads: " + FctHelper::vectorStringF(reservableWorkloads, [&](const array<uint64_t, 2>& a) { return to_string(r++) + ":[" + to_string(a[0]) + ", " + (a[1] ? to_string(a[1] - 1) : "-1") + "]"; }, "{ ", " }") + "." << endl;
						if (pendingSources.empty()) { // all other processes are done as well
							workload[0] = UINT64_MAX; // signal to the worker, that there is nothing left to do
							loading = false; // the worker thread may now continue
						}
					} else if (!pendingSources.empty()) {

						// 2.2 Gather responses from other processes
						array<uint64_t, 2> requestedWorkload;
						MPI_Status status;
						while (FctHelper::mpi_tryRecvPairUint64(mpi_rank, MPI_ANY_SOURCE, requestedWorkload, FctHelper::mpi_tag_custom + mpi_tag_respond_reservable, &status)) {
							pendingSources.erase(status.MPI_SOURCE);
							reservableWorkloads[status.MPI_SOURCE] = requestedWorkload; // update reservable workload that is owned by the requested process
						}
					} else if (requestedSource == -1) { // gathering completed, need a reservation request
						//#int r = 0; cout << "[Rank " + to_string(mpi_rank) + "] Reservable workloads updated to " + FctHelper::vectorStringF(reservableWorkloads, [&](const array<uint64_t, 2>& a) { return to_string(r++) + ":[" + to_string(a[0]) + ", " + (a[1] ? to_string(a[1] - 1) : "-1") + "]"; }, "{ ", " }") + "." << endl;

						// 2.3 Attempt to reserve the biggest workload from all other processes
						int bestSource = -1;
						uint64_t maxSize = 0;
						for (int source = 0; source < mpi_size; source++) {
							array<uint64_t, 2>& reservableInfo = reservableWorkloads[source];
							if (source != mpi_rank && reservableInfo[0] != UINT64_MAX) {
								uint64_t size = reservableInfo[1] - reservableInfo[0];
								if (size > maxSize) {
									bestSource = source;
									maxSize = size;
								}
							}
						}
						if (maxSize) { // found something to reserve
							requestedSource = bestSource;
							requestingWorkload = reservableWorkloads[requestedSource];
							FctHelper::mpi_sendPairUint64(mpi_rank, requestingWorkload, requestedSource, FctHelper::mpi_tag_custom + mpi_tag_attempt_reservation); // request to transfer workload
						} else { // all other processes are done as well
							workload[0] = UINT64_MAX; // signal to the worker, that there is nothing left to do
							loading = false; // the worker thread may now continue
						}
					} else {

						// 2.4 Handle rejection or approval of reservation request
						bool approved;
						if (FctHelper::mpi_tryRecvBool(mpi_rank, requestedSource, approved, FctHelper::mpi_tag_custom + mpi_tag_respond_reservation)) {
							//#cout << "[Rank " + to_string(mpi_rank) + "] Request for [" + to_string(requestingWorkload[0]) + ", " + (requestingWorkload[1] ? to_string(requestingWorkload[1] - 1) : "-1") + "] handled by rank " + to_string(requestedSource) + "." << endl;

							// 2.4.1 Extract actual workload from requested slot
							if (requestingWorkload == reservableWorkloads[requestedSource]) {
								// Also update requestedSource's reservable workload according to the best knowledge, if it was not updated in the meantime.
								split(requestingWorkload[0], requestingWorkload[1], &reservableWorkloads[requestedSource], &requestingWorkload);
							} else
								split(requestingWorkload[0], requestingWorkload[1], nullptr, &requestingWorkload);

							// 2.4.2 Apply workload and finish loading, or continue with more requests in case of rejection
							if (approved) {
								cout << "[Rank " + to_string(mpi_rank) + "] Workload transfer approved. Starting to work on " + to_string(requestedSource) + ":[" + to_string(requestingWorkload[0]) + ", " + (requestingWorkload[1] ? to_string(requestingWorkload[1] - 1) : "-1") + "]." << endl;
								workload = requestingWorkload; // update current workload
								loading = false; // the worker thread may now continue
							} else
								requestedSource = -1; // need another reservation request ; the workload in question has been given to another process in the meantime
						}
					}
				}
			} while (loading); // a gathering and reserve operation is ongoing
		} else
			this_thread::yield(); // reservations are currently being accessed => try again next time
	};
	if (isMainProc) {
		int numComplete = 0;
		uint64_t index;
		while (communicate) {
			while (FctHelper::mpi_tryRecvUint64(mpi_rank, MPI_ANY_SOURCE, index))
				if (index == UINT64_MAX) // notification that the process is done
					numComplete++;
				else {
					toErase_mainProc.insert(index);

					// Show progress if requested
					if (progressData && progressData->nextStep()) {
						uint64_t percentage;
						string progress;
						string etc;
						if (progressData->nextState(percentage, progress, etc))
							cout << myTime() + ": Removed " + (progressData->maximumEstimated ? "≈" : "") + (percentage < 10 ? " " : "") + to_string(percentage) + "% of redundant conclusions. [" + progress + "] (" + etc + ")" << endl;
					}
				}
			if (numComplete + 1 == mpi_size) {
				// NOTE: The MPI standard guarantees that messages are received in the order they are sent ("non-overtaking messages", https://www.mpi-forum.org/docs/mpi-1.1/mpi-11-html/node41.html).
				//       Therefore, since UINT64_MAX is the last message for each rank, all messages have been received.
				//#cerr << "[ARNOLD] EVERYONE, SHUT THE FUCK DOWN!" << endl;
				for (int dest = 1; dest < mpi_size; dest++) // tell everyone to shut down
					FctHelper::mpi_sendBool(mpi_rank, true, dest, FctHelper::mpi_tag_custom + mpi_tag_terminate);
				communicate = false;
			} else if (checkRequests) // timed notification to check for incoming balancing requests from other processes
				handleBalancingRequests();
			else
				this_thread::yield();
		}
	} else
		while (communicate) {
			cond.wait(condLock);
			uint64_t index = 0;
			while (toErase.try_pop(index)) // send and clear 'toErase'
				FctHelper::mpi_sendUint64(mpi_rank, index, 0);
			if (workerDone && !waitTermination && toErase.empty()) {
				FctHelper::mpi_sendUint64(mpi_rank, UINT64_MAX, 0); // notify main process that this process is done
				waitTermination = true; // stay responsive to balancing requests in order to avoid deadlocks ; communication ends only when the main process says so
				//#cout << "[Rank " + to_string(mpi_rank) + "] WHERE'S ARNOLD?" << endl;
			}
			if (checkRequests) // timed notification to check for incoming balancing requests from other processes
				handleBalancingRequests();
		}
	//#cout << "[Rank " + to_string(mpi_rank) + "] Communication complete, waiting for worker to join main thread." << endl;
	workerThread.join();
	timerThread.join();
	//#if (isMainProc) cout << FctHelper::round(static_cast<long double>(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime).count()) / 1000.0, 2) + " ms taken for data iteration." << endl;

	//#MPI_Barrier(MPI_COMM_WORLD);
	//#cout << "[Rank " + to_string(mpi_rank) + "] Done. Candidates registered: " + to_string(localCounter) << endl;
	return toErase_mainProc;
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
		size_t bestSize = SIZE_MAX;
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
			uint32_t remainingSpace = wordLengthLimit - static_cast<uint32_t>(prefix.length() + stack.size()); // NOTE: Considers that stack already popped the current symbol.
			for (uint32_t s = 3; s <= knownLimit; s += 2)
				if (remainingSpace >= s)
					processRepresentatives(allRepresentatives[s]);

			// 2/2 : ε, S, [A] ; stack: pop current symbol, push [A] on top of stack
			stack.push_back(A);
			recurse_loadCondensedDetachmentPlProofs_generic_par(prefix, stack, wordLengthLimit, knownLimit, allRepresentatives, queues, mtxs, combinations);
		} else if (symbol == A) {
			uint32_t remainingSpace = wordLengthLimit - static_cast<uint32_t>(prefix.length() + stack.size() - 1); // NOTE: Considers that stack still has to pop the current symbol.
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
		size_t bestSize = SIZE_MAX;
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
