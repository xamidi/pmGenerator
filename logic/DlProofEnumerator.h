#ifndef XAMIDI_LOGIC_DLPROOFENUMERATOR_H
#define XAMIDI_LOGIC_DLPROOFENUMERATOR_H

#include "../helper/FwdTbb.h"
#include "../helper/ProgressData.h"

#include <array>
#include <condition_variable>
#include <cstddef>
#include <tbb/concurrent_queue.h>
#include <map>
#include <thread>

namespace xamidi {
namespace logic {

enum class DlProofEnumeratorMode {
	Generic, Naive
};

struct DlProofEnumerator {
	// Data loading
	static bool loadDProofRepresentatives(std::vector<std::vector<std::string>>& allRepresentatives, std::vector<std::vector<std::string>>* optOut_allConclusionsLookup, std::uint64_t* optOut_allRepresentativesCount = nullptr, std::uint32_t* optOut_firstMissingIndex = nullptr, bool debug = false, const std::string& filePrefix = "data/dProofs", const std::string& filePostfix = ".txt", bool initFresh = true, std::uint32_t limit = UINT32_MAX);
	static tbb_concurrent_unordered_map<std::string, std::string> parseDProofRepresentatives(const std::vector<std::string>& representatives, helper::ProgressData* const progressData = nullptr);
	static tbb_concurrent_unordered_map<std::string, std::string> parseDProofRepresentatives(const std::vector<std::vector<std::string>>& allRepresentatives, helper::ProgressData* const progressData = nullptr);
	static tbb_concurrent_unordered_map<std::string, std::string> connectDProofConclusions(const std::vector<std::vector<std::string>>& allRepresentatives, const std::vector<std::vector<std::string>>& allConclusions, helper::ProgressData* const progressData = nullptr);

	// Basic functionality
	static const std::vector<const std::vector<std::string>*>& builtinRepresentatives();
	static const std::vector<const std::vector<std::string>*>& builtinConclusions();
	static std::vector<std::vector<std::string>> composeToLookupVector(const std::vector<const std::vector<std::string>*>& all);
	static bool readRepresentativesLookupVectorFromFiles_seq(std::vector<std::vector<std::string>>& allRepresentativesLookup, std::vector<std::vector<std::string>>* optOut_allConclusionsLookup, bool debug = false, const std::string& filePrefix = "data/dProofs", const std::string& filePostfix = ".txt", bool initFresh = true, std::uint32_t limit = UINT32_MAX);
	static bool readRepresentativesLookupVectorFromFiles_par(std::vector<std::vector<std::string>>& allRepresentativesLookup, std::vector<std::vector<std::string>>* optOut_allConclusionsLookup, bool debug = false, unsigned concurrencyCount = std::thread::hardware_concurrency(), const std::string& filePrefix = "data/dProofs", const std::string& filePostfix = ".txt", bool initFresh = true, std::uint32_t limit = UINT32_MAX, std::size_t containerReserve = 100);
	static std::vector<std::pair<std::array<std::uint32_t, 2>, unsigned>> proofLengthCombinations(std::uint32_t knownLimit);

	// Data prediction
	static void countNextIterationAmount(bool redundantSchemaRemoval = true, bool withConclusions = true);
	static bool determineCountingLimit(std::uint32_t wordLengthLimit, std::uint64_t& count, const std::map<std::uint32_t, std::uint64_t>& counts, bool iteration);
	static std::map<std::uint32_t, std::uint64_t>& iterationCounts_filtered();
	static std::map<std::uint32_t, std::map<std::uint32_t, std::uint64_t>>& iterationCounts_unfiltered();
	static std::map<std::uint32_t, std::uint64_t>& removalCounts();

	// Data generation
	// Summarized, this shared memory parallelism utilizing function is able to generate D-proofs without redundant conclusions ('dProofs<k>.txt')_{k<=n} (where time quickly becomes a limiting factor),
	// and subsequently it can generate D-proofs with redundant conclusions ('dProofs<m>-unfiltered<n+1>+.txt')_{m>n} (where space becomes a limiting factor).
	// The earlier one begins to generate D-proofs with redundant conclusions, the larger resulting files 'dProofs<m>-unfiltered<n+1>+.txt' become (with an exponential growth).
	// 'dProofs1.txt', 'dProofs3.txt', ..., 'dProofs15.txt' are built-in, and 'dProofs17.txt', ..., 'dProofs29.txt' are available at https://github.com/xamidi/pmGenerator/tree/master/data/dProofs-withConclusions
	// and https://github.com/xamidi/pmGenerator/tree/master/data/dProofs-withoutConclusions (150'170'911 bytes compressed into 'dProofs17-29.7z' of 1'005'537 bytes), so it is recommended to choose n >= 29.
	static void generateDProofRepresentativeFiles(std::uint32_t limit = UINT32_MAX, bool redundantSchemaRemoval = true, bool withConclusions = true);
	// Given word length limit n, filters a first unfiltered proof file (with conclusions) at ./data/dProofs-withConclusions/dProofs<n>-unfiltered<n>+.txt in order to create dProofs<n>.txt.
	// The function utilizes multiple processes via Message Passing Interface (MPI) and assumes that MPI has been initialized with at least MPI_THREAD_FUNNELED threading support.
	// Prints a warning message for single-process calls, i.e. when the executable was not called via "mpiexec -n <np> ./pmGenerator <args>" or "srun -n <np> ./pmGenerator <args>" (with np > 1), or similar.
	// The schema checks are distributed among the processes, and candidates for removal are sent to the main thread of the main process for registration, as soon as they are detected.
	// Finally, the main process (MPI_COMM_WORLD rank 0) waits until all other processes have finished, and stores the resulting database at ./data/dProofs-withConclusions/dProofs<n>.txt.
	static void mpi_filterDProofRepresentativeFile(std::uint32_t wordLengthLimit, bool smoothProgress = true);
	// To create generator files with conclusions from those without, or vice versa. Generator files with conclusions are around four times bigger, with an increasing factor for increasing
	// proof lengths, e.g. for 'dProofs17.txt' there is a factor (369412 bytes)/(93977 bytes) ≈ 3.93, and for 'dProofs29.txt' there is a factor (516720692 bytes)/(103477529 bytes) ≈ 4.99.
	// Furthermore, files with conclusions have much higher entropy, thus can be compressed worse. For example, { 'dProofs17.txt', ..., 'dProofs29.txt' } can be compressed via LZMA to around
	// around 42 MB when conclusions are stored (compression ratio 735676962/41959698 ≈ 17.53), but to around 1 MB when conclusions are omitted (compression ratio 150170911/1005537 ≈ 149.34).
	static void createGeneratorFilesWithConclusions(const std::string& inputFilePrefix = "data/dProofs-withoutConclusions/dProofs", const std::string& outputFilePrefix = "data/dProofs-withConclusions/dProofs", bool debug = false);
	static void createGeneratorFilesWithoutConclusions(const std::string& inputFilePrefix = "data/dProofs-withConclusions/dProofs", const std::string& outputFilePrefix = "data/dProofs-withoutConclusions/dProofs", bool debug = false);

	// Data representation ; input files with conclusions are required
	static void printConclusionLengthPlotData(bool measureSymbolicLength = true, bool table = true, std::int64_t cutX = -1, std::int64_t cutY = -1, const std::string& inputFilePrefix = "data/dProofs-withConclusions/dProofs", std::ostream* mout = nullptr, bool debug = false);

	// Helper functions
private:
	static void _findProvenFormulas(tbb_concurrent_unordered_map<std::string, std::string>& representativeProofs, std::uint32_t wordLengthLimit, DlProofEnumeratorMode mode, helper::ProgressData* const progressData, std::uint64_t* optOut_counter, std::uint64_t* optOut_conclusionCounter, std::uint64_t* optOut_redundantCounter, std::uint64_t* optOut_invalidCounter, const std::vector<std::uint32_t>* genIn_stack = nullptr, const std::uint32_t* genIn_n = nullptr, const std::vector<std::vector<std::string>>* genIn_allRepresentativesLookup = nullptr);
	static void _removeRedundantConclusionsForProofsOfMaxLength(const std::uint32_t maxLength, tbb_concurrent_unordered_map<std::string, std::string>& representativeProofs, helper::ProgressData* const progressData, std::uint64_t& conclusionCounter, std::uint64_t& redundantCounter);
	static tbb_concurrent_unordered_set<std::uint64_t> _mpi_findRedundantConclusionsForProofsOfMaxLength(int mpi_rank, int mpi_size, const std::uint32_t maxLength, tbb_concurrent_unordered_map<std::string, std::string>& representativeProofs, const std::vector<std::string>& recentConclusionSequence, helper::ProgressData* const progressData, bool smoothProgress);

public:
	// Iterates condensed detachment strings for PL-proofs in D-notation, using knowledge of all representative proofs of length n or lower, which must be passed via 'allRepresentatives'.
	// For strings of lengths n or lower, only one representative proof is used for each "relevant" equivalence class. Each proof a of formula ψ that
	// already has a schema which can be proven with not more steps than ψ, is also redundant. Equivalence classes of redundant proofs are irrelevant.
	// Strings of lengths of n + 2 and higher may not encode valid PL-proofs, i.e. may result in unification failures upon parsing.
	// One may customize what is being iterated by specifying the stack, i.e. { 0 } iterates all formulas, { s } for 0 < s <= n iterates formulas of length s, and
	// { n + 2 } iterates all formulas of at least length n + 2. Note that this can be combined with 'wordLengthLimit' := n + 2 to iterate only formulas of length n + 2.
	static void processCondensedDetachmentPlProofs_generic(const std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t n, const std::vector<const std::vector<std::string>*>& allRepresentatives, const auto& fString, unsigned concurrencyCount = std::thread::hardware_concurrency()) {
		processCondensedDetachmentPlProofs_generic(stack, wordLengthLimit, n, composeToLookupVector(allRepresentatives), fString, concurrencyCount);
	}
	static void processCondensedDetachmentPlProofs_generic(const std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t n, const std::vector<std::vector<std::string>>& allRepresentativesLookup, const auto& fString, unsigned concurrencyCount = std::thread::hardware_concurrency()) {
		if (n % 2 == 0)
			throw std::logic_error("Cannot have an even limit.");
		std::string prefix;
		std::vector<std::uint32_t> _stack = stack;
		if (concurrencyCount < 2) // call 'fString' only from this thread
			_processCondensedDetachmentPlProofs_generic_seq(prefix, _stack, wordLengthLimit, n, allRepresentativesLookup, fString);
		else { // call 'fString' from different threads ; NOTE: Iteration itself is super fast, so the worker threads' queues are loaded (and balanced while being processed) by this thread only.
			std::vector<tbb::concurrent_queue<std::string>> queues(concurrencyCount);
			std::vector<std::mutex> mtxs(concurrencyCount);
			_loadAndProcessQueuesConcurrently(concurrencyCount, queues, mtxs, [&]() { _loadCondensedDetachmentPlProofs_generic_par(prefix, _stack, wordLengthLimit, n, allRepresentativesLookup, queues, mtxs); }, fString);
		}
	}

	// Iterates condensed detachment strings for PL-proofs in D-notation.
	// Strings of lengths of 3 and higher may not encode valid PL-proofs, i.e. may result in unification failures upon parsing.
	static void processCondensedDetachmentPlProofs_naive(std::uint32_t wordLengthLimit, const auto& fString, unsigned concurrencyCount = std::thread::hardware_concurrency()) {
		std::string prefix;
		if (concurrencyCount < 2) // call 'fString' only from this thread
			_processCondensedDetachmentPlProofs_naive_seq(prefix, 1, wordLengthLimit, fString);
		else { // call 'fString' from different threads ; NOTE: Iteration itself is super fast, so the worker threads' queues are loaded (and balanced while being processed) by this thread only.
			std::vector<tbb::concurrent_queue<std::string>> queues(concurrencyCount);
			std::vector<std::mutex> mtxs(concurrencyCount);
			_loadAndProcessQueuesConcurrently(concurrencyCount, queues, mtxs, [&]() { _loadCondensedDetachmentPlProofs_naive_par(prefix, 1, wordLengthLimit, queues, mtxs); }, fString);
		}
	}

private:
	// The idea, for an odd number n := 'knownLimit', is to implement a pushdown automaton for a context-free grammar
	// with start symbol S, nonterminals {S, A} \cup {Nx | x > 0 odd, and x <= n}, and production rules
	// S -> N1 | ... | Nn | A                     (S produces a superset of all representative proofs.)
	// A -> <production generated by proofLengthCombinations(n)>, e.g. n = 5 => A -> D N1 N5 | D N5 N1 | D N3 N3 | D N3 N5 | D N5 N3 | D N1 A | D A N1 | D N5 N5 | D N3 A | D A N3 | D N5 A | D A N5 | D A A
	// N1 -> {p | p is representative proof of length 1}
	// ...
	// Nn -> {p | p is representative proof of length n}.
	// This grammar defines a superset of all condensed-detachment proofs on top of the already known proofs of lengths up to n, where A encodes those which have
	// at least length n + 2. By starting the pushdown automaton with stack [A], only the new candidates are iterated, of which invalid candidates can be skipped
	// after resulting in a parse error. When providing 'wordLengthLimit' := n + 2, this means to only iterate candidates of length n + 2 in an efficient way.
	// [NOTE: Sequential non-generic variants (with explicit grammars given as comments) are available at https://github.com/deontic-logic/proof-tool/blob/29dd7dfab9f373d1dd387fb99c16e82c577ec21f/nortmann/DlProofEnumerator.h?ts=4#L167-L174 and below.]
	static void _loadAndProcessQueuesConcurrently(unsigned concurrencyCount, std::vector<tbb::concurrent_queue<std::string>>& queues, std::vector<std::mutex>& mtxs, const auto& loader, const auto& process);
	static void _processCondensedDetachmentPlProofs_generic_seq(std::string& prefix, std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t knownLimit, const std::vector<std::vector<std::string>>& allRepresentatives, const auto& fString);
	static void _processCondensedDetachmentPlProofs_naive_seq(std::string& prefix, unsigned stackSize, std::uint32_t wordLengthLimit, const auto& fString);
	static void _loadCondensedDetachmentPlProofs_generic_par(std::string& prefix, std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t knownLimit, const std::vector<std::vector<std::string>>& allRepresentatives, std::vector<tbb::concurrent_queue<std::string>>& queues, std::vector<std::mutex>& mtxs);
	static void _loadCondensedDetachmentPlProofs_naive_par(std::string& prefix, unsigned stackSize, std::uint32_t wordLengthLimit, std::vector<tbb::concurrent_queue<std::string>>& queues, std::vector<std::mutex>& mtxs);
};

void DlProofEnumerator::_loadAndProcessQueuesConcurrently(unsigned concurrencyCount, std::vector<tbb::concurrent_queue<std::string>>& queues, std::vector<std::mutex>& mtxs, const auto& loader, const auto& process) {
	if (queues.size() != concurrencyCount || mtxs.size() != concurrencyCount)
		throw std::invalid_argument("|queues| = " + std::to_string(queues.size()) + ", |mtxs| = " + std::to_string(mtxs.size()) + ", but concurrencyCount = " + std::to_string(concurrencyCount) + ".");

	// 1. Prepare thread queues and worker threads.
	constexpr unsigned tinyBound = 10;
	constexpr unsigned sharingBound = 20;
	std::mutex mtx;
	std::unique_lock<std::mutex> condLock(mtx);
	std::condition_variable cond;
	std::vector<std::thread> threads;
	std::atomic<bool> incomplete = true; // NOTE: Indicates whether balancing may still take place, not whether all all queues are empty.
	auto worker = [&process, &queues, &cond, &incomplete](unsigned t) {
		tbb::concurrent_queue<std::string>& queue = queues[t];
		// NOTE: It is important to check '!queue.empty()' in loop header _after_ 'incomplete', since 'queue' might
		//       become filled and 'incomplete' false, while this condition is being processed in this thread.
		//       Since 'incomplete' can only become false after all queues are filled and no more balancing will
		//       take place, evaluating 'incomplete' first ensures that whenever 'queue' is not filled completely,
		//       the loop remains active, i.e. whenever !incomplete holds (such that '!queue.empty()' is checked here),
		//       the loop is discontinued only if there is nothing left to process.
		while (incomplete || !queue.empty()) {
			std::string s;
			if (queue.try_pop(s))
				process(s);
			else {
				// NOTE: The queue balancer is notified only when a queue is already empty, but such requests lead to all
				//       queues smaller than 'tinyBound' being balanced with those being larger than 'sharingBound'.
				//       Routinely requesting locks in order to retrieve queue sizes by workers would take too much time.
				cond.notify_one();
				std::this_thread::yield();
			}
		}
	};
	for (unsigned t = 0; t < concurrencyCount; t++)
		threads.emplace_back(worker, t);

	// 2. Line up the working queues.
	loader();

	// 3. Balance the queues while they are being worked on.
	//#std::size_t balanceCounter = 0;
	while (true) {
		// NOTE: Every worker thread with an empty queue will spam notifications until 'incomplete' is set to false below this loop, i.e. there cannot be a deadlock based on 'cond'.
		//       This way, no worker thread is ever blocked due to 'cond', which has better performance than utilizing locks to synchronize conditions.
		cond.wait(condLock);
		bool allTiny = true;
		bool someTiny = false;
		for (unsigned t = 0; t < queues.size(); t++) {
			std::size_t size;
			{
				std::lock_guard<std::mutex> lock(mtxs[t]);
				size = queues[t].unsafe_size();
			}
			if (size < tinyBound) {
				someTiny = true;
				if (!allTiny)
					break;
			} else {
				allTiny = false;
				if (someTiny)
					break;
			}
		}
		if (allTiny)
			break;
		if (someTiny) {
			std::map<unsigned, unsigned> tinyCandidates;
			std::map<unsigned, unsigned> sharingCandidates;
			for (unsigned t = 0; t < queues.size(); t++) {
				std::size_t size;
				{
					std::lock_guard<std::mutex> lock(mtxs[t]);
					size = queues[t].unsafe_size();
				}
				if (size < tinyBound)
					tinyCandidates.emplace(size, t);
				else if (size > sharingBound)
					sharingCandidates.emplace(size, t);
			}
			while (!tinyCandidates.empty() && !sharingCandidates.empty()) {
				std::map<unsigned, unsigned>::const_iterator itSmallest = tinyCandidates.begin();
				std::map<unsigned, unsigned>::const_iterator itLargest = std::prev(sharingCandidates.end());
				unsigned t_smallest = itSmallest->second;
				unsigned t_largest = itLargest->second;
				std::vector<std::string> tmp;
				tbb::concurrent_queue<std::string>& queue_largest = queues[t_largest];
				bool skip = false;
				std::size_t size_largest;
				{
					std::lock_guard<std::mutex> lock(mtxs[t_largest]);
					size_largest = queue_largest.unsafe_size();
				}
				if (size_largest > sharingBound) { // ensure there still are enough elements
					std::size_t halfSize = size_largest / 2;
					if (halfSize >= tinyBound) { // ensure there still are enough elements, again
						tbb::concurrent_queue<std::string>& queue_smallest = queues[t_smallest];
						std::string s;
						for (std::size_t i = 0; i < halfSize && queue_largest.try_pop(s); i++)
							queue_smallest.push(s);
						//#balanceCounter++;
					} else
						skip = true;
				} else
					skip = true;
				if (!skip)
					tinyCandidates.erase(itSmallest);
				sharingCandidates.erase(itLargest);
			}
		}
		//#auto queueSizesStr = [&]() -> std::string { std::stringstream ss; for (unsigned t = 0; t < queues.size(); t++) { if (t) ss << ", "; std::size_t size = queues[t].unsafe_size(); ss << t << ": " << size; } return ss.str(); };
		//#std::cout << queueSizesStr() << std::endl; // print sizes of queues when a balancing attempt just took place
	}
	//#std::cout << "Balanced " << balanceCounter << " times." << std::endl;

	// 4. Wait for all threads to complete.
	incomplete = false;
	for (unsigned t = 0; t < threads.size(); t++)
		threads[t].join();
}

void DlProofEnumerator::_processCondensedDetachmentPlProofs_generic_seq(std::string& prefix, std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t knownLimit, const std::vector<std::vector<std::string>>& allRepresentatives, const auto& fString) {
	const std::vector<std::pair<std::array<std::uint32_t, 2>, unsigned>> combinations = proofLengthCombinations(knownLimit);
	auto recurse = [&wordLengthLimit, &knownLimit, &allRepresentatives, &fString, &combinations](std::string& prefix, std::vector<std::uint32_t>& stack, const auto& me) -> void {
		constexpr std::uint32_t S = 0;
		const std::uint32_t A = knownLimit + 2;
		// NOTE: N1, N3, ..., N<knownLimit> are now simply 1, 3, ..., knownLimit.
		if (prefix.length() + stack.size() > wordLengthLimit)
			return;
		if (stack.empty())
			fString(prefix);
		else {
			auto processN = [&](const std::vector<std::string>& representatives) {
				std::vector<std::uint32_t> stack_copy; // Since there are multiple options, we use copies for all
				std::string prefix_copy; //               but the last option, in order to restore the parameters.
				std::vector<std::string>::const_iterator last = std::prev(representatives.end());
				for (std::vector<std::string>::const_iterator it = representatives.begin(); it != last; ++it) {
					stack_copy = stack;
					prefix_copy = prefix;
					prefix_copy += *it;
					me(prefix_copy, stack_copy, me);
				}
				prefix += *last;
				me(prefix, stack, me);
			};
			std::uint32_t symbol = stack.back();
			if (symbol == S) {
				stack.pop_back(); // pop already for all cases
				// 1/2 : {1,...,allRepresentatives[knownLimit].back()}, S, [] ; stack: pop current symbol, push nothing
				std::vector<std::uint32_t> stack_copy; // Since there are multiple options, we use copies for all
				std::string prefix_copy; //               but the last option, in order to restore the parameters.
				auto processRepresentatives = [&](const std::vector<std::string>& representatives) {
					for (const std::string& sequence : representatives) {
						stack_copy = stack;
						prefix_copy = prefix;
						prefix_copy += sequence;
						me(prefix_copy, stack_copy, me);
					}
				};
				processRepresentatives(allRepresentatives[1]);
				std::uint32_t remainingSpace = wordLengthLimit - static_cast<std::uint32_t>(prefix.length() + stack.size()); // NOTE: Considers that stack already popped the current symbol.
				for (std::uint32_t s = 3; s <= knownLimit; s += 2)
					if (remainingSpace >= s)
						processRepresentatives(allRepresentatives[s]);

				// 2/2 : ε, S, [A] ; stack: pop current symbol, push [A] on top of stack
				stack.push_back(A);
				me(prefix, stack, me);
			} else if (symbol == A) {
				std::uint32_t remainingSpace = wordLengthLimit - static_cast<std::uint32_t>(prefix.length() + stack.size() - 1); // NOTE: Considers that stack still has to pop the current symbol.
				if (remainingSpace < knownLimit + 2)
					return; // cancel already if adding the below sequences would exceed the word length limit
				// 1/|combinations| : D, A, [N1,N<knownLimit>] ; stack: pop current symbol, push [N1,N<knownLimit>] on top of stack
				// ...
				// |combinations|/|combinations| : D, A, [A,A] ; stack: pop current symbol, push [A,A] on top of stack
				prefix += "D"; // same terminal for all cases, so all prefix already
				stack.pop_back(); // pop already for all cases
				std::vector<std::uint32_t> stack_copy; // Since there are multiple options, we use copies for all
				std::string prefix_copy; //               but the last option, in order to restore the parameters.
				for (unsigned i = 0; i < combinations.size() - 1; i++) {
					const std::pair<std::array<std::uint32_t, 2>, unsigned>& p = combinations[i];
					if (remainingSpace < p.second)
						return; // cancel already if adding the following sequences would exceed the word length limit
					stack_copy = stack;
					prefix_copy = prefix;
					stack_copy.insert(stack_copy.end(), p.first.rbegin(), p.first.rend());
					me(prefix_copy, stack_copy, me);
				}
				const std::pair<std::array<std::uint32_t, 2>, unsigned>& p = combinations[combinations.size() - 1];
				if (remainingSpace < p.second)
					return; // cancel already if adding the final sequence would exceed the word length limit
				stack.insert(stack.end(), p.first.rbegin(), p.first.rend());
				me(prefix, stack, me);
			} else {
				if (symbol > 1 && prefix.length() + symbol + stack.size() - 1 > wordLengthLimit)
					return; // cancel already if adding the below sequences would exceed the word length limit
				stack.pop_back(); // pop already for all cases
				// 1/1 : {w | w is known representative of length <knownLimit>}, N<symbol>, [] ; stack: pop current symbol, push nothing
				processN(allRepresentatives[symbol]);
			}
		}
	};
	recurse(prefix, stack, recurse);
}

// Grammar in Greibach normal form (GNF) for condensed detachment proofs (using D-notation): [NOTE: Also includes invalid combinations!]
//  S -> 1 | 2 | 3 | D S S
// Pushdown automaton:
//  M = ({q},{1,2,3,D},{S},δ,q,S,{})
// with transitions (q,a,N,q,β)∈δ such that a,N,β are:
//  1, S, ε
//  2, S, ε
//  3, S, ε
//  D, S, SS
void DlProofEnumerator::_processCondensedDetachmentPlProofs_naive_seq(std::string& prefix, unsigned stackSize, std::uint32_t wordLengthLimit, const auto& fString) {
	auto recurse = [&wordLengthLimit, &fString](std::string& prefix, unsigned stackSize, const auto& me) -> void {
		if (prefix.length() + stackSize > wordLengthLimit)
			return;
		if (!stackSize)
			fString(prefix);
		else {
			// 1/4 : 1, S, [] ; stack: pop current symbol, push nothing
			std::string prefix_copy = prefix; // Since there are multiple options, we use copies for all but the last option, in order to restore the parameters.
			prefix_copy += "1";
			me(prefix_copy, stackSize - 1, me);

			// 2/4 : 2, S, [] ; stack: pop current symbol, push nothing
			prefix_copy = prefix;
			prefix_copy += "2";
			me(prefix_copy, stackSize - 1, me);

			// 3/4 : 3, S, [] ; stack: pop current symbol, push nothing
			prefix_copy = prefix;
			prefix_copy += "3";
			me(prefix_copy, stackSize - 1, me);

			// 4/4 : D, S, [S,S] ; stack: pop current symbol, push [S,S] on top of stack
			prefix += "D";
			me(prefix, stackSize + 1, me);
		}
	};
	recurse(prefix, stackSize, recurse);
}

}
}

#endif // XAMIDI_LOGIC_DLPROOFENUMERATOR_H
