#ifndef XAMIDI_LOGIC_DLPROOFENUMERATOR_H
#define XAMIDI_LOGIC_DLPROOFENUMERATOR_H

#include "../helper/FwdTbb.h"
#include "../helper/ProgressData.h"
#include "../metamath/DRuleParser.h"

#include <array>
#include <condition_variable>
#include <iostream>
#include <iterator>
#include <tbb/concurrent_hash_map.h>
#include <tbb/concurrent_queue.h>
#include <tbb/concurrent_unordered_map.h>
#include <thread>

namespace xamidi {
namespace logic {

enum class DlProofEnumeratorMode {
	Dynamic, FromConclusionStrings, FromConclusionTrees, Naive
};

enum class DlFormulaStyle {
	PolishNumeric, PolishStandard, InfixUnicode
};

enum class ExtractionMethod {
	TopListFile, ProofSystemFromTopList, ProofSystemFromString, ProofSystemFromFile, CopyWithLimitedConclusions
};

struct DlProofEnumerator {
	// Data loading
	static bool loadDProofRepresentatives(std::vector<std::vector<std::string>>& allRepresentatives, std::vector<std::vector<std::string>>* optOut_allConclusions, std::uint64_t* optOut_allRepresentativesCount = nullptr, std::map<std::uint32_t, std::uint64_t>* optOut_representativeCounts = nullptr, std::uint32_t* optOut_firstMissingIndex = nullptr, bool debug = false, const std::string& filePrefix = "data/dProofs", const std::string& filePostfix = ".txt", bool initFresh = true, std::uint32_t limit = UINT32_MAX, const std::uint32_t* proofLenStepSize = nullptr);
	static tbb::concurrent_hash_map<std::string, std::string> parseDProofRepresentatives(const std::vector<std::string>& representatives, helper::ProgressData* const progressData = nullptr, std::atomic<std::uint64_t>* misses_speedupN = nullptr, tbb::concurrent_hash_map<std::string, std::string>* target_speedupN = nullptr, tbb::concurrent_unordered_map<std::string, std::string>* lookup_speedupN = nullptr);
	static tbb::concurrent_hash_map<std::string, std::string> parseDProofRepresentatives(const std::vector<std::vector<std::string>>& allRepresentatives, helper::ProgressData* const progressData = nullptr, std::atomic<std::uint64_t>* misses_speedupN = nullptr, tbb::concurrent_unordered_map<std::string, std::string>* lookup_speedupN = nullptr, const std::uint32_t* proofLenStepSize = nullptr);
	static tbb::concurrent_hash_map<std::string, std::string> connectDProofConclusions(const std::vector<std::vector<std::string>>& allRepresentatives, const std::vector<std::vector<std::string>>& allConclusions, helper::ProgressData* const progressData = nullptr, const std::uint32_t* proofLenStepSize = nullptr);
	static bool parseAndInsertDProof_speedupN(tbb::concurrent_hash_map<std::string, std::string>::accessor* wAcc, bool* isNew, const std::string& dProof, tbb::concurrent_hash_map<std::string, std::string>& results, tbb::concurrent_unordered_map<std::string, std::string>* lookup_speedupN = nullptr, bool permissive = false, std::atomic<std::uint64_t>* misses_speedupN = nullptr, std::size_t maxSymbolicConclusionLength = SIZE_MAX, std::size_t maxSymbolicConsequentLength = SIZE_MAX);
	static tbb::concurrent_unordered_map<std::string, std::string> parseDProofRepresentatives_um(const std::vector<std::string>& representatives, helper::ProgressData* const progressData = nullptr, std::atomic<std::uint64_t>* misses_speedupN = nullptr, tbb::concurrent_unordered_map<std::string, std::string>* target_speedupN = nullptr, tbb::concurrent_unordered_map<std::string, tbb::concurrent_unordered_map<std::string, std::string>::iterator>* lookup_speedupN = nullptr);
	static tbb::concurrent_unordered_map<std::string, std::string> parseDProofRepresentatives_um(const std::vector<std::vector<std::string>>& allRepresentatives, helper::ProgressData* const progressData = nullptr, std::atomic<std::uint64_t>* misses_speedupN = nullptr, tbb::concurrent_unordered_map<std::string, tbb::concurrent_unordered_map<std::string, std::string>::iterator>* lookup_speedupN = nullptr, const std::uint32_t* proofLenStepSize = nullptr);
	static tbb::concurrent_unordered_map<std::string, std::string> connectDProofConclusions_um(const std::vector<std::vector<std::string>>& allRepresentatives, const std::vector<std::vector<std::string>>& allConclusions, helper::ProgressData* const progressData = nullptr, const std::uint32_t* proofLenStepSize = nullptr);
	static std::pair<tbb::concurrent_unordered_map<std::string, std::string>::iterator, bool> parseAndInsertDProof_speedupN_um(const std::string& dProof, tbb::concurrent_unordered_map<std::string, std::string>& results, tbb::concurrent_unordered_map<std::string, tbb::concurrent_unordered_map<std::string, std::string>::iterator>* lookup_speedupN = nullptr, bool permissive = false, std::atomic<std::uint64_t>* misses_speedupN = nullptr, std::size_t maxSymbolicConclusionLength = SIZE_MAX, std::size_t maxSymbolicConsequentLength = SIZE_MAX);

	// Basic functionality
	static const std::vector<const std::vector<std::string>*>& builtinRepresentatives();
	static const std::vector<const std::vector<std::string>*>& builtinConclusions();
private:
	static std::vector<metamath::DRuleParser::AxiomInfo> _customAxioms;
	static const std::vector<metamath::DRuleParser::AxiomInfo>* _customAxiomsPtr;
	static std::vector<metamath::DRuleParser::AxiomInfo> _originalCustomAxioms;
	static const std::vector<metamath::DRuleParser::AxiomInfo>* _originalCustomAxiomsPtr;
	static std::map<std::string, std::string> _originalTheoremTranslation;
	static std::uint32_t _necessitationLimit;
	static bool _speedupN;
	static std::string _customAxiomsHash;
	static std::string _customizedPath;
	static std::vector<std::string> _customRepresentatives1;
	static std::vector<std::string> _customConclusions1;
	static const std::string _defaultConfig;
public:
	static const std::vector<metamath::DRuleParser::AxiomInfo>* getCustomAxioms();
	static std::uint32_t getNecessitationLimit();
	static std::string concatenateDataPath(const std::string& dataLocation, const std::string& append);
	static bool resetRepresentativesFor(const std::vector<std::string>* customAxioms = nullptr, bool normalPolishNotation = false, std::uint32_t necessitationLimit = 0, bool speedupN = true, const std::string* extractedSystemId = nullptr, std::ostream* stdOut = &std::cout, std::ostream* errOut = &std::cerr);
	static bool readInfoFile(std::map<std::uint32_t, std::uint64_t>* removalCounts, std::vector<std::string>* customInfoLines, std::size_t* removalCounts_infoLine, std::string& error);
	static void readConfigFile(bool initMissingFile = true, std::size_t* showProgress_bound = nullptr, std::size_t* parseProgressSteps5 = nullptr, std::size_t* parseProgressSteps10 = nullptr, std::size_t* collectProgressSteps2 = nullptr, std::size_t* collectProgressSteps5 = nullptr, std::size_t* collectProgressSteps10 = nullptr, std::size_t* filterProgressSteps2 = nullptr, std::size_t* filterProgressSteps5 = nullptr, std::size_t* filterProgressSteps10 = nullptr);
	static std::vector<const std::vector<std::string>*>& currentRepresentatives();
	static std::vector<const std::vector<std::string>*>& currentConclusions();
	static std::vector<std::vector<std::string>> composeToLookupVector(const std::vector<const std::vector<std::string>*>& all, const std::uint32_t* proofLenStepSize = nullptr);
	static bool readRepresentativesLookupVectorFromFiles_seq(std::vector<std::vector<std::string>>& allRepresentativesLookup, std::vector<std::vector<std::string>>* optOut_allConclusionsLookup, bool debug = false, const std::string& filePrefix = "data/dProofs", const std::string& filePostfix = ".txt", bool initFresh = true, std::uint32_t limit = UINT32_MAX, const std::uint32_t* proofLenStepSize = nullptr);
	static bool readRepresentativesLookupVectorFromFiles_par(std::vector<std::vector<std::string>>& allRepresentativesLookup, std::vector<std::vector<std::string>>* optOut_allConclusionsLookup, bool debug = false, unsigned concurrencyCount = std::thread::hardware_concurrency(), const std::string& filePrefix = "data/dProofs", const std::string& filePostfix = ".txt", bool initFresh = true, std::uint32_t limit = UINT32_MAX, const std::uint32_t* proofLenStepSize = nullptr);
	static std::vector<std::pair<std::array<std::uint32_t, 2>, unsigned>> proofLengthCombinationsD_oddLengths(std::uint32_t knownLimit, bool singleStep = false);
	static std::vector<std::pair<std::array<std::uint32_t, 2>, unsigned>> proofLengthCombinationsD_allLengths(std::uint32_t knownLimit, bool singleStep = false);
	static void sampleCombinations();
	static void printProofs(const std::vector<std::string>& dProofs, DlFormulaStyle outputNotation = DlFormulaStyle::PolishNumeric, bool conclusionsOnly = false, bool summaryMode = false, unsigned minUseAmountToCreateHelperProof = 2, bool abstractProofStrings = false, const std::string* inputFile = nullptr, const std::string* outputFile = nullptr, bool debug = false);
	static void convertProofSummaryToAbstractDProof(const std::string& input, std::vector<metamath::DRuleParser::AxiomInfo>* optOut_customAxioms = nullptr, std::vector<std::string>* optOut_abstractDProof = nullptr, std::vector<metamath::DRuleParser::AxiomInfo>* optOut_requiredIntermediateResults = nullptr, bool useInputFile = false, bool normalPolishNotation = false, bool noInputConclusions = false, bool debug = true);
	static void recombineProofSummary(const std::string& input, bool useInputFile, const std::string* conclusionsWithHelperProofs = nullptr, unsigned minUseAmountToCreateHelperProof = 2, std::size_t maxLengthToKeepProof = SIZE_MAX, bool normalPolishNotation = false, bool printInfixUnicode = false, const std::string* filterForTheorems = nullptr, bool abstractProofStrings = true, std::size_t storeIntermediateUnfoldingLimit = SIZE_MAX, std::size_t maxLengthToComputeDProof = 134217728, bool removeDuplicateConclusions = false, bool compress = false, bool noInputConclusions = false, const std::string* outputFile = nullptr, bool debug = false, bool compress_concurrentDRuleSearch = true);
	static void unfoldProofSummary(const std::string& input, bool useInputFile, bool normalPolishNotation, const std::string* filterForTheorems = nullptr, std::size_t storeIntermediateUnfoldingLimit = SIZE_MAX, std::size_t maxLengthToComputeDProof = 134217728, bool wrap = false, bool noInputConclusions = false, const std::string* outputFile = nullptr, bool debug = false);

	// Data prediction
	static void printGenerationExpenditures(bool redundantSchemaRemoval = true, bool withConclusions = true, bool debug = false);
	static void countNextIterationAmount(bool redundantSchemaRemoval = true, bool withConclusions = true);
	static bool determineCountingLimit(std::uint32_t wordLengthLimit, std::uint64_t& count, const std::map<std::uint32_t, std::uint64_t>& counts, bool iteration, std::uint64_t* maxNs = nullptr, bool assess = false);
	static std::map<std::uint32_t, std::uint64_t>& removalCounts();

	// Data generation
	// Summarized, this shared memory parallelism utilizing function is able to generate D-proofs without redundant conclusions ('dProofs<k>.txt')_{k<=n} (where time quickly becomes a limiting factor),
	// and subsequently it can generate D-proofs with redundant conclusions ('dProofs<m>-unfiltered<n+1>+.txt')_{m>n} (where space becomes a limiting factor).
	// The earlier one begins to generate D-proofs with redundant conclusions, the larger resulting files 'dProofs<m>-unfiltered<n+1>+.txt' become (with an exponential growth).
	// 'dProofs1.txt', 'dProofs3.txt', ..., 'dProofs15.txt' are built-in, and 'dProofs17.txt', ..., 'dProofs29.txt' are available at https://github.com/xamidi/pmGenerator/tree/master/data/dProofs-withConclusions
	// and https://github.com/xamidi/pmGenerator/tree/master/data/dProofs-withoutConclusions (150'170'911 bytes compressed into 'dProofs17-29.7z' of 1'005'537 bytes), so it is recommended to choose n >= 29.
	static void generateDProofRepresentativeFiles(std::uint32_t limit = UINT32_MAX, bool redundantSchemaRemoval = true, bool withConclusions = true, std::size_t* candidateQueueCapacities = nullptr, std::size_t maxSymbolicConclusionLength = SIZE_MAX, std::size_t maxSymbolicConsequentLength = SIZE_MAX, bool useConclusionStrings = false, bool useConclusionTrees = false);
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
	static void createGeneratorFilesWithConclusions(const std::string& dataLocation = "data", const std::string& inputFilePrefix = "dProofs-withoutConclusions/dProofs", const std::string& outputFilePrefix = "dProofs-withConclusions/dProofs", bool memoryOnly = false, bool debug = false, const std::uint32_t* proofLenStepSize = nullptr);
	static void createGeneratorFilesWithoutConclusions(const std::string& dataLocation = "data", const std::string& inputFilePrefix = "dProofs-withConclusions/dProofs", const std::string& outputFilePrefix = "dProofs-withoutConclusions/dProofs", bool memoryOnly = false, bool debug = false, const std::uint32_t* proofLenStepSize = nullptr);

	// Data search ; input files with conclusions are required
	static std::map<std::string, std::string> searchProofFiles(const std::vector<std::string>& searchTerms, bool normalPolishNotation = false, bool searchProofs = false, unsigned schemaSearch = 0, const std::string* inputFile = nullptr, bool debug = false);
	static void extractConclusions(ExtractionMethod method, std::uint32_t extractAmount, const std::string* config = nullptr, bool allowRedundantSchemaRemoval = false, bool forceRedundantSchemaRemoval = false, std::size_t bound1 = 0, std::size_t bound2 = 0, bool debug = false, std::string* optOut_createdExDir = nullptr);

	// Data representation ; input files with conclusions are required
	static void printConclusionLengthPlotData(bool measureSymbolicLength = true, bool table = true, std::int64_t cutX = -1, std::int64_t cutY = -1, const std::string& dataLocation = "data", const std::string& inputFilePrefix = "dProofs-withConclusions/dProofs", bool includeUnfiltered = false, std::ostream* mout = nullptr, bool debug = false, const std::uint32_t* proofLenStepSize = nullptr);

	// Helper functions
private:
	static void _collectProvenFormulas(tbb::concurrent_hash_map<std::string, std::string>& representativeProofs, std::uint32_t wordLengthLimit, DlProofEnumeratorMode mode, helper::ProgressData* const progressData, tbb::concurrent_unordered_map<std::string, std::string>* lookup_speedupN, std::atomic<std::uint64_t>* misses_speedupN, std::uint64_t* optOut_counter, std::uint64_t* optOut_conclusionCounter, std::uint64_t* optOut_redundantCounter, std::uint64_t* optOut_invalidCounter, const std::vector<std::uint32_t>* genIn_stack = nullptr, const std::uint32_t* genIn_n = nullptr, const std::vector<std::vector<std::string>>* genIn_allRepresentativesLookup = nullptr, const std::vector<std::vector<std::string>>* genIn_allConclusionsLookup = nullptr, std::vector<std::vector<std::shared_ptr<logic::DlFormula>>>* genInOut_allParsedConclusions = nullptr, std::vector<std::vector<std::atomic<bool>>>* genInOut_allParsedConclusions_init = nullptr, std::size_t* candidateQueueCapacities = nullptr, std::size_t maxSymbolicConclusionLength = SIZE_MAX, std::size_t maxSymbolicConsequentLength = SIZE_MAX);
	static void _removeRedundantConclusionsForProofsOfMaxLength(const std::uint32_t maxLength, tbb::concurrent_hash_map<std::string, std::string>& representativeProofs, helper::ProgressData* const progressData, std::uint64_t& conclusionCounter, std::uint64_t& redundantCounter);
	static tbb_concurrent_unordered_set<std::uint64_t> _mpi_removeRedundantConclusionsForProofsOfMaxLength(int mpi_rank, int mpi_size, const std::uint32_t maxLength, tbb::concurrent_hash_map<std::string, std::string>& representativeProofs, const std::vector<std::string>& recentConclusionSequence, helper::ProgressData* const progressData, bool smoothProgress);

public:
	// Iterates condensed detachment strings for proofs in D-N-notation (i.e. rules D : modus ponens and N : necessitation are supported),
	// using knowledge of all representative proofs of length n or lower, which must be passed via 'allRepresentatives'.
	// For strings of lengths n or lower, only one representative proof is used for each "relevant" equivalence class. Each proof a of formula ψ that
	// already has a schema which can be proven with not more steps than ψ, is also redundant. Equivalence classes of redundant proofs are irrelevant.
	// Generated strings allow an amount of 'necessitationLimit' consecutive applications of the necessitation rule "N".
	// When necessitation is disabled (i.e. proofs are only in D-notation), all proofs have odd length. Let c := necessitationLimit == 0 ? 2 : 1 denote the proof length step size.
	// Strings of lengths of n + c and higher may not encode valid proofs, i.e. may result in unification failures upon parsing.
	// One may customize what is being iterated by specifying the stack, i.e. { 0 } iterates all formulas, { s } for 0 < s <= n iterates formulas of length s, and
	// { n + c } iterates all formulas of at least length n + c. Note that this can be combined with 'wordLengthLimit' := n + c to iterate only formulas of length n + c.
	static void processCondensedDetachmentProofs_dynamic(const std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t n, const std::vector<const std::vector<std::string>*>& allRepresentatives, const auto& fString, std::uint32_t necessitationLimit, std::size_t* candidateQueueCapacities = nullptr, unsigned concurrencyCount = std::thread::hardware_concurrency()) {
		processCondensedDetachmentProofs_dynamic(stack, wordLengthLimit, n, composeToLookupVector(allRepresentatives), fString, necessitationLimit, candidateQueueCapacities, nullptr, nullptr, nullptr, concurrencyCount);
	}
	// default: parse full D-proofs
	// 'allConclusionsLookup' != nullptr => use (stored) conclusion strings to parse final rules
	// 'allConclusionsLookup' != nullptr && 'allParsedConclusions' != nullptr => use (stored) conclusion strings to parse and store unknown conclusion trees, and use those to parse final rules
	// 'stack' and 'wordLengthLimit' are only used for default variant ; 'fString' must be defined accordingly (see _loadCondensedDetachmentProofs_useConclusions() for non-default variants)
	static void processCondensedDetachmentProofs_dynamic(const std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t n, const std::vector<std::vector<std::string>>& allRepresentativesLookup, const auto& fString, std::uint32_t necessitationLimit, std::size_t* candidateQueueCapacities = nullptr, const std::vector<std::vector<std::string>>* allConclusionsLookup = nullptr, std::vector<std::vector<std::shared_ptr<logic::DlFormula>>>* allParsedConclusions = nullptr, std::vector<std::vector<std::atomic<bool>>>* allParsedConclusions_init = nullptr, unsigned concurrencyCount = std::thread::hardware_concurrency()) {
		if (n % 2 == 0 && necessitationLimit == 0)
			throw std::logic_error("Cannot have an even limit.");
		if (!allConclusionsLookup) {
			std::string prefix;
			std::vector<std::uint32_t> _stack = stack;
			if (concurrencyCount < 2) // call 'fString' only from this thread
				_processCondensedDetachmentProofs_dynamic_seq(prefix, _stack, wordLengthLimit, n, allRepresentativesLookup, fString, necessitationLimit);
			else { // call 'fString' from different threads ; NOTE: Iteration itself is super fast, so the worker threads' queues are loaded (and balanced while being processed) by this thread only.
				std::vector<tbb::concurrent_bounded_queue<std::string>> queues(concurrencyCount);
				if (candidateQueueCapacities)
					for (tbb::concurrent_bounded_queue<std::string>& queue : queues)
						queue.set_capacity(*candidateQueueCapacities);
				_loadAndProcessQueuesConcurrently(concurrencyCount, queues, [&]() { _loadCondensedDetachmentProofs_dynamic_par(prefix, _stack, wordLengthLimit, n, allRepresentativesLookup, queues, necessitationLimit); }, fString);
			}
		} else {
			std::vector<tbb::concurrent_bounded_queue<std::string>> queues(concurrencyCount);
			if (candidateQueueCapacities)
				for (tbb::concurrent_bounded_queue<std::string>& queue : queues)
					queue.set_capacity(*candidateQueueCapacities);
			_loadAndProcessQueuesConcurrently(concurrencyCount, queues, [&]() { _loadCondensedDetachmentProofs_useConclusions(n, allRepresentativesLookup, *allConclusionsLookup, queues, necessitationLimit, allParsedConclusions, allParsedConclusions_init); }, fString);
		}
	}

	// Iterates condensed detachment strings for proofs in D-notation.
	// Strings of lengths of 3 and higher may not encode valid proofs, i.e. may result in unification failures upon parsing.
	static void processCondensedDetachmentProofs_naive(std::uint32_t wordLengthLimit, const auto& fString, std::size_t* candidateQueueCapacities = nullptr, unsigned concurrencyCount = std::thread::hardware_concurrency()) {
		std::string prefix;
		if (concurrencyCount < 2) // call 'fString' only from this thread
			_processCondensedDetachmentProofs_naive_seq(prefix, 1, wordLengthLimit, fString);
		else { // call 'fString' from different threads ; NOTE: Iteration itself is super fast, so the worker threads' queues are loaded (and balanced while being processed) by this thread only.
			std::vector<tbb::concurrent_bounded_queue<std::string>> queues(concurrencyCount);
			if (candidateQueueCapacities)
				for (tbb::concurrent_bounded_queue<std::string>& queue : queues)
					queue.set_capacity(*candidateQueueCapacities);
			_loadAndProcessQueuesConcurrently(concurrencyCount, queues, [&]() { _loadCondensedDetachmentProofs_naive_par(prefix, 1, wordLengthLimit, queues); }, fString);
		}
	}

private:
	// The idea, for an odd number n := 'knownLimit', is to implement a pushdown automaton for a context-free grammar
	// with start symbol S, nonterminals {S, A} \cup {Xx | x > 0 odd, and x <= n}, and production rules
	// S -> X1 | ... | Xn | A                     (S produces a superset of all representative proofs.)
	// A -> <production generated by proofLengthCombinationsD_oddLengths(n)>, e.g. n = 5 => A -> D X1 X5 | D X5 X1 | D X3 X3 | D X3 X5 | D X5 X3 | D X1 A | D A X1 | D X5 X5 | D X3 A | D A X3 | D X5 A | D A X5 | D A A
	// X1 -> {p | p is representative proof of length 1}
	// ...
	// Xn -> {p | p is representative proof of length n}.
	// This grammar defines a superset of all condensed-detachment proofs on top of the already known proofs of lengths up to n, where A encodes those which have
	// at least length n + 2. By starting the pushdown automaton with stack [A], only the new candidates are iterated, of which invalid candidates can be skipped
	// after resulting in a parse error. When providing 'wordLengthLimit' := n + 2, this means to only iterate candidates of length n + 2 in an efficient way.
	// For even n allowed, this similarly works with proofLengthCombinationsD_allLengths(n), e.g. n = 3 => A -> D X1 X2 | D X2 X1 | D X1 X3 | D X3 X1 | D X2 X2 | D X2 X3 | D X3 X2 | D X1 A | D A X1 | D X3 X3 | D X2 A | D A X2 | D X3 A | D A X3 | D A A
	// [NOTE: Sequential non-generic variants (with explicit grammars given as comments) are available at https://github.com/deontic-logic/proof-tool/blob/29dd7dfab9f373d1dd387fb99c16e82c577ec21f/nortmann/DlProofEnumerator.h?ts=4#L167-L174 and below.]
	static void _loadAndProcessQueuesConcurrently(unsigned concurrencyCount, std::vector<tbb::concurrent_bounded_queue<std::string>>& queues, const auto& loader, const auto& process);
	static void _processCondensedDetachmentProofs_dynamic_seq(std::string& prefix, std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t knownLimit, const std::vector<std::vector<std::string>>& allRepresentatives, const auto& fString, std::uint32_t necessitationLimit);
	static void _processCondensedDetachmentProofs_naive_seq(std::string& prefix, unsigned stackSize, std::uint32_t wordLengthLimit, const auto& fString);
	static void _loadCondensedDetachmentProofs_dynamic_par(std::string& prefix, std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t knownLimit, const std::vector<std::vector<std::string>>& allRepresentatives, std::vector<tbb::concurrent_bounded_queue<std::string>>& queues, std::uint32_t necessitationLimit);
	static void _loadCondensedDetachmentProofs_naive_par(std::string& prefix, unsigned stackSize, std::uint32_t wordLengthLimit, std::vector<tbb::concurrent_bounded_queue<std::string>>& queues);

	// Similar to _loadCondensedDetachmentProofs_dynamic_par(), but can only generate unknown D-proofs of the smallest greater length (i.e. length of D-proofs with known conclusions increased by proof length step size),
	// since all conclusions that serve as inputs of the topmost rule (two for D-rule; one for N-rule) are required to be known to evaluate the rule directly (tree unification in case of D-rule, string concatenation in case of N-rule).
	// Registers strings like "D:<length of 1st input>,<length of 2nd input>:<index of 1st input>,<index of 2nd input>" or "N:<length of input>:<index of input>",
	// such that allConclusions[<length of (|1st |2nd )input>][<index of (|1st |2nd ) input>] address conclusion strings to be used.
	// When 'allParsedConclusions' is given, conclusions used by D-rules are additionally parsed and inserted into 'allParsedConclusions' at equal positions as in 'allConclusions'.
	static void _loadCondensedDetachmentProofs_useConclusions(std::uint32_t knownLimit, const std::vector<std::vector<std::string>>& allRepresentatives, const std::vector<std::vector<std::string>>& allConclusions, std::vector<tbb::concurrent_bounded_queue<std::string>>& queues, std::uint32_t necessitationLimit, std::vector<std::vector<std::shared_ptr<logic::DlFormula>>>* allParsedConclusions, std::vector<std::vector<std::atomic<bool>>>* allParsedConclusions_init);
};

void DlProofEnumerator::_loadAndProcessQueuesConcurrently(unsigned concurrencyCount, std::vector<tbb::concurrent_bounded_queue<std::string>>& queues, const auto& loader, const auto& process) {
	if (queues.size() != concurrencyCount)
		throw std::invalid_argument("|queues| = " + std::to_string(queues.size()) + ", but concurrencyCount = " + std::to_string(concurrencyCount) + ".");

	// 1. Prepare thread queues and worker threads.
	constexpr unsigned tinyBound = 10;
	constexpr unsigned sharingBound = 20;
	std::mutex mtx;
	std::unique_lock<std::mutex> condLock(mtx);
	std::condition_variable cond;
	std::vector<std::thread> threads;
	std::atomic<bool> incomplete = true; // NOTE: Indicates whether balancing may still take place, not whether all all queues are empty.
	auto worker = [&process, &queues, &cond, &incomplete](unsigned t) {
		tbb::concurrent_bounded_queue<std::string>& queue = queues[t];
		// NOTE: It is important to check '!queue.empty()' in loop header _after_ 'incomplete', since 'queue' might
		//       become filled and 'incomplete' false, while this condition is being processed in this thread.
		//       Since 'incomplete' can only become false after all queues are filled and no more balancing will
		//       take place, evaluating 'incomplete' first ensures that whenever 'queue' is not filled completely,
		//       the loop remains active, i.e. whenever !incomplete holds (such that '!queue.empty()' is checked here),
		//       the loop is discontinued only if there is nothing left to process.
		while (incomplete || !queue.empty()) {
			std::string s;
			if (queue.try_pop(s)) {
				process(s);
				if (queue.size() < tinyBound)
					cond.notify_one(); // notify queue balancer
			} else {
				cond.notify_one(); // notify queue balancer
				std::this_thread::yield();
			}
		}
	};
	for (unsigned t = 0; t < concurrencyCount; t++)
		threads.emplace_back(worker, t);

	// 2. Line up the working queues.
	loader();
	//#std::cout << "Loader complete." << std::endl;

	// 3. Balance the queues while they are being worked on.
	//#std::size_t balanceCounter = 0;
	while (true) {
		// NOTE: Every worker thread with a tiny queue will spam notifications until 'incomplete' is set to false below this loop, i.e. there cannot be a deadlock based on 'cond'.
		//       This way, no worker thread is ever blocked due to 'cond', which has better performance than utilizing locks to synchronize conditions.
		cond.wait(condLock);
		bool allTiny = true;
		bool someTiny = false;
		for (unsigned t = 0; t < queues.size(); t++)
			if (queues[t].size() < tinyBound) {
				someTiny = true;
				if (!allTiny)
					break;
			} else {
				allTiny = false;
				if (someTiny)
					break;
			}
		if (allTiny)
			break;
		if (someTiny) {
			std::map<unsigned, unsigned> tinyCandidates;
			std::map<unsigned, unsigned> sharingCandidates;
			for (unsigned t = 0; t < queues.size(); t++) {
				std::ptrdiff_t size = queues[t].size();
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
				tbb::concurrent_bounded_queue<std::string>& queue_largest = queues[t_largest];
				bool skip = false;
				std::ptrdiff_t size_largest = queue_largest.size();
				if (size_largest > sharingBound) { // ensure there still are enough elements
					std::size_t halfSize = size_largest / 2;
					if (halfSize >= tinyBound) { // ensure there still are enough elements, again
						tbb::concurrent_bounded_queue<std::string>& queue_smallest = queues[t_smallest];
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
		//#auto queueSizesStr = [&]() -> std::string { std::stringstream ss; for (unsigned t = 0; t < queues.size(); t++) { if (t) ss << ", "; std::size_t size = queues[t].size(); ss << t << ": " << size; } return ss.str(); }; // requires '#include <sstream>'
		//#std::cout << queueSizesStr() << std::endl; // print sizes of queues when a balancing attempt just took place
	}
	//#std::cout << "Balanced " << balanceCounter << " times." << std::endl;

	// 4. Wait for all threads to complete.
	incomplete = false;
	for (unsigned t = 0; t < threads.size(); t++)
		threads[t].join();
}

void DlProofEnumerator::_processCondensedDetachmentProofs_dynamic_seq(std::string& prefix, std::vector<std::uint32_t>& stack, std::uint32_t wordLengthLimit, std::uint32_t knownLimit, const std::vector<std::vector<std::string>>& allRepresentatives, const auto& fString, std::uint32_t necessitationLimit) {
	const std::uint32_t c = necessitationLimit ? 1 : 2; // proof length step size
	bool singleStep = wordLengthLimit <= knownLimit + c;
	const std::vector<std::pair<std::array<std::uint32_t, 2>, unsigned>> combinations = necessitationLimit ? proofLengthCombinationsD_allLengths(knownLimit, singleStep) : proofLengthCombinationsD_oddLengths(knownLimit, singleStep);
	bool ignoreN = !necessitationLimit || necessitationLimit == UINT32_MAX;
	auto recurse = [&wordLengthLimit, &knownLimit, &allRepresentatives, &fString, &necessitationLimit, &c, &singleStep, &combinations, &ignoreN](std::string& prefix, std::vector<std::uint32_t>& stack, const auto& me, std::uint32_t N = 0) -> void {
		constexpr std::uint32_t S = 0;
		const std::uint32_t A = knownLimit + c;
		// NOTE: X1, ..., X<knownLimit> are now simply 1, ..., knownLimit.
		if (prefix.length() + stack.size() > wordLengthLimit)
			return;
		if (stack.empty())
			fString(prefix);
		else {
			auto countLeadingNs = [](const std::string& p) { std::uint32_t counter = 0; for (std::string::const_iterator it = p.begin(); it != p.end() && *it == 'N'; ++it) counter++; return counter; };
			auto countTrailingNs = [](const std::string& p) { std::uint32_t counter = 0; for (std::string::const_reverse_iterator it = p.rbegin(); it != p.rend() && *it == 'N'; ++it) counter++; return counter; };
			auto fittingNs = [&](const std::string& pre, const std::string& post) { return countTrailingNs(pre) + countLeadingNs(post) <= necessitationLimit; };
			auto processX = [&](const std::vector<std::string>& representatives) {
				std::vector<std::uint32_t> stack_copy; // Since there are multiple options, we use copies for all
				std::string prefix_copy; //               but the last option, in order to restore the parameters.
				std::vector<std::string>::const_iterator last = std::prev(representatives.end());
				for (std::vector<std::string>::const_iterator it = representatives.begin(); it != last; ++it) {
					stack_copy = stack;
					prefix_copy = prefix;
					if (ignoreN) {
						prefix_copy += *it;
						me(prefix_copy, stack_copy, me);
					} else if (fittingNs(prefix_copy, *it)) {
						prefix_copy += *it;
						me(prefix_copy, stack_copy, me, countTrailingNs(prefix_copy));
					}
				}
				if (ignoreN) {
					prefix += *last;
					me(prefix, stack, me);
				} else if (fittingNs(prefix, *last)) {
					prefix += *last;
					me(prefix, stack, me, countTrailingNs(prefix));
				}
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
						if (ignoreN) {
							prefix_copy += sequence;
							me(prefix_copy, stack_copy, me);
						} else if (fittingNs(prefix_copy, sequence)) {
							prefix_copy += sequence;
							me(prefix_copy, stack_copy, me, countTrailingNs(prefix_copy));
						}
					}
				};
				processRepresentatives(allRepresentatives[1]);
				std::uint32_t remainingSpace = wordLengthLimit - static_cast<std::uint32_t>(prefix.length() + stack.size()); // NOTE: Considers that stack already popped the current symbol.
				for (std::uint32_t s = 1 + c; s <= knownLimit; s += c)
					if (remainingSpace >= s)
						processRepresentatives(allRepresentatives[s]);

				// 2/2 : ε, S, [A] ; stack: pop current symbol, push [A] on top of stack
				stack.push_back(A);
				me(prefix, stack, me);
			} else if (symbol == A) {
				std::uint32_t remainingSpace = wordLengthLimit - static_cast<std::uint32_t>(prefix.length() + stack.size() - 1); // NOTE: Considers that stack still has to pop the current symbol.
				if (remainingSpace < knownLimit + c)
					return; // cancel already if adding the below sequences would exceed the word length limit
				stack.pop_back(); // pop already for all cases
				std::vector<std::uint32_t> stack_copy; // Since there are multiple options, we use copies for all
				std::string prefix_copy; //               but the last option, in order to restore the parameters.
				if (N < necessitationLimit || necessitationLimit == UINT32_MAX) { // Δ := 2 (otherwise Δ := 0)
					// 1/2 : N, A, [X<knownLimit>] ; stack: pop current symbol, push [X<knownLimit>] on top of stack
					stack_copy = stack;
					prefix_copy = prefix + "N";
					stack_copy.push_back(knownLimit);
					me(prefix_copy, stack_copy, me, N + 1);
					if (!singleStep) {
						// 2/2 : N, A, [A] ; stack: pop current symbol, push [A] on top of stack
						stack_copy = stack;
						prefix_copy = prefix + "N";
						stack_copy.push_back(A);
						me(prefix_copy, stack_copy, me, N + 1);
					}
				}
				// (1+Δ)/(|combinations|+Δ) : D, A, [X1,X<knownLimit-2+c>] ; stack: pop current symbol, push [X1,X<knownLimit-2+c>] on top of stack
				// ...
				// (|combinations|+Δ)/(|combinations|+Δ) : D, A, [A,A] ; stack: pop current symbol, push [A,A] on top of stack
				if (combinations.empty())
					return;
				prefix += "D"; // same terminal for all remaining cases, so append to prefix already
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
				if (symbol > 1 && prefix.length() + symbol + stack.size() > wordLengthLimit + 1)
					return; // cancel already if adding the below sequences would exceed the word length limit ; condition already outruled for 'symbol == 1'
				const std::vector<std::string>& r = allRepresentatives[symbol];
				if (r.empty())
					return; // when X<symbol> is empty, throw out all stacks which make use of it
				stack.pop_back(); // pop already for all cases
				// 1/1 : {w | w is known representative of length <knownLimit>}, X<symbol>, [] ; stack: pop current symbol, push nothing
				processX(r);
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
void DlProofEnumerator::_processCondensedDetachmentProofs_naive_seq(std::string& prefix, unsigned stackSize, std::uint32_t wordLengthLimit, const auto& fString) {
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
