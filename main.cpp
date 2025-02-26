#include "helper/FctHelper.h"
#include "helper/Version.h"
#include "metamath/DRuleReducer.h"
#include "logic/DlProofEnumerator.h"

#include <boost/algorithm/string.hpp>

#include <cstring>
#include <ctime>
#ifdef _MSC_VER
#include <process.h>
#else
#include <unistd.h>
#endif

using namespace std;
using namespace xamidi::helper;
using namespace xamidi::metamath;
using namespace xamidi::logic;

struct A {
	string myTime() {
		time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
		return strtok(ctime(&time), "\n");
	}
	string myInfo() {
		stringstream ss;
		ss << "[pid: " << getpid() << ", tid:" << this_thread::get_id() << "]";
		return ss.str();
	}
	A() { cout << myTime() << ": Process started. " << myInfo() << endl; }
	~A() { cout << myTime() << ": Process terminated. " << myInfo() << endl; }
} a;

enum class Task {
	Invalid,
	Customize, //              -c
	Generate, //               -g
	CreateReplacements, //     -r
	ApplyReplacements, //      -a
	ParseAndPrintProofs, //    --parse
	TransformProofSummary, //  --transform
	UnfoldProofSummary, //     --unfold
	SearchProofFiles, //       --search
	ExtractFromProofFiles, //  --extract
	AssessGeneration, //       --assess
	IterateProofCandidates, // --iterate
	FileConversion, //         --variate
	ConclusionLengthPlot, //   --plot
	MpiFilter //               -m
};

static const map<Task, string>& cmdInfo() {
	static const map<Task, string> _ = []() {
		map<Task, string> _;
		_[Task::Customize] =
				"    -c [-i <file>] [-s <string>] [-n] [-N <limit or -1>] [-l] [-e <id>] [-d]\n"
				"       Proof system customization ; Generates a SHA-512/224 hash to identify the system, sets the effective data location to \"<data location>/<hash>\", and (if nonexisting) creates the !.def file.\n"
				"         -i: specify axioms by input file path (where a LF-separated string of axioms is stored), ignoring lines that are empty or starting with '%'\n"
				"         -s: specify axioms by comma-separated string ; used only when '-i' unspecified ; default: \"C0C1.0,CC0C1.2CC0.1C0.2,CCN0N1C1.0\"\n"
				"         -n: specify formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -N: enable necessitation rule \"N\" for the given system with unlimited (-N 0) or limited (-N <positive amount>) consecutive necessitation steps allowed\n"
				"         -l: disable lazy N-rule parsing ; parse proofs Nα:Lβ despite knowing α:β (requires more time but less memory)\n"
				"         -e: specify extracted system with the given identifier\n"
				"         -d: default system ; ignore all other arguments except '-e'\n";
		_[Task::Generate] =
				"    -g <limit or -1> [-u] [-q <limit or -1>] [-l <limit or -1>] [-k <limit or -1>] [-b] [-f] [-s]\n"
				"       Generate proof files ; at ./data/[<hash>/]/dProofs-withConclusions/ when '-s' unspecified ; otherwise at ./data/[<hash>/]/dProofs-withoutConclusions/\n"
				"         -u: unfiltered (significantly faster, but generates redundant proofs)\n"
				"         -q: limit number of proof candidate strings queued per worker thread (may lower memory requirements for systems with low acceptance rates) ; default: 50\n"
				"         -l: limit symbolic length of generated conclusions to at most the given number ; works only in extracted environments ; recommended to use in combination with '-q' to save memory\n"
				"         -k: similar to '-l' ; limit symbolic length of consequents in generated conclusions, i.e. antecedents in conditionals are not limited (but non-conditionals are limited in full length)\n"
				"         -b: brief parsing ; append conclusion structures to D-proof processing and use them for rule evaluation (collects faster, but requires significantly more memory)\n"
				"         -f: full parsing ; parse entire D-proofs rather than using conclusion strings for rule evaluation ; used only when '-b' unspecified\n"
				"         -s: proof files without conclusions, requires additional parsing ; entails '-f' ; used only when '-b' unspecified\n";
		_[Task::CreateReplacements] =
				"    -r <D-proof database> <output file> [-l <path>] [-i <prefix>] [-s] [-d]\n"
				"       Replacements file creation based on proof files\n"
				"         -l: customize data location path ; default: \"data\"\n"
				"         -i: customize input file path prefix in data location ; default: \"dProofs-withConclusions/dProofs\"\n"
				"         -s: proof files without conclusions, requires additional parsing ; sets default input file path prefix to \"dProofs-withoutConclusions/dProofs\"\n"
				"         -d: print debug information\n";
		_[Task::ApplyReplacements] =
				"    -a <initials> <replacements file> <D-proof database> <output file> [-s] [-l] [-w] [-d]\n"
				"       Apply replacements file\n"
				"         -s: style all proofs (replace proofs with alphanumerically smaller variants)\n"
				"         -l: list all proofs (i.e. not only modified proofs)\n"
				"         -w: wrap results\n"
				"         -d: print debug information\n";
		_[Task::ParseAndPrintProofs] =
				"    --parse <string> [-n] [-u] [-j <limit or -1>] [-b] [-s] [-e] [-f] [-o <output file>] [-d]\n"
				"       Parse and print proofs given by a comma-separated string\n"
				"         -n: print formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -u: print formulas in infix notation with operators as Unicode characters ; used only when '-n' unspecified\n"
				"         -j: join common subproofs together when they are used at least a given amount of times ; default: 2\n"
				"         -b: only print conclusions of the given proofs ; sets default of '-j' to 1\n"
				"         -s: only print summary with conclusions and abstract condensed detachment proofs ; used only when '-b' unspecified\n"
				"         -e: keep expanded proof strings ; show fully detailed condensed detachment proofs rather than allowing them to contain references ; used only when '-b' unspecified\n"
				"         -f: proofs are given by input file path (where a comma-separated string is stored), ignoring all CR, LF, whitespace, and lines starting with '%'\n"
				"         -o: redirect the result's output to the specified file\n"
				"         -d: print debug information\n";
		_[Task::TransformProofSummary] =
				"    --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-u] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-b] [-w] [-z] [-x <limit>] [-y] [-k] [-v <file>] [-h] [-q] [-f] [-o <output file>] [-d]\n"
				"       Transform proof summary (as by '--parse [...] -s') into recombined variant ; ignores configured system (proof summaries provide their own axioms) ; \",\" represents LF\n"
				"         -s: list a subproof with its conclusion if it occurs in the given comma-separated list of conclusions\n"
				"         -j: join common subproofs together when they are used at least a given amount of times ; default: 2\n"
				"         -p: only keep subproofs with primitive lengths not exceeding the given limit ; default: -1\n"
				"         -n: specify and print formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -u: print formulas in infix notation with operators as Unicode characters ; does not affect input format (for which '-n' can still be specified)\n"
				"         -t: only transform proofs of specified theorems (proven by subsequences of the input), given by a comma-separated string ; '-t .': all given conclusions ; '-t _': all used conclusions ; default: final theorem only\n"
				"         -e: keep expanded proof strings ; show fully detailed condensed detachment proofs rather than allowing them to contain references\n"
				"         -i: decrease memory requirements but increase time consumption by not storing intermediate unfoldings that exceed a certain length ; default: -1\n"
				"         -l: abort computation when combined requested proof sequences exceed the given limit in bytes ; default: 134217728 (i.e. 128 MiB)\n"
				"         -b: duplicate conclusion removal ; replace each given subproof that has a redundant conclusion with its first shortest alternative and remove duplicates ; beneficial in preparing '-z'\n"
				"         -w: read input without conclusions given\n"
				"         -z: proof compression ; find and remove internal redundancies (e.g. non-trivial parts not affecting intermediate theorems) by attempting to use shorter owned subproofs at all positions\n"
				"         -x: proof compression with extended modification range; before each round generate relative abstract proofs (D-rules only) with up to <range> steps, potentially improving rules with new formulas ; default: 0\n"
				"         -y: disable multi-threaded D-rule replacement search in case proof compression is performed (enables deterministic procedure) ; not affecting exhaustive generations via '-x', which remain nondeterministic\n"
				"         -k: store maximum-size proofs generated via 'x' also when they do not prove known intermediate theorems, so they can still be used as replacements for subproofs ; increases memory consumption significantly\n"
				"         -v: coordinate iteration phases for maximum-size proofs generated via 'x' with the specified vault file (to avoid repeating these computations over multiple runs) ; used only when '-k' unspecified\n"
				"         -h: save raw intermediate results in files before each proof compression round (and after productive rounds) ; after each preparation phase (exhaustive generation) in case '-x' is specified\n"
				"         -q: skip first round preparation for '-x' ; useful to continue working on intermediate results produced by an aborted computation using '-h'\n"
				"         -f: proof summary is given by input file path ; ignores lines that are empty or starting with '%'\n"
				"         -o: redirect the result's output to the specified file\n"
				"         -d: print debug information\n";
		_[Task::UnfoldProofSummary] =
				"    --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-v] [-f] [-o <output file>] [-d]\n"
				"       Break down proof summary (as by '--parse [...] -s') into primitive steps ; ignores configured system (proof summaries provide their own axioms) ; \",\" represents LF\n"
				"         -n: specify formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -t: obtain proofs of specified theorems (proven by subsequences of the input), given by a comma-separated string ; '-t .': all given conclusions ; '-t _': all used conclusions ; default: final theorem only\n"
				"         -i: decrease memory requirements but increase time consumption by not storing intermediate unfoldings that exceed a certain length ; default: -1\n"
				"         -l: abort computation when combined requested proof sequences exceed the given limit in bytes ; default: 134217728 (i.e. 128 MiB)\n"
				"         -w: wrap results\n"
				"         -v: read input without conclusions given\n"
				"         -f: proof summary is given by input file path ; ignores lines that are empty or starting with '%'\n"
				"         -o: redirect the result's output to the specified file\n"
				"         -d: print debug information\n";
		_[Task::SearchProofFiles] =
				"    --search <string> [-n] [-s] [-w] [-t] [-p] [-f] [-d]\n"
				"       Search in proof files at ./data/[<hash>/]/dProofs-withConclusions/ via comma-separated string of full formulas or full proofs ; [Hint: Generate missing files with '--variate 1 -s'.]\n"
				"         -n: specify formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -s: search for schemas of the given formulas\n"
				"         -w: search whole collections of schemas (i.e. enable multiple results per term) ; entails '-s'\n"
				"         -t: search for formulas of the given schemas (allows multiple results per term) ; used only when '-s' and '-w' unspecified\n"
				"         -p: search proofs (rather than conclusions) ; used only when '-n', '-s', '-w' and '-t' unspecified\n"
				"         -f: search terms are given by input file path (where a comma-separated string is stored), ignoring all CR, LF, whitespace, and lines starting with '%'\n"
				"         -d: print debug information\n";
		_[Task::ExtractFromProofFiles] =
				"    --extract [-t <limit or -1>] [-o <output file>] [-s] [-z] [-# <amount up to 35>] [-h <string>] [-l <limit or -1>] [-k <limit or -1>] [-f] [-d]\n"
				"       Various options to extract information from proof files ; [Hint: Generate missing files with '--variate 1 -s'.]\n"
				"         -t: compose file with up to the given amount of smallest conclusions that occur in proof files ; includes origins, symbolic lengths, proofs, and formulas in normal Polish notation\n"
				"         -o: specify output file path for '-t' ; relative to effective data location ; default: \"top<amount>SmallestConclusions_<min proof length>to<max proof length>Steps<unfiltered info>.txt\"\n"
				"         -s: redundant schema removal for '-t' ; very time-intensive for requesting huge collections from unfiltered proof files - better pre-filter via '-g' or '-m' instead ; default: false\n"
				"         -z: force redundant schema removal for '-t' ; like '-s', but also filter proof files not declared as unfiltered (which might be useful for non-standard procedures)\n"
				"         -#: initialize proof system at ./data/[<hash>/]/extraction-<id>/ with the given amount of smallest filtered conclusions that occur in proof files ; specify with '-c <parent system> -e <id>'\n"
				"         -h: similar to '-#' ; hand-pick conclusions with a comma-separated string of proofs ; \".\" to not modify axioms\n"
				"         -l: similar to '-#' (but creates identical system with prebuilt proof files) ; copy proofs with conclusions that have symbolic lengths of at most the given number\n"
				"         -k: similar to '-l' ; copy proofs with conclusions that have consequents or are non-conditionals of symbolic lengths of at most the given number ; can be combined with '-l'\n"
				"         -f: proofs for '-h' are given by input file path (where a comma-separated string is stored), ignoring all CR, LF, whitespace, and lines starting with '%'\n"
				"         -d: print debug information\n";
		_[Task::AssessGeneration] =
				"    --assess [-u] [-s] [-d]\n"
				"       Print proof file cardinalities, numbers of proof candidates for all generation steps up to the next one, and all stored and estimated next removal amounts (to assess generation expenditures)\n"
				"         -u: use unfiltered proof files\n"
				"         -s: use proof files without conclusions\n"
				"         -d: print debug information\n";
		_[Task::IterateProofCandidates] =
				"    --iterate [-u] [-s]\n"
				"       Iterate proof candidates currently next up for generation and print their amount (for resource consumption measurements)\n"
				"         -u: use unfiltered proof files\n"
				"         -s: use proof files without conclusions\n";
		_[Task::FileConversion] =
				"    --variate ( 0 | 1 ) [-l <path>] [-i <prefix>] [-o <prefix>] [-s] [-d]\n"
				"       Create proof files with removed (--variate 0) or added (--variate 1) conclusions from in-memory data and proof files of the other variant\n"
				"         -l: customize data location path ; default: \"data\"\n"
				"         -i: customize input file path prefix in data location ; default: \"dProofs-withConclusions/dProofs\" or \"dProofs-withoutConclusions/dProofs\"\n"
				"         -o: customize output file path prefix in data location ; default: \"dProofs-withoutConclusions/dProofs\" or \"dProofs-withConclusions/dProofs\"\n"
				"         -s: only use data stored in-memory\n"
				"         -d: print debug information\n";
		_[Task::ConclusionLengthPlot] =
				"    --plot [-l <path>] [-i <prefix>] [-s] [-t] [-x <limit or -1>] [-y <limit or -1>] [-o <output file>] [-d]\n"
				"       Print conclusion length plot data\n"
				"         -l: customize data location path ; default: \"data\"\n"
				"         -i: customize input file path prefix in data location ; requires files with conclusions ; default: \"dProofs-withConclusions/dProofs\"\n"
				"         -s: measure symbolic length (in contrast to conclusion representation length)\n"
				"         -u: include unfiltered proof files\n"
				"         -t: table arrangement, one data point per row\n"
				"         -x: upper horizontal limit\n"
				"         -y: upper vertical limit\n"
				"         -o: print to given output file\n"
				"         -d: print debug information\n";
		_[Task::MpiFilter] =
				"    -m <limit> [-s]\n"
				"       MPI-based multi-node filtering (-m <n>) of a first unfiltered proof file (with conclusions) at ./data/[<hash>/]dProofs-withConclusions/dProofs<n>-unfiltered<n>+.txt. Creates dProofs<n>.txt.\n"
				"         -s: disable smooth progress mode (lowers memory requirements, but makes terrible progress predictions)\n";
		return _;
	}();
	return _;
}

int main(int argc, char* argv[]) { // argc = 1 + N, argv = { <command>, <arg1>, ..., <argN> }
	// Custom tools' code - (v1.2.1) : https://github.com/xamidi/pmGenerator/commit/55c31a5f3dd951a72097393ba3d213980303dfe4
#if 0 //### ./searchShorterSubproofs ; search shorter proofs for conclusions used in a given proof summary
	// NOTE: Requires '#include "logic/DlCore.h"' and '#include <numeric>'.
	// e.g. ./searchShorterSubproofs data/w3.txt 0 data/tmp.txt CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,Cpp,CCpqCCqrCpr,CCNppp,CpCNpq 0
	if (argc <= 1) {
		cerr << "Need 1. path to proof summary. Optional: 2. necessitation limit (or -1), 3. output file path, 4. target theorems in normal Polish notation (or \"_\" to keep everything), 5. extracted system ID" << endl;
		return 0;
	}
	string proofSummaryFile = argv[1];
	uint32_t necessitationLimit = 0;
	if (argc >= 3) {
		try {
			necessitationLimit = stoi(argv[2]);
			cout << "Necessitation limit set to " << necessitationLimit << "." << endl;
		} catch (...) {
			cerr << "Invalid format for \"2. necessitation limit (or -1)\"." << endl;
			return 0;
		}
	}
	string tmpFile = "data/tmp.txt";
	string _outputFile;
	string* outputFile = nullptr;
	if (argc >= 4) {
		_outputFile = argv[3];
		outputFile = &_outputFile;
	}
	vector<DRuleParser::AxiomInfo>* targetTheorems = nullptr;
	vector<DRuleParser::AxiomInfo> _targetTheorems;
	bool targetEverything = false;
	if (argc >= 5) {
		string arg = argv[4];
		if (arg == "_")
			targetEverything = true;
		else {
			vector<string> theorems = FctHelper::stringSplit(arg, ",");
			for (const string& theorem : theorems) {
				shared_ptr<DlFormula> f;
				if (!DlCore::fromPolishNotation(f, theorem)) {
					cerr << "Invalid format for \"4. target theorems in normal Polish notation\"." << endl;
					return 0;
				}
				_targetTheorems.push_back(DRuleParser::AxiomInfo(theorem, f));
			}
			targetTheorems = &_targetTheorems;
		}
	}
	string _extractedSystemId;
	string* extractedSystemId = nullptr;
	if (argc >= 6) {
		_extractedSystemId = argv[5];
		extractedSystemId = &_extractedSystemId;
	}

	// 1. Obtain all conclusions used by proof summary (i.e. all which are relevant).
	string filterForTheorems = ".";
	DlProofEnumerator::recombineProofSummary(proofSummaryFile, true, nullptr, 1, SIZE_MAX, true, false, &filterForTheorems, true, SIZE_MAX, 134217728, false, false, false, &tmpFile, false);
	vector<string> conclusions;
	vector<size_t> fundamentalProofLengths;
	vector<DRuleParser::AxiomInfo> customAxioms;
	vector<string> abstractDProof;
	vector<shared_ptr<DlFormula>> abstractDProofConclusions;
	vector<DRuleParser::AxiomInfo> requiredIntermediateResults;
	{
		DlProofEnumerator::convertProofSummaryToAbstractDProof(tmpFile, &customAxioms, &abstractDProof, &requiredIntermediateResults, true, true, false);
		for (const DRuleParser::AxiomInfo& info : requiredIntermediateResults) {
			const shared_ptr<DlFormula>& f = info.refinedAxiom;
			abstractDProofConclusions.push_back(f);
			//conclusions.push_back(DlCore::toPolishNotation(f));
			conclusions.push_back(DlCore::toPolishNotation_noRename(f));
		}
		vector<size_t> targetIndices(abstractDProof.size());
		iota(targetIndices.begin(), targetIndices.end(), 0);
		fundamentalProofLengths = DRuleParser::measureFundamentalLengthsInAbstractDProof(targetIndices, abstractDProof, abstractDProofConclusions);

	}
	if (conclusions.size() != fundamentalProofLengths.size()) {
		cerr << "|conclusions| = " << conclusions.size() << " != " << fundamentalProofLengths.size() << " = |fundamentalProofLengths|" << endl;
		return 0;
	}
	cout << "Found " << conclusions.size() << " relevant conclusions." << endl;
	cout << "<conclusion>:<fundamental proof length>-pairs:" << endl;
	for (size_t i = 0; i < conclusions.size(); i++)
		cout << conclusions[i] << ":" << fundamentalProofLengths[i] << endl;
	cout << "[Copy] List of Conclusions: " << FctHelper::vectorString(conclusions, { }, { }, ",") << endl;
	cout << "[Copy] List of fundamental proof lengths: " << FctHelper::vectorString(fundamentalProofLengths, { }, { }, ",") << endl;

	// 2. Search conclusions in proof files.
	//#
	{
		vector<string> axioms;
		for (const DRuleParser::AxiomInfo& ax : customAxioms)
			axioms.push_back(DlCore::toPolishNotation_noRename(ax.refinedAxiom));
		DlProofEnumerator::resetRepresentativesFor(&axioms, false, necessitationLimit, true, extractedSystemId);
	}
	//#
	vector<string> improvedAbstractDProof = abstractDProof;
	map<string, string> bestResults = DlProofEnumerator::searchProofFiles(conclusions, false, false, true, nullptr, true);
	vector<size_t> indicesToCheck;
	vector<string> proofsToCheck;
	for (size_t i = 0; i < conclusions.size(); i++) {
		const string& conclusion = conclusions[i];
		map<string, string>::const_iterator searchResult = bestResults.find(conclusion);
		if (searchResult != bestResults.end()) {
			size_t usedLen = fundamentalProofLengths[i];
			const string& storedProof = searchResult->second;
			if (storedProof.length() < usedLen) {
				cout << "Found shorter proof " << storedProof << " (length " << storedProof.length() << ") for " << conclusion << " (" << DlCore::toPolishNotation(abstractDProofConclusions[i]) << "), for which a proof of fundamental length " << usedLen << " was given." << endl;
				improvedAbstractDProof[i] = storedProof;
			} else if (storedProof.length() == usedLen) { // Proof of same length is stored => Need to unfold proof in order to compare alphanumerically.
				indicesToCheck.push_back(i);
				proofsToCheck.push_back(storedProof);
			}
		}
	}

	// 3. Replace with shorter (sub)-proofs.
	vector<string> unfoldedProofs = DRuleParser::unfoldRulesInAbstractDProof(indicesToCheck, abstractDProof);
	for (size_t j = 0; j < indicesToCheck.size(); j++) {
		size_t i = indicesToCheck[j];
		const string& conclusion = conclusions[i];
		const string& storedProof = proofsToCheck[j];
		if (storedProof.length() != fundamentalProofLengths[i])
			throw logic_error("storedProof.length() = " + to_string(storedProof.length()) + " != " + to_string(fundamentalProofLengths[i]) + " = fundamentalProofLengths[" + to_string(i) + "]");
		const string& unfoldedProof = unfoldedProofs[j];
		if (storedProof < unfoldedProof) {
			cout << "Found alphanumerically smaller proof " << storedProof << " of the same fundamental length (" << storedProof.length() << ") for " << conclusion << " (" << DlCore::toPolishNotation(abstractDProofConclusions[i]) << ")." << endl;
			improvedAbstractDProof[i] = storedProof;
		}
	}

	// 4. Regenerate resulting abstract proof.
	vector<shared_ptr<DlFormula>> improvedConclusions;
	improvedAbstractDProof = DRuleParser::recombineAbstractDProof(improvedAbstractDProof, improvedConclusions, &customAxioms, targetEverything, targetTheorems, nullptr, 2, &requiredIntermediateResults, true, -2);

	// 5. Print result.
	bool normalPolishNotation = true; //###
	auto print = [&](ostream& mout) -> string::size_type {
		string::size_type bytes = 0;
		for (const DRuleParser::AxiomInfo& ax : customAxioms) {
			string f = normalPolishNotation ? DlCore::toPolishNotation(ax.refinedAxiom) : DlCore::toPolishNotation_noRename(ax.refinedAxiom);
			mout << "    " << f << " = " << ax.name << "\n";
			bytes += 9 + f.length();
		}
		for (size_t i = 0; i < improvedAbstractDProof.size(); i++) {
			string f = normalPolishNotation ? DlCore::toPolishNotation(improvedConclusions[i]) : DlCore::toPolishNotation_noRename(improvedConclusions[i]);
			const string& p = improvedAbstractDProof[i];
			mout << "[" << i << "] " << f << " = " << p << "\n";
			bytes += 7 + FctHelper::digitsNum_uint64(i) + f.length() + p.length();
		}
		return bytes;
	};
	chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	if (outputFile) { // Not using FctHelper::writeToFile() in order to write huge files without huge string acquisition.
		filesystem::path file = filesystem::u8path(*outputFile);
		while (!filesystem::exists(file) && !FctHelper::ensureDirExists(file.string()))
			cerr << "Failed to create file at \"" << file.string() << "\", trying again." << endl;
		string::size_type bytes;
		{
			ofstream fout(file, fstream::out | fstream::binary);
			bytes = print(fout);
		}
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print and save " << bytes << " bytes to " << file.string() << "." << endl;
	} else {
		string::size_type bytes = print(cout);
		cout << flush;
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to print " << bytes << " bytes." << endl;
	}
	return 0;
#endif //###
#if 0 //### entropy calculation
	// NOTE: Requires '#include <cmath>'.
	map<char, size_t> m;
	uint32_t num = 57;
	ifstream fin("data/0df075acc552c62513b49b6ed674bfcde1c1b018e532c665be229314/dProofs-withConclusions/dProofs" + to_string(num) + ".txt", fstream::in | fstream::binary);
	if (!fin.is_open()) {
		cerr << "Failed to read the data file. Aborting." << endl;
		return 0;
	}
	char c;
	while (fin.get(c))
		m[c]++;
	size_t len = 0;
	for (pair<char, size_t> p : m)
		len += p.second;
	double result = 0.0;
	for (const pair<char, size_t> p : m) {
		double frequency = static_cast<double>(p.second) / static_cast<double>(len);
		result -= frequency * log2(frequency);
	}
	cout << "Shannon entropy: " << result << " bits of information per byte" << endl; // e.g. 3.3841 for data/0df075acc552c62513b49b6ed674bfcde1c1b018e532c665be229314/dProofs-withConclusions/dProofs57.txt
	cout << "Length: " << len << endl;
	cout << "Amounts: " << FctHelper::mapStringF(m, [](const pair<char, size_t>& p) { return "'" + (p.first == '\n' ? "\\n" : string { p.first }) + "':" + to_string(p.second); }) << endl;
	return 0;
#endif //###
	//#cout << "argc = " << argc << ", argv = { " << [&]() { string s; for (int i = 0; i < argc; i++) { if (i) s += ", "; s += string { argv[i] }; } return s; }() << " }" << endl;
	auto printUsage = [&](const string& error = "", Task task = Task::Invalid) {
		if (!error.empty())
			cerr << error << endl;
		switch (task) {
		case Task::Invalid:
			cout << "\n" << xamidi::version << " ; repository at " << xamidi::repository;
			cout << "\nUsage:\n"
					"    pmGenerator ( <configuring command> | <composable command> )+ | <configuring command>* <standalone command>\n"
					"Configuring:\n";
			cout << cmdInfo().at(Task::Customize);
			cout << "Composable:\n";
			cout << cmdInfo().at(Task::Generate);
			cout << cmdInfo().at(Task::CreateReplacements);
			cout << cmdInfo().at(Task::ApplyReplacements);
			cout << cmdInfo().at(Task::ParseAndPrintProofs);
			cout << cmdInfo().at(Task::TransformProofSummary);
			cout << cmdInfo().at(Task::UnfoldProofSummary);
			cout << cmdInfo().at(Task::SearchProofFiles);
			cout << cmdInfo().at(Task::ExtractFromProofFiles);
			cout << cmdInfo().at(Task::AssessGeneration);
			cout << cmdInfo().at(Task::IterateProofCandidates);
			cout << cmdInfo().at(Task::FileConversion);
			cout << cmdInfo().at(Task::ConclusionLengthPlot);
			cout << "Standalone:\n";
			cout << cmdInfo().at(Task::MpiFilter);
			cout << "Examples:\n"
					"    pmGenerator -g -1 -q 50\n"
					"    pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -d -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w -d\n"
					"    pmGenerator --variate 0 -l data/ -o \"dProofs-withoutConclusions (all)/dProofs\" -d\n"
					"    pmGenerator --variate 1 -s --search CNpCCNpqNp -n -d --search CNpCCNpqNp -n -s\n"
					"    pmGenerator --variate 1 -s --search CCNpCpqCNpCpq,CCCCppCppCCCppCppCNCCqqCqqCCCqqCqqCCqqCqqCCCppCppCNCCqqCqqCCCqqCqqCCqqCqq -n -w -d\n"
					"    pmGenerator --plot -s -d --plot -s -t -x 50 -y 100 -o data/plot_data_x50_y100.txt\n"
					"    pmGenerator -c -N -1 -n -s CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp --parse DD2D16DD2DD2D13DD2D1D2DD2D1D2D1DD2DD2D13D1DD2DD2D13DD2D13114DD2D13DD2D1311D3DD2DD2D13DD2D1311 -j 2 -n\n"
					"    pmGenerator --parse DD2D11DD2D13DD2D1DD22D11DD2D11DD2D131 -n -s -o data/CNCpNqCrCsq.txt --transform data/CNCpNqCrCsq.txt -f -n -j 1 -e --transform data/CNCpNqCrCsq.txt -f -n -t CNCpNqCrq -d\n"
					"    pmGenerator --unfold CpCqp=1,CCpCqrCCpqCpr=2,CCNpNqCqp=3,[0]CCpCNqNrCpCrq:D2D13,[1]Cpp:DD211,[2]NCCppNCqq:DD3DD2DD2D[0]D[0]11D1[1][1] -n -t CNNpp,NCCppNCqq\n"
					"    pmGenerator --transform data/m.txt -f -n -t CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,Cpp,CCpqCCqrCpr,CCNppp,CpCNpq -j -1 -p -2 -d\n"
					"    pmGenerator --transform \"CCCpqrCCrpCsp=1,[0]=DDDD1D1D1D1DDDD1D1D11111111,[1]=D1DD[0]1[0],[2]=DDDD1DD[1][1]1111\" -n -w -t _\n"
					"    pmGenerator -c -s CCCCC0.1CN2N3.2.4CC4.0C3.0 -g 35 --plot -s -t -x 50 -y 100 -o data/478804cd4793bc7f87041d99326aff4595662146d8a68175dda22bed/plot_data_x50_y100.txt\n"
					"    pmGenerator -c -n -s CCCCCpqCNrNsrtCCtpCsp --search CpCqp,CCpCqrCCpqCpr,CCNpNqCqp -n\n"
					"    pmGenerator --variate 1 -s --extract -t 1000 -s -d\n"
					"    pmGenerator --variate 1 -s --extract -# 35 -d -c -d -e 0\n"
					"    pmGenerator -m 17 -s\n" << endl;
			break;
		default:
			cout << "\n" << cmdInfo().at(task) << endl;
			break;
		}
		return 0;
	};
#if 0 // default command
	if (argc <= 1) {
		//for (unsigned i = 0; i < 26; i++) cout << ", { \"" << i << "\", \"" << string { (char) ('p' + i <= 'z' ? 'p' + i : 'a' + i - 'z' + 'p' - 1) } << "\" }" << flush; cout << endl; return 0;
		//#DlProofEnumerator::sampleCombinations();
		//#for (unsigned knownLimit = 1; knownLimit < 100; knownLimit++)
		//#	cout << knownLimit << ":" << DlProofEnumerator::proofLengthCombinationsD_allLengths(knownLimit, false).size() << endl;
		//#return 0;
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-all.txt -l -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-all.txt -s -l -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-modifiedOnly.txt -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly-noWrap.txt -s", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator --plot -s -d --plot -s -t -x 50 -y 100 -o data/plot_data_x50_y100.txt", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -r data/pmproofs-unified.txt data/pmproofs-reducer33.txt -d", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -a SD data/pmproofs-reducer33.txt data/pmproofs-unified.txt data/pmproofs-unified33-modifiedOnly-noWrap.txt -s", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -a SD data/pmproofs-reducer33.txt data/pmproofs-unified.txt data/pmproofs-unified33.txt -s -l -w -d", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 35 -u", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -m 17", " ");
		// Redundancy check ; generates ./data/bf8f05b7537814a14fca0790dab97644033d9ca0ba5293063831124f/{!.def, dProofs-withConclusions/dProofs1.txt}, with "#removals;1:4" in !.def, and "4:C0C1.1" as only representative.
		static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -c -s CN0C1.1,C0CN1N1,C0CN1N1,C0C1.1,C0C1.1 --variate 1", " ");

		argc = static_cast<int>(customCmd.size());
		argv = new char*[customCmd.size()];
		for (size_t i = 0; i < customCmd.size(); i++)
			argv[i] = const_cast<char*>(customCmd[i].c_str());
	}
#endif
	if (argc <= 1)
		return printUsage();
	struct TaskInfo {
		Task task;
		map<string, string> str;
		map<string, int64_t> num;
		map<string, bool> bln;
		TaskInfo(Task task, const map<string, string>& str, const map<string, int64_t>& num, const map<string, bool>& bln) :
				task(task), str(str), num(num), bln(bln) {
		}
	};
	vector<TaskInfo> tasks;
	auto lastTask = [&]() -> Task { return tasks.empty() ? Task::Invalid : tasks.back().task; };

	string mpiArg;
	size_t mpiIgnoreCount = 0;
	bool extractedEnv = false;
	for (int i = 1; i < argc; i++) {
		auto recent = [&](const string& s = "?") {
			if (s == "c")
				return Task::Customize;
			else if (s == "g")
				return Task::Generate;
			else if (s == "r")
				return Task::CreateReplacements;
			else if (s == "a")
				return Task::ApplyReplacements;
			else if (s == "parse")
				return Task::ParseAndPrintProofs;
			else if (s == "search")
				return Task::SearchProofFiles;
			else if (s == "iterate")
				return Task::IterateProofCandidates;
			else if (s == "variate")
				return Task::FileConversion;
			else if (s == "plot")
				return Task::ConclusionLengthPlot;
			else if (s == "m")
				return Task::MpiFilter;
			else
				return tasks.empty() ? Task::Invalid : tasks.back().task;
		};
		if (argv[i][0] != '-' || argv[i][1] == '\0' || (argv[i][2] != '\0' && argv[i][1] != '-') || (argv[i][1] == '-' && argv[i][2] == '\0'))
			return printUsage("Invalid argument \"" + string { argv[i] } + "\".", recent());
		const char c = argv[i][1];
		switch (c) {

		// Commands
		case 'c': // -c [-i <file>] [-s <string>] [-n] [-N <limit or -1>] [-l] [-e <id>] [-d]
			if (!mpiArg.empty())
				return printUsage("Invalid argument \"-" + string { c } + "\": Cannot configure after \"" + mpiArg + "\".");
			tasks.emplace_back(Task::Customize, map<string, string> { { "axiomString", "C0C1.0,CC0C1.2CC0.1C0.2,CCN0N1C1.0" }, { "axiomFilePath", "" }, { "extractedSystemId", "" } }, map<string, int64_t> { { "necessitationLimit", 0 } }, map<string, bool> { { "useInputFile", false }, { "normalPolishNotation", false }, { "speedupN", true }, { "extractedSystem", false }, { "defaultSystem", false } });
			mpiIgnoreCount++;
			extractedEnv = false;
			break;
		case 'g': // -g <limit or -1> [-u] [-q <limit>] [-l <limit or -1>] [-k <limit or -1>] [-b] [-f] [-s]
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
			try {
				tasks.emplace_back(Task::Generate, map<string, string> { }, map<string, int64_t> { { "limit", stoi(argv[++i]) }, { "candidateQueueCapacities", 0 }, { "maxSymbolicConclusionLength", -1 }, { "maxSymbolicConsequentLength", -1 } }, map<string, bool> { { "redundantSchemaRemoval", true }, { "withConclusions", true }, { "useConclusionStrings", true }, { "useConclusionTrees", false }, { "whether -q was called", false } });
			} catch (...) {
				return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
			}
			break;
		case 'r': // -r <D-proof database> <output file> [-l <path>] [-i <prefix>] [-s] [-d]
			if (i + 2 >= argc)
				return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
			tasks.emplace_back(Task::CreateReplacements, map<string, string> { { "dProofDB", argv[i + 1] }, { "outputFile", argv[i + 2] }, { "dataLocation", "data" }, { "inputFilePrefix", "dProofs-withConclusions/dProofs" } }, map<string, int64_t> { }, map<string, bool> { { "withConclusions", true }, { "debug", false }, { "whether -i was called", false } });
			i += 2;
			break;
		case 'a': // -a <initials> <replacements file> <D-proof database> <output file> [-s] [-l] [-w] [-d]
			if (i + 4 >= argc)
				return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
			tasks.emplace_back(Task::ApplyReplacements, map<string, string> { { "initials", argv[i + 1] }, { "replacementsFile", argv[i + 2] }, { "dProofDB", argv[i + 3] }, { "outputFile", argv[i + 4] } }, map<string, int64_t> { }, map<string, bool> { { "styleAll", false }, { "listAll", false }, { "wrap", false }, { "debug", false } });
			i += 4;
			break;
		case 'm': // -m <limit> [-s]
			if (tasks.size() > mpiIgnoreCount)
				return printUsage("Invalid argument \"-" + string { c } + "\": Can only be combined with preceding configuring commands.");
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
			else {
				string param = string(argv[++i]);
				unsigned value;
				from_chars_result result = FctHelper::toUInt(param, value);
				if (result.ec != errc())
					return printUsage("Invalid parameter \"" + param + "\" for \"-" + string { c } + "\".", recent(string { c }));
				tasks.emplace_back(Task::MpiFilter, map<string, string> { }, map<string, int64_t> { { "wordLengthLimit", value } }, map<string, bool> { { "smoothProgress", true } });
				mpiArg = "-m";
			}
			break;
		case '-': { // "--<command>"
			string command { argv[i] + 2 };
			if (command == "parse") { // --parse <string> [-n] [-u] [-j <limit or -1>] [-b] [-s] [-e] [-f] [-o <output file>] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::ParseAndPrintProofs, map<string, string> { { "string", argv[++i] }, { "outputFile", "" } }, map<string, int64_t> { { "minUseAmountToCreateHelperProof", 2 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "normalPolishNotation", false }, { "unicodeInfixNotation", false }, { "conclusionsOnly", false }, { "summaryMode", false }, { "abstractProofStrings", true }, { "debug", false }, { "whether -j was called", false } });
			} else if (command == "transform") { // --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-u] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-b] [-w] [-z] [-x <limit>] [-y] [-k] [-v <file>] [-h] [-q] [-f] [-o <output file>] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::TransformProofSummary, map<string, string> { { "string", argv[++i] }, { "conclusionsWithHelperProofs", "" }, { "filterForTheorems", "" }, { "outputFile", "" }, { "compress_vault", "" } }, map<string, int64_t> { { "minUseAmountToCreateHelperProof", 2 }, { "maxLengthToKeepProof", -1 }, { "storeIntermediateUnfoldingLimit", -1 }, { "maxLengthToComputeDProof", 134217728 }, { "compress_range", 0 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "normalPolishNotation", false }, { "printInfixUnicode", false }, { "abstractProofStrings", true }, { "removeDuplicateConclusions", false }, { "compress", false }, { "noInputConclusions", false }, { "debug", false }, { "compress_concurrent", true }, { "compress_keep", false }, { "compress_sureSaves", false }, { "compress_skip", false }, { "whether -s was called", false }, { "whether -t was called", false }, { "whether -v was called", false } });
			} else if (command == "unfold") { // --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-v] [-f] [-o <output file>] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::UnfoldProofSummary, map<string, string> { { "string", argv[++i] }, { "filterForTheorems", "" }, { "outputFile", "" } }, map<string, int64_t> { { "storeIntermediateUnfoldingLimit", -1 }, { "maxLengthToComputeDProof", 134217728 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "normalPolishNotation", false }, { "wrap", false }, { "noInputConclusions", false }, { "debug", false }, { "whether -t was called", false } });
			} else if (command == "search") { // --search <string> [-n] [-s] [-w] [-t] [-p] [-f] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::SearchProofFiles, map<string, string> { { "string", argv[++i] } }, map<string, int64_t> { }, map<string, bool> { { "useInputFile", false }, { "normalPolishNotation", false }, { "searchProofs", false }, { "schemaSearch", false }, { "multiSchemaSearch", false }, { "abstractSearch", false }, { "debug", false } });
			} else if (command == "extract") // --extract [-t <limit or -1>] [-o <output file>] [-s] [-z] [-# <amount up to 35>] [-h <string>] [-l <limit or -1>] [-k <limit or -1>] [-f] [-d]
				tasks.emplace_back(Task::ExtractFromProofFiles, map<string, string> { { "proofs", "" }, { "outputFile", "" } }, map<string, int64_t> { { "extractToFileAmount", 0 }, { "extractToSystemAmount", 0 }, { "maxConclusionLength", 0 }, { "maxConsequentLength", 0 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "allowRedundantSchemaRemoval", false }, { "forceRedundantSchemaRemoval", false }, { "debug", false }, { "whether -t was called", false }, { "whether -# was called", false }, { "whether -h was called", false }, { "whether -l was called", false }, { "whether -k was called", false } });
			else if (command == "assess") // --assess [-u] [-s] [-d]
				tasks.emplace_back(Task::AssessGeneration, map<string, string> { }, map<string, int64_t> { }, map<string, bool> { { "redundantSchemaRemoval", true }, { "withConclusions", true }, { "debug", false } });
			else if (command == "iterate") // --iterate [-u] [-s]
				tasks.emplace_back(Task::IterateProofCandidates, map<string, string> { }, map<string, int64_t> { }, map<string, bool> { { "redundantSchemaRemoval", true }, { "withConclusions", true } });
			else if (command == "variate") {  // --variate ( 0 | 1 ) [-l <path>] [-i <prefix>] [-o <prefix>] [-s] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				else {
					string param = string(argv[++i]);
					if (param != "0" && param != "1")
						return printUsage("Invalid parameter \"" + param + "\" for \"--" + command + "\".", recent(command));
					bool with = param == "1";
					tasks.emplace_back(Task::FileConversion, map<string, string> { { "dataLocation", "data" }, { "inputFilePrefix", with ? "dProofs-withoutConclusions/dProofs" : "dProofs-withConclusions/dProofs" }, { "outputFilePrefix", with ? "dProofs-withConclusions/dProofs" : "dProofs-withoutConclusions/dProofs" } }, map<string, int64_t> { }, map<string, bool> { { "memoryOnly", false }, { "debug", false }, { "with", with } });
				}
				break;
			} else if (command == "plot") // --plot [-l <path>] [-i <prefix>] [-s] [-t] [-x <limit or -1>] [-y <limit or -1>] [-o <output file>] [-d]
				tasks.emplace_back(Task::ConclusionLengthPlot, map<string, string> { { "dataLocation", "data" }, { "inputFilePrefix", "dProofs-withConclusions/dProofs" }, { "mout", "" } }, map<string, int64_t> { { "cutX", -1 }, { "cutY", -1 } }, map<string, bool> { { "measureSymbolicLength", false }, { "table", false }, { "includeUnfiltered", false }, { "debug", false } });
			else
				return printUsage("Invalid argument \"--" + command + "\".", recent(command));
			break;
		}
		// Arguments
		case '#':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::ExtractFromProofFiles: // --extract -# <amount up to 35> (initialize proof system at ./data/[<hash>/]/extraction-<id>/ with the given amount [...])
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					unsigned num = stoi(argv[++i]);
					if (num > 35)
						throw "";
					tasks.back().num["extractToSystemAmount"] = num;
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["whether -# was called"] = true;
				break;
			}
			break;
		case 'b':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Generate: // -g -b (brief parsing)
				tasks.back().bln["useConclusionTrees"] = true;
				break;
			case Task::ParseAndPrintProofs: // --parse -b (only print conclusions of the given proofs)
				tasks.back().bln["conclusionsOnly"] = true;
				if (!tasks.back().bln["whether -j was called"])
					tasks.back().num["minUseAmountToCreateHelperProof"] = 1;
				break;
			case Task::TransformProofSummary: // --transform -b (duplicate conclusion removal)
				tasks.back().bln["removeDuplicateConclusions"] = true;
				break;
			}
			break;
		case 'd':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Customize: // -c -d (default system)
				tasks.back().bln["defaultSystem"] = true;
				break;
			case Task::CreateReplacements: //             -r -d (print debug information)
			case Task::ApplyReplacements: //              -a -d (print debug information)
			case Task::ParseAndPrintProofs: //       --parse -d (print debug information)
			case Task::TransformProofSummary: // --transform -d (print debug information)
			case Task::UnfoldProofSummary: //       --unfold -d (print debug information)
			case Task::SearchProofFiles: //         --search -d (print debug information)
			case Task::ExtractFromProofFiles: //   --extract -d (print debug information)
			case Task::AssessGeneration: //         --assess -d (print debug information)
			case Task::FileConversion: //          --variate -d (print debug information)
			case Task::ConclusionLengthPlot: //       --plot -d (print debug information)
				tasks.back().bln["debug"] = true;
				break;
			}
			break;
		case 'e':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Customize: // -c -e <id> (specify extracted system with the given identifie)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["extractedSystemId"] = argv[++i];
				tasks.back().bln["extractedSystem"] = true;
				extractedEnv = true;
				break;
			case Task::ParseAndPrintProofs: //       --parse -e (keep expanded proof strings)
			case Task::TransformProofSummary: // --transform -e (keep expanded proof strings)
				tasks.back().bln["abstractProofStrings"] = false;
				break;
			}
			break;
		case 'f':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Generate: // -g -f (full parsing)
				tasks.back().bln["useConclusionStrings"] = false;
				break;
			case Task::ParseAndPrintProofs: //       --parse -f (proofs are given by input file path)
			case Task::TransformProofSummary: // --transform -f (proof summary is given by input file path)
			case Task::UnfoldProofSummary: //       --unfold -f (proof summary is given by input file path)
			case Task::SearchProofFiles: //         --search -f (search terms are given by input file path)
			case Task::ExtractFromProofFiles: //   --extract -f (proofs for '-h' are given by input file path)
				tasks.back().bln["useInputFile"] = true;
				break;
			}
			break;
		case 'h':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::TransformProofSummary: // --transform -h (save raw intermediate results in files before each proof compression round)
				tasks.back().bln["compress_sureSaves"] = true;
				break;
			case Task::ExtractFromProofFiles: // --extract -h <string> (similar to '-#' ; hand-pick conclusions with a comma-separated string of proofs)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["proofs"] = argv[++i];
				tasks.back().bln["whether -h was called"] = true;
				break;
			}
			break;
		case 'i':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Customize: // -c -i <file> (specify axioms by input file path)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["axiomFilePath"] = argv[++i];
				tasks.back().bln["useInputFile"] = true;
				break;
			case Task::CreateReplacements: // -r -i <prefix> (customize input file path prefix in data location)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["inputFilePrefix"] = argv[++i];
				tasks.back().bln["whether -i was called"] = true;
				break;
			case Task::TransformProofSummary: // --transform -i <limit or -1> (decrease memory requirements but increase time consumption by not storing intermediate unfoldings that exceed a certain length)
			case Task::UnfoldProofSummary: //       --unfold -i <limit or -1> (decrease memory requirements but increase time consumption by not storing intermediate unfoldings that exceed a certain length)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["storeIntermediateUnfoldingLimit"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			case Task::FileConversion: //    --variate -i <prefix> (customize input file path prefix in data location)
			case Task::ConclusionLengthPlot: // --plot -i <prefix> (customize input file path prefix in data location)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["inputFilePrefix"] = argv[++i];
				break;
			}
			break;
		case 'j':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::ParseAndPrintProofs: // --parse -j <limit or -1> (join common subproofs together when they are used at least a given amount of times)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["minUseAmountToCreateHelperProof"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["whether -j was called"] = true;
				break;
			case Task::TransformProofSummary: // --transform -j <limit or -1> (join common subproofs together when they are used at least a given amount of times)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["minUseAmountToCreateHelperProof"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			}
			break;
		case 'k':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Generate: // -g -k <limit or -1> (similar to '-l' ; limit symbolic length of consequents in generated conclusions)
				if (!extractedEnv)
					return printUsage("Invalid argument \"-" + string { c } + "\" for \"-g\": Specific filters can only be used in extracted environments. [Hint: '--extract -h .' extracts a system with all axioms unmodified that can be specified with '-c <parent system> -e <id>'.]", recent(string { c }));
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["maxSymbolicConsequentLength"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			case Task::TransformProofSummary: // --transform -k (store maximum-size proofs generated via 'x' also when they do not prove known intermediate theorems)
				tasks.back().bln["compress_keep"] = true;
				break;
			case Task::ExtractFromProofFiles: // --extract -k <limit or -1> (similar to '-l' ; copy proofs with conclusions that have consequents or are non-conditionals of symbolic lengths of at most the given number)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["maxConsequentLength"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["whether -k was called"] = true;
				break;
			}
			break;
		case 'l':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Generate: // -g -l <limit or -1> (limit symbolic length of generated conclusions to at most the given number)
				if (!extractedEnv)
					return printUsage("Invalid argument \"-" + string { c } + "\" for \"-g\": Specific filters can only be used in extracted environments. [Hint: '--extract -h .' extracts a system with all axioms unmodified that can be specified with '-c <parent system> -e <id>'.]", recent(string { c }));
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["maxSymbolicConclusionLength"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			case Task::Customize: // -c -l (disable lazy N-rule parsing)
				tasks.back().bln["speedupN"] = false;
				break;
			case Task::CreateReplacements: //       -r -l <path> (customize data location path)
			case Task::FileConversion: //    --variate -l <path> (customize data location path)
			case Task::ConclusionLengthPlot: // --plot -l <path> (customize data location path)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["dataLocation"] = argv[++i];
				break;
			case Task::ApplyReplacements: // -a -l (list all proofs)
				tasks.back().bln["listAll"] = true;
				break;
			case Task::TransformProofSummary: // --transform -l <limit or -1> (abort computation when combined requested proof sequences exceed the given limit in bytes)
			case Task::UnfoldProofSummary: //       --unfold -l <limit or -1> (abort computation when combined requested proof sequences exceed the given limit in bytes)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["maxLengthToComputeDProof"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			case Task::ExtractFromProofFiles: // --extract -l <limit or -1> (similar to '-#' ; copy proofs with conclusions that have symbolic lengths of at most the given number)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["maxConclusionLength"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["whether -l was called"] = true;
				break;
			}
			break;
		case 'n':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Customize: //                      -c -n (specify formulas in normal Polish notation)
			case Task::ParseAndPrintProofs: //       --parse -n (print formulas in normal Polish notation)
			case Task::TransformProofSummary: // --transform -n (specify and print formulas in normal Polish notation)
			case Task::UnfoldProofSummary: //       --unfold -n (specify formulas in normal Polish notation)
			case Task::SearchProofFiles: //         --search -n (specify formulas in normal Polish notation)
				tasks.back().bln["normalPolishNotation"] = true;
				break;
			}
			break;
		case 'N':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Customize: // -c -N <limit or -1> (enable necessitation rule)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["necessitationLimit"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			}
			break;
		case 'o':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::ParseAndPrintProofs: //       --parse -o <output file> (redirect the result's output to the specified file)
			case Task::TransformProofSummary: // --transform -o <output file> (redirect the result's output to the specified file)
			case Task::UnfoldProofSummary: //       --unfold -o <output file> (redirect the result's output to the specified file)
			case Task::ExtractFromProofFiles: //   --extract -o <output file> (specify output file path for '-t')
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["outputFile"] = argv[++i];
				tasks.back().bln["useOutputFile"] = true;
				break;
			case Task::FileConversion: // --variate -o <prefix> (customize output file path prefix in data location)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["outputFilePrefix"] = argv[++i];
				break;
			case Task::ConclusionLengthPlot: // --plot -o <output file> (print to given output file)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["mout"] = argv[++i];
				break;
			}
			break;
		case 'p':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::TransformProofSummary: // --transform -p <limit or -1> (only keep subproofs with primitive lengths not exceeding the given limit)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["maxLengthToKeepProof"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			case Task::SearchProofFiles: // --search -p (search proofs)
				tasks.back().bln["searchProofs"] = true;
				break;
			}
			break;
		case 'q':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Generate: // -g -q <limit> (limit number of proof candidate strings queued per worker thread)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["candidateQueueCapacities"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["whether -q was called"] = true;
				break;
			case Task::TransformProofSummary: // --transform -q (skip first round preparation for '-x')
				tasks.back().bln["compress_skip"] = true;
				break;
			}
			break;
		case 's':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Customize: // -c -s <string> (specify axioms by comma-separated string)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["axiomString"] = argv[++i];
				break;
			case Task::Generate: //                      -g -s (proof files without conclusions)
			case Task::AssessGeneration: //        --assess -s (use proof files without conclusions)
			case Task::IterateProofCandidates: // --iterate -s (use proof files without conclusions)
				tasks.back().bln["withConclusions"] = false;
				break;
			case Task::CreateReplacements: // -r -s (proof files without conclusions)
				tasks.back().bln["withConclusions"] = false;
				if (!tasks.back().bln["whether -i was called"])
					tasks.back().str["inputFilePrefix"] = "dProofs-withoutConclusions/dProofs";
				break;
			case Task::ApplyReplacements: // -a -s (style all proofs)
				tasks.back().bln["styleAll"] = true;
				break;
			case Task::ParseAndPrintProofs: // --parse -s (only print summary with conclusions and abstract condensed detachment proofs)
				tasks.back().bln["summaryMode"] = true;
				break;
			case Task::TransformProofSummary: // --transform -s <string> (list a subproof with its conclusion if it occurs in the given comma-separated list of conclusions)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["conclusionsWithHelperProofs"] = argv[++i];
				tasks.back().bln["whether -s was called"] = true;
				break;
			case Task::SearchProofFiles: // --search -s (search for schemas of the given formulas)
				tasks.back().bln["schemaSearch"] = true;
				break;
			case Task::ExtractFromProofFiles: // --extract -s (redundant schema removal for '-t')
				tasks.back().bln["allowRedundantSchemaRemoval"] = true;
				break;
			case Task::FileConversion: // --variate -s (only use data stored in-memory)
				tasks.back().bln["memoryOnly"] = true;
				break;
			case Task::ConclusionLengthPlot: // --plot -s (measure symbolic length)
				tasks.back().bln["measureSymbolicLength"] = true;
				break;
			case Task::MpiFilter: // -m -s (disable smooth progress mode)
				tasks.back().bln["smoothProgress"] = false;
				break;
			}
			break;
		case 't':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::TransformProofSummary: // --transform -t <string> (only transform proofs of specified theorems)
			case Task::UnfoldProofSummary: //       --unfold -t <string> (obtain proofs of specified theorems)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["filterForTheorems"] = argv[++i];
				tasks.back().bln["whether -t was called"] = true;
				break;
			case Task::SearchProofFiles: // --search -t (search for formulas of the given schemas)
				tasks.back().bln["abstractSearch"] = true;
				break;
			case Task::ExtractFromProofFiles: // --extract -t <limit or -1> (compose file with up to the given amount of smallest conclusions that occur in proof files)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["extractToFileAmount"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["whether -t was called"] = true;
				break;
			case Task::ConclusionLengthPlot: // --plot -t (table arrangement)
				tasks.back().bln["table"] = true;
				break;
			}
			break;
		case 'u':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::Generate: //                      -g -u (unfiltered)
			case Task::AssessGeneration: //        --assess -u (use unfiltered proof files)
			case Task::IterateProofCandidates: // --iterate -u (use unfiltered proof files)
				tasks.back().bln["redundantSchemaRemoval"] = false;
				break;
			case Task::ParseAndPrintProofs: // --parse -u (print formulas in infix notation with operators as Unicode characters)
				tasks.back().bln["unicodeInfixNotation"] = true;
				break;
			case Task::TransformProofSummary: // --transform -u (print formulas in infix notation with operators as Unicode characters)
				tasks.back().bln["printInfixUnicode"] = true;
				break;
			case Task::ConclusionLengthPlot: // --plot -u (include unfiltered proof files)
				tasks.back().bln["includeUnfiltered"] = true;
				break;
			}
			break;
		case 'v':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::TransformProofSummary: // --transform -v (coordinate iteration phases for maximum-size proofs generated via 'x' with the specified vault file)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["compress_vault"] = argv[++i];
				tasks.back().bln["whether -v was called"] = true;
				break;
			case Task::UnfoldProofSummary: // --unfold -v (read input without conclusions given)
				tasks.back().bln["noInputConclusions"] = true;
				break;
			}
			break;
		case 'w':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::ApplyReplacements: //        -a -w (wrap results)
			case Task::UnfoldProofSummary: // --unfold -w (wrap results)
				tasks.back().bln["wrap"] = true;
				break;
			case Task::TransformProofSummary: // --transform -w (read input without conclusions given)
				tasks.back().bln["noInputConclusions"] = true;
				break;
			case Task::SearchProofFiles: // --search -w (search whole collections of schemas)
				tasks.back().bln["multiSchemaSearch"] = true;
				break;
			}
			break;
		case 'x':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::TransformProofSummary: // --transform -x <limit> (proof compression with extended modification range)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["compress_range"] = stoll(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["compress"] = true;
				break;
			case Task::ConclusionLengthPlot: // --plot -x <limit or -1> (upper horizontal limit)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["cutX"] = stoll(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			}
			break;
		case 'y':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::TransformProofSummary: // --transform -y (disable multi-threaded D-rule replacement search in case proof compression is performed)
				tasks.back().bln["compress_concurrent"] = false;
				break;
			case Task::ConclusionLengthPlot: // --plot -y <limit or -1> (upper vertical limit)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["cutY"] = stoll(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				break;
			}
			break;
		case 'z':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::TransformProofSummary: // --transform -z (proof compression)
				tasks.back().bln["compress"] = true;
				break;
			case Task::ExtractFromProofFiles: // --extract -z (force redundant schema removal for '-t')
				tasks.back().bln["forceRedundantSchemaRemoval"] = true;
			}
			break;
		default:
			return printUsage("Invalid argument \"" + string { argv[i] } + "\".", recent());
		}
	}
	int mpi_size;
	int mpi_rank;
	if (!mpiArg.empty()) {
		if (tasks.size() > 1 + mpiIgnoreCount)
			return printUsage("Invalid argument \"" + mpiArg + "\": Can only be combined with preceding configuring commands.");

		// Initialize the MPI library.
		int provided;
		MPI_Init_thread(&argc, &argv, MPI_THREAD_FUNNELED, &provided);
		if (provided < MPI_THREAD_FUNNELED) {
			cerr << "Missing MPI support. (provided: " << provided << ", requested: " << MPI_THREAD_FUNNELED << ") Aborting." << endl;
			MPI_Finalize(); // Finalize the MPI library.
			return 0;
		}

		// Obtain the process ID and the number of processes
		MPI_Comm_size(MPI_COMM_WORLD, &mpi_size);
		MPI_Comm_rank(MPI_COMM_WORLD, &mpi_rank);
	}
	auto bstr = [](bool b) { return b ? "true" : "false"; };
	try {
		if (mpiArg.empty() || mpi_rank == 0) {
			stringstream ss;
			size_t index = 0;
			for (TaskInfo& t : tasks)
				switch (t.task) {
				default:
					throw logic_error("Invalid task.");
				case Task::Customize: // -c
					ss << ++index << ". resetRepresentativesFor(" << (t.bln["defaultSystem"] ? "null" : "\"" + (t.bln["useInputFile"] ? t.str["axiomFilePath"] : t.str["axiomString"]) + "\"") << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (unsigned) t.num["necessitationLimit"] << ", " << bstr(t.bln["speedupN"]) << (t.bln["extractedSystem"] ? ", \"" + t.str["extractedSystemId"] + "\"" : "") << ")\n";
					break;
				case Task::Generate: { // -g
					unsigned optParams = t.bln["useConclusionTrees"] ? 5 : t.bln["useConclusionStrings"] ? 4 : t.num["maxSymbolicConsequentLength"] != -1 ? 3 : t.num["maxSymbolicConclusionLength"] != -1 ? 2 : t.bln["whether -q was called"] ? 1 : 0;
					ss << ++index << ". generateDProofRepresentativeFiles(" << (unsigned) t.num["limit"] << ", " << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << (t.bln["whether -q was called"] ? string(", ") + to_string(size_t(t.num["candidateQueueCapacities"])) : optParams > 1 ? ", null" : "") << (t.num["maxSymbolicConclusionLength"] != -1 ? string(", ") + to_string(size_t(t.num["maxSymbolicConclusionLength"])) : optParams > 2 ? ", -1" : "") << (t.num["maxSymbolicConsequentLength"] != -1 ? string(", ") + to_string(size_t(t.num["maxSymbolicConsequentLength"])) : optParams > 3 ? ", -1" : "") << (t.bln["useConclusionStrings"] || optParams > 4 ? string(", ") + bstr(t.bln["useConclusionStrings"]) : "") << (t.bln["useConclusionTrees"] || optParams > 5 ? string(", ") + bstr(t.bln["useConclusionTrees"]) : "") << ")\n";
					break;
				}
				case Task::CreateReplacements: // -r
					ss << ++index << ". createReplacementsFile(\"" << t.str["dProofDB"] << "\", \"" << t.str["outputFile"] << "\", \"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", " << bstr(t.bln["withConclusions"]) << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::ApplyReplacements: // -a
					ss << ++index << ". applyReplacements(\"" << t.str["initials"] << "\", \"" << t.str["replacementsFile"] << "\", \"" << t.str["dProofDB"] << "\", \"" << t.str["outputFile"] << "\", " << bstr(t.bln["styleAll"]) << ", " << bstr(t.bln["listAll"]) << ", " << bstr(t.bln["wrap"]) << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::ParseAndPrintProofs: // --parse
					ss << ++index << ". printProofs(" << (t.bln["useInputFile"] ? "{ }" : "\"" + t.str["string"] + "\"") << ", " << (t.bln["normalPolishNotation"] ? "DlFormulaStyle::PolishStandard" : t.bln["unicodeInfixNotation"] ? "DlFormulaStyle::InfixUnicode" : "DlFormulaStyle::PolishNumeric") << ", " << bstr(t.bln["conclusionsOnly"]) << ", " << bstr(t.bln["summaryMode"]) << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << (t.bln["useInputFile"] ? "\"" + t.str["string"] + "\"" : "null") << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::TransformProofSummary: // --transform
					ss << ++index << ". recombineProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << (t.bln["whether -s was called"] ? "\"" + t.str["conclusionsWithHelperProofs"] + "\"" : "null") << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << (size_t) t.num["maxLengthToKeepProof"] << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << bstr(t.bln["printInfixUnicode"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["removeDuplicateConclusions"]) << ", " << bstr(t.bln["compress"]) << ", " << bstr(t.bln["noInputConclusions"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ", " << bstr(t.bln["compress_concurrent"]) << ", " << t.num["compress_range"] << ", " << bstr(t.bln["compress_keep"]) << ", " << (t.bln["whether -v was called"] ? "\"" + t.str["compress_vault"] + "\"" : "null") << ", " << bstr(t.bln["compress_sureSaves"]) << ", " << bstr(t.bln["compress_skip"]) << ")\n";
					break;
				case Task::UnfoldProofSummary: // --unfold
					ss << ++index << ". unfoldProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["wrap"]) << ", " << bstr(t.bln["noInputConclusions"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::SearchProofFiles: // --search
					ss << ++index << ". searchProofFiles(" << (t.bln["useInputFile"] ? "{ }" : "\"" + t.str["string"] + "\"") << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << bstr(t.bln["searchProofs"]) << ", " << (t.bln["multiSchemaSearch"] ? 2 : t.bln["schemaSearch"] ? 1 : t.bln["abstractSearch"] ? 3 : 0) << ", " << (t.bln["useInputFile"] ? "\"" + t.str["string"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::ExtractFromProofFiles: // --extract
					if (t.bln["whether -t was called"])
						ss << ++index << ". extractConclusions(ExtractionMethod::TopListFile, " << (unsigned) t.num["extractToFileAmount"] << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["allowRedundantSchemaRemoval"]) << ", " << bstr(t.bln["forceRedundantSchemaRemoval"]) << ", 0, 0, " << bstr(t.bln["debug"]) << ")\n";
					if (t.bln["whether -# was called"])
						ss << ++index << ". extractConclusions(ExtractionMethod::ProofSystemFromTopList, " << (unsigned) t.num["extractToSystemAmount"] << ", null, true, false, 0, 0, " << bstr(t.bln["debug"]) << ")\n";
					if (t.bln["whether -h was called"])
						ss << ++index << ". extractConclusions(" << (t.bln["useInputFile"] ? "ExtractionMethod::ProofSystemFromFile" : "ExtractionMethod::ProofSystemFromString") << ", 0, \"" << t.str["proofs"] << "\", true, false, 0, 0, " << bstr(t.bln["debug"]) << ")\n";
					if (t.bln["whether -l was called"] || t.bln["whether -k was called"])
						ss << ++index << ". extractConclusions(ExtractionMethod::CopyWithLimitedConclusions" << ", 0, null, true, false, " << (t.bln["whether -l was called"] ? to_string((size_t) t.num["maxConclusionLength"]) : "-1") << ", " << (t.bln["whether -k was called"] ? to_string((size_t) t.num["maxConsequentLength"]) : "-1") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::AssessGeneration: // --assess
					ss << ++index << ". printGenerationExpenditures(" << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::IterateProofCandidates: // --iterate
					ss << ++index << ". countNextIterationAmount(" << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << ")\n";
					break;
				case Task::FileConversion: // --variate
					if (t.bln["with"])
						ss << ++index << ". createGeneratorFilesWithConclusions(\"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", \"" << t.str["outputFilePrefix"] << "\", " << bstr(t.bln["memoryOnly"]) << ", " << bstr(t.bln["debug"]) << ")\n";
					else
						ss << ++index << ". createGeneratorFilesWithoutConclusions(\"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", \"" << t.str["outputFilePrefix"] << "\", " << bstr(t.bln["memoryOnly"]) << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::ConclusionLengthPlot: // --plot
					ss << ++index << ". printConclusionLengthPlotData(" << bstr(t.bln["measureSymbolicLength"]) << ", " << bstr(t.bln["table"]) << ", " << t.num["cutX"] << ", " << t.num["cutY"] << ", \"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", " << bstr(t.bln["includeUnfiltered"]) << ", " << (t.str["mout"].empty() ? "null" : "\"" + t.str["mout"] + "\"") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::MpiFilter: // -m
					ss << ++index << ". mpi_filterDProofRepresentativeFile(" << (unsigned) t.num["wordLengthLimit"] << ", " << bstr(t.bln["smoothProgress"]) << ")\n";
					break;
				}
			cout << "Tasks:\n" << ss.str() << endl;
		}
		for (TaskInfo& t : tasks)
			switch (t.task) {
			default:
				throw logic_error("Invalid task.");
			case Task::Customize: { // -c [-i <file>] [-s <string>] [-n] [-N <limit or -1>] [-l] [-e <id>] [-d]
				vector<string> axioms;
				if (t.bln["useInputFile"]) {
					string axiomString;
					if (!FctHelper::readFile(t.str["axiomFilePath"], axiomString))
						throw runtime_error("Failed to read file \"" + t.str["axiomFilePath"] + "\".");
					axioms = FctHelper::stringSplitAndSkip(axiomString, "\n", "%", true);
				} else
					axioms = FctHelper::stringSplit(t.str["axiomString"], ",");
				if (mpiArg.empty()) {
					cout << "[Main] Calling resetRepresentativesFor(" << (t.bln["defaultSystem"] ? "null" : "\"" + (t.bln["useInputFile"] ? t.str["axiomFilePath"] : t.str["axiomString"]) + "\"") << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (unsigned) t.num["necessitationLimit"] << ", " << bstr(t.bln["speedupN"]) << (t.bln["extractedSystem"] ? ", \"" + t.str["extractedSystemId"] + "\"" : "") << ")." << endl;
					if (!DlProofEnumerator::resetRepresentativesFor(t.bln["defaultSystem"] ? nullptr : &axioms, t.bln["normalPolishNotation"], (unsigned) t.num["necessitationLimit"], t.bln["speedupN"], t.bln["extractedSystem"] ? &t.str["extractedSystemId"] : nullptr))
						throw domain_error("The axiomatic system could not be modified.");
				} else { // MPI-capable variant - allows multiple processes with a single (console and file) output - used only when called in combination with a (standalone) MPI command.
					stringstream ss;
					ss << "[Rank " << mpi_rank << " ; pid: " << getpid() << " ; " << mpi_size << " process" << (mpi_size == 1 ? "" : "es") << "] Calling resetRepresentativesFor(" << (t.bln["defaultSystem"] ? "null" : "\"" + (t.bln["useInputFile"] ? t.str["axiomFilePath"] : t.str["axiomString"]) + "\"") << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (unsigned) t.num["necessitationLimit"] << ", " << bstr(t.bln["speedupN"]) << (t.bln["extractedSystem"] ? ", \"" + t.str["extractedSystemId"] + "\"" : "") << ")" << (mpi_rank ? ", silently" : "") << ".";
					if (!mpi_rank) {
						cout << ss.str() << endl;
						if (!DlProofEnumerator::resetRepresentativesFor(t.bln["defaultSystem"] ? nullptr : &axioms, t.bln["normalPolishNotation"], (unsigned) t.num["necessitationLimit"], t.bln["speedupN"], t.bln["extractedSystem"] ? &t.str["extractedSystemId"] : nullptr)) {
							cerr << "[Rank " + to_string(mpi_rank) + " ; pid: " + to_string(getpid()) + " ; " + to_string(mpi_size) + " process" + (mpi_size == 1 ? "" : "es") + "] The axiomatic system could not be modified." << endl;
							MPI_Abort(MPI_COMM_WORLD, 1);
							return 1;
						}
					}
					MPI_Barrier(MPI_COMM_WORLD); // allow potential file initializations only by the main process
					if (mpi_rank) {
						cout << ss.str() << endl;
						stringstream ss_err;
						if (!DlProofEnumerator::resetRepresentativesFor(t.bln["defaultSystem"] ? nullptr : &axioms, t.bln["normalPolishNotation"], (unsigned) t.num["necessitationLimit"], t.bln["speedupN"], t.bln["extractedSystem"] ? &t.str["extractedSystemId"] : nullptr, nullptr, &ss_err)) {
							cerr << "[Rank " + to_string(mpi_rank) + " ; pid: " + to_string(getpid()) + " ; " + to_string(mpi_size) + " process" + (mpi_size == 1 ? "" : "es") + "] The axiomatic system could not be modified:\n" + ss_err.str() << endl;
							MPI_Abort(MPI_COMM_WORLD, 1);
							return 1;
						}
					}
					MPI_Barrier(MPI_COMM_WORLD); // do not mix up with subsequent commands
				}
				break;
			}
			case Task::Generate: { // -g <limit or -1> [-u] [-q <limit>] [-l <limit or -1>] [-k <limit or -1>] [-b] [-f] [-s]
				unsigned optParams = t.bln["useConclusionTrees"] ? 5 : t.bln["useConclusionStrings"] ? 4 : t.num["maxSymbolicConsequentLength"] != -1 ? 3 : t.num["maxSymbolicConclusionLength"] != -1 ? 2 : t.bln["whether -q was called"] ? 1 : 0;
				cout << "[Main] Calling generateDProofRepresentativeFiles(" << (unsigned) t.num["limit"] << ", " << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << (t.bln["whether -q was called"] ? string(", ") + to_string(size_t(t.num["candidateQueueCapacities"])) : optParams > 1 ? ", null" : "") << (t.num["maxSymbolicConclusionLength"] != -1 ? string(", ") + to_string(size_t(t.num["maxSymbolicConclusionLength"])) : optParams > 2 ? ", -1" : "") << (t.num["maxSymbolicConsequentLength"] != -1 ? string(", ") + to_string(size_t(t.num["maxSymbolicConsequentLength"])) : optParams > 3 ? ", -1" : "") << (t.bln["useConclusionStrings"] || optParams > 4 ? string(", ") + bstr(t.bln["useConclusionStrings"]) : "") << (t.bln["useConclusionTrees"] || optParams > 5 ? string(", ") + bstr(t.bln["useConclusionTrees"]) : "") << ")." << endl;
				size_t candidateQueueCapacities = static_cast<size_t>(t.num["candidateQueueCapacities"]);
				DlProofEnumerator::generateDProofRepresentativeFiles((unsigned) t.num["limit"], t.bln["redundantSchemaRemoval"], t.bln["withConclusions"], t.bln["whether -q was called"] ? &candidateQueueCapacities : nullptr, t.num["maxSymbolicConclusionLength"], t.num["maxSymbolicConsequentLength"], t.bln["useConclusionStrings"], t.bln["useConclusionTrees"]);
				break;
			}
			case Task::CreateReplacements: // -r <D-proof database> <output file> [-l <path>] [-i <prefix>] [-s] [-d]
				cout << "[Main] Calling createReplacementsFile(\"" << t.str["dProofDB"] << "\", \"" << t.str["outputFile"] << "\", \"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", " << bstr(t.bln["withConclusions"]) << ", " << bstr(t.bln["debug"]) << ")." << endl;
				DRuleReducer::createReplacementsFile(t.str["dProofDB"], t.str["outputFile"], t.str["dataLocation"], t.str["inputFilePrefix"], t.bln["withConclusions"], t.bln["debug"]);
				break;
			case Task::ApplyReplacements: // -a <initials> <replacements file> <D-proof database> <output file> [-s] [-l] [-w] [-d]
				cout << "[Main] Calling applyReplacements(\"" << t.str["initials"] << "\", \"" << t.str["replacementsFile"] << "\", \"" << t.str["dProofDB"] << "\", \"" << t.str["outputFile"] << "\", " << bstr(t.bln["styleAll"]) << ", " << bstr(t.bln["listAll"]) << ", " << bstr(t.bln["wrap"]) << ", " << bstr(t.bln["debug"]) << ")." << endl;
				DRuleReducer::applyReplacements(t.str["initials"], t.str["replacementsFile"], t.str["dProofDB"], t.str["outputFile"], t.bln["styleAll"], t.bln["listAll"], t.bln["wrap"], t.bln["debug"]);
				break;
			case Task::ParseAndPrintProofs: // --parse <string> [-n] [-u] [-j <limit or -1>] [-b] [-s] [-e] [-f] [-o <output file>] [-d]
				cout << "[Main] Calling printProofs(" << (t.bln["useInputFile"] ? "{ }" : "\"" + t.str["string"] + "\"") << ", " << (t.bln["normalPolishNotation"] ? "DlFormulaStyle::PolishStandard" : t.bln["unicodeInfixNotation"] ? "DlFormulaStyle::InfixUnicode" : "DlFormulaStyle::PolishNumeric") << ", " << bstr(t.bln["conclusionsOnly"]) << ", " << bstr(t.bln["summaryMode"]) << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << (t.bln["useInputFile"] ? "\"" + t.str["string"] + "\"" : "null") << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				DlProofEnumerator::printProofs(t.bln["useInputFile"] ? vector<string> { } : FctHelper::stringSplit(t.str["string"], ","), t.bln["normalPolishNotation"] ? DlFormulaStyle::PolishStandard : t.bln["unicodeInfixNotation"] ? DlFormulaStyle::InfixUnicode : DlFormulaStyle::PolishNumeric, t.bln["conclusionsOnly"], t.bln["summaryMode"], (unsigned) t.num["minUseAmountToCreateHelperProof"], t.bln["abstractProofStrings"], t.bln["useInputFile"] ? &t.str["string"] : nullptr, t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["debug"]);
				break;
			case Task::TransformProofSummary: // --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-u] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-b] [-w] [-z] [-x <limit>] [-y] [-k] [-v <file>] [-h] [-q] [-f] [-o <output file>] [-d]
				cout << "[Main] Calling recombineProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << (t.bln["whether -s was called"] ? "\"" + t.str["conclusionsWithHelperProofs"] + "\"" : "null") << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << (size_t) t.num["maxLengthToKeepProof"] << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << bstr(t.bln["printInfixUnicode"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["removeDuplicateConclusions"]) << ", " << bstr(t.bln["compress"]) << ", " << bstr(t.bln["noInputConclusions"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ", " << bstr(t.bln["compress_concurrent"]) << ", " << t.num["compress_range"] << ", " << bstr(t.bln["compress_keep"]) << ", " << (t.bln["whether -v was called"] ? "\"" + t.str["compress_vault"] + "\"" : "null") << ", " << bstr(t.bln["compress_sureSaves"]) << ", " << bstr(t.bln["compress_skip"]) << ")." << endl;
				if (!t.bln["useInputFile"])
					boost::replace_all(t.str["string"], ",", "\n");
				DlProofEnumerator::recombineProofSummary(t.str["string"], t.bln["useInputFile"], t.bln["whether -s was called"] ? &t.str["conclusionsWithHelperProofs"] : nullptr, (unsigned) t.num["minUseAmountToCreateHelperProof"], t.num["maxLengthToKeepProof"], t.bln["normalPolishNotation"], t.bln["printInfixUnicode"], t.bln["whether -t was called"] ? &t.str["filterForTheorems"] : nullptr, t.bln["abstractProofStrings"], t.num["storeIntermediateUnfoldingLimit"], t.num["maxLengthToComputeDProof"], t.bln["removeDuplicateConclusions"], t.bln["compress"], t.bln["noInputConclusions"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["debug"], t.bln["compress_concurrent"], t.num["compress_range"], t.bln["compress_keep"], t.bln["whether -v was called"] ? &t.str["compress_vault"] : nullptr, t.bln["compress_sureSaves"], t.bln["compress_skip"]);
				break;
			case Task::UnfoldProofSummary: // --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-v] [-f] [-o <output file>] [-d]
				cout << "[Main] Calling unfoldProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["wrap"]) << ", " << bstr(t.bln["noInputConclusions"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				if (!t.bln["useInputFile"])
					boost::replace_all(t.str["string"], ",", "\n");
				DlProofEnumerator::unfoldProofSummary(t.str["string"], t.bln["useInputFile"], t.bln["normalPolishNotation"], t.bln["whether -t was called"] ? &t.str["filterForTheorems"] : nullptr, t.num["storeIntermediateUnfoldingLimit"], t.num["maxLengthToComputeDProof"], t.bln["wrap"], t.bln["noInputConclusions"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["debug"]);
				break;
			case Task::SearchProofFiles: // --search <string> [-n] [-s] [-w] [-t] [-p] [-f] [-d]
				cout << "[Main] Calling searchProofFiles(" << (t.bln["useInputFile"] ? "{ }" : "\"" + t.str["string"] + "\"") << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["multiSchemaSearch"] ? 2 : t.bln["schemaSearch"] ? 1 : t.bln["abstractSearch"] ? 3 : 0) << ", " << bstr(t.bln["schemaSearch"]) << ", " << (t.bln["useInputFile"] ? "\"" + t.str["string"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				DlProofEnumerator::searchProofFiles(t.bln["useInputFile"] ? vector<string> { } : FctHelper::stringSplit(t.str["string"], ","), t.bln["normalPolishNotation"], t.bln["searchProofs"], t.bln["multiSchemaSearch"] ? 2 : t.bln["schemaSearch"] ? 1 : t.bln["abstractSearch"] ? 3 : 0, t.bln["useInputFile"] ? &t.str["string"] : nullptr , t.bln["debug"]);
				break;
			case Task::ExtractFromProofFiles: // --extract [-t <limit or -1>] [-o <output file>] [-s] [-z] [-# <amount up to 35>] [-h <string>] [-l <limit or -1>] [-k <limit or -1>] [-f] [-d]
				if (t.bln["whether -t was called"]) {
					cout << "[Main] Calling extractConclusions(ExtractionMethod::TopListFile, " << (unsigned) t.num["extractToFileAmount"] << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["allowRedundantSchemaRemoval"]) << ", " << bstr(t.bln["forceRedundantSchemaRemoval"]) << ", 0, 0, " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::extractConclusions(ExtractionMethod::TopListFile, (unsigned) t.num["extractToFileAmount"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["allowRedundantSchemaRemoval"], t.bln["forceRedundantSchemaRemoval"], 0, 0, t.bln["debug"]);
				}
				if (t.bln["whether -# was called"]) {
					cout << "[Main] Calling extractConclusions(ExtractionMethod::ProofSystemFromTopList, " << (unsigned) t.num["extractToSystemAmount"] << ", null, true, false, 0, 0, " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::extractConclusions(ExtractionMethod::ProofSystemFromTopList, (unsigned) t.num["extractToSystemAmount"], nullptr, true, false, 0, 0, t.bln["debug"]);
				}
				if (t.bln["whether -h was called"]) {
					cout << "[Main] Calling extractConclusions(" << (t.bln["useInputFile"] ? "ExtractionMethod::ProofSystemFromFile" : "ExtractionMethod::ProofSystemFromString") << ", 0, \"" << t.str["proofs"] << "\", true, false, 0, 0, " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::extractConclusions(t.bln["useInputFile"] ? ExtractionMethod::ProofSystemFromFile : ExtractionMethod::ProofSystemFromString, 0, &t.str["proofs"], true, false, 0, 0, t.bln["debug"]);
				}
				if (t.bln["whether -l was called"] || t.bln["whether -k was called"]) {
					cout << "[Main] Calling extractConclusions(ExtractionMethod::CopyWithLimitedConclusions" << ", 0, null, true, false, " << (t.bln["whether -l was called"] ? to_string((size_t) t.num["maxConclusionLength"]) : "-1") << ", " << (t.bln["whether -k was called"] ? to_string((size_t) t.num["maxConsequentLength"]) : "-1") << ", " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::extractConclusions(ExtractionMethod::CopyWithLimitedConclusions, 0, nullptr, true, false, t.bln["whether -l was called"] ? t.num["maxConclusionLength"] : -1, t.bln["whether -k was called"] ? t.num["maxConsequentLength"] : -1, t.bln["debug"]);
				}
				break;
			case Task::AssessGeneration: // --assess [-u] [-s] [-d]
				cout << "[Main] Calling printGenerationExpenditures(" << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << ", " << bstr(t.bln["debug"]) << ")." << endl;
				DlProofEnumerator::printGenerationExpenditures(t.bln["redundantSchemaRemoval"], t.bln["withConclusions"], t.bln["debug"]);
				break;
			case Task::IterateProofCandidates: // --iterate [-u] [-s]
				cout << "[Main] Calling countNextIterationAmount(" << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << ")." << endl;
				DlProofEnumerator::countNextIterationAmount(t.bln["redundantSchemaRemoval"], t.bln["withConclusions"]);
				break;
			case Task::FileConversion: // --variate ( 0 | 1 ) [-l <path>] [-i <prefix>] [-o <prefix>] [-s] [-d]
				if (t.bln["with"]) {
					cout << "[Main] Calling createGeneratorFilesWithConclusions(\"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", \"" << t.str["outputFilePrefix"] << "\", " << bstr(t.bln["memoryOnly"]) << ", " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::createGeneratorFilesWithConclusions(t.str["dataLocation"], t.str["inputFilePrefix"], t.str["outputFilePrefix"], t.bln["memoryOnly"], t.bln["debug"]);
				} else {
					cout << "[Main] Calling createGeneratorFilesWithoutConclusions(\"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", \"" << t.str["outputFilePrefix"] << "\", " << bstr(t.bln["memoryOnly"]) << ", " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::createGeneratorFilesWithoutConclusions(t.str["dataLocation"], t.str["inputFilePrefix"], t.str["outputFilePrefix"], t.bln["memoryOnly"], t.bln["debug"]);
				}
				break;
			case Task::ConclusionLengthPlot: // --plot [-l <path>] [-i <prefix>] [-s] [-t] [-x <limit or -1>] [-y <limit or -1>] [-o <output file>] [-d]
				cout << "[Main] Calling printConclusionLengthPlotData(" << bstr(t.bln["measureSymbolicLength"]) << ", " << bstr(t.bln["table"]) << ", " << t.num["cutX"] << ", " << t.num["cutY"] << ", \"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", " << bstr(t.bln["includeUnfiltered"]) << ", " << (t.str["mout"].empty() ? "null" : "\"" + t.str["mout"] + "\"") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				if (t.str["mout"].empty())
					DlProofEnumerator::printConclusionLengthPlotData(t.bln["measureSymbolicLength"], t.bln["table"], t.num["cutX"], t.num["cutY"], t.str["dataLocation"], t.str["inputFilePrefix"], t.bln["includeUnfiltered"], nullptr, t.bln["debug"]);
				else {
					string path = t.str["mout"];
					FctHelper::ensureDirExists(path);
					ofstream fout(filesystem::u8path(path), fstream::out | fstream::binary);
					if (!fout.is_open())
						throw invalid_argument("Cannot write to file \"" + path + "\".");
					DlProofEnumerator::printConclusionLengthPlotData(t.bln["measureSymbolicLength"], t.bln["table"], t.num["cutX"], t.num["cutY"], t.str["dataLocation"], t.str["inputFilePrefix"], t.bln["includeUnfiltered"], &fout, t.bln["debug"]);
				}
				break;
			case Task::MpiFilter: // -m <limit> [-s]
				stringstream ss;
				ss << "[Rank " << mpi_rank << " ; pid: " << getpid() << " ; " << mpi_size << " process" << (mpi_size == 1 ? "" : "es") << "] Calling mpi_filterDProofRepresentativeFile(" << (unsigned) t.num["wordLengthLimit"] << ", " << bstr(t.bln["smoothProgress"]) << ").";
				cout << ss.str() << endl;
				DlProofEnumerator::mpi_filterDProofRepresentativeFile((unsigned) t.num["wordLengthLimit"], t.bln["smoothProgress"]);
				break;
			}
	} catch (exception& e) {
		cerr << "ERROR exception thrown: " << e.what() << endl;
	}
	if (!mpiArg.empty())
		MPI_Finalize(); // Finalize the MPI library.
	return 0;
}
