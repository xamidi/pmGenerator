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

//#include <tbb/concurrent_map.h>
//#include <tbb/parallel_for.h>

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
				"    --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-u] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-b] [-z] [-y] [-f] [-o <output file>] [-d]\n"
				"       Transform proof summary (as by '--parse [...] -s') into recombined variant ; ignores configured system (proof summaries provide their own axioms) ; \",\" represents LF\n"
				"         -s: list a subproof with its conclusion if it occurs in the given comma-separated list of conclusions\n"
				"         -j: join common subproofs together when they are used at least a given amount of times ; default: 2\n"
				"         -p: only keep subproofs with primitive lengths not exceeding the given limit ; default: -1\n"
				"         -n: specify and print formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -u: print formulas in infix notation with operators as Unicode characters ; does not affect input format (for which '-n' can still be specified)\n"
				"         -t: only transform proofs of specified theorems (proven by subsequences of the input), given by a comma-separated string ; \".\" to keep all conclusions ; default: final theorem only\n"
				"         -e: keep expanded proof strings ; show fully detailed condensed detachment proofs rather than allowing them to contain references\n"
				"         -i: decrease memory requirements but increase time consumption by not storing intermediate unfoldings that exceed a certain length ; default: -1\n"
				"         -l: abort computation when combined requested proof sequences exceed the given limit in bytes ; default: 134217728 (i.e. 128 MiB)\n"
				"         -b: duplicate conclusion removal ; replace each given subproof that has a redundant conclusion with its first shortest alternative and remove duplicates ; beneficial in preparing '-z'\n"
				"         -z: proof compression ; find and remove internal redundancies (e.g. non-trivial parts not affecting intermediate theorems) by attempting to use shorter owned subproofs at all positions\n"
				"         -y: disable multi-threaded D-rule replacement search in case proof compression is performed (enables deterministic solution procedure)\n"
				"         -f: proof summary is given by input file path ; ignores lines that are empty or starting with '%'\n"
				"         -o: redirect the result's output to the specified file\n"
				"         -d: print debug information\n";
		_[Task::UnfoldProofSummary] =
				"    --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-f] [-o <output file>] [-d]\n"
				"       Break down proof summary (as by '--parse [...] -s') into primitive steps ; ignores configured system (proof summaries provide their own axioms) ; \",\" represents LF\n"
				"         -n: specify formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -t: obtain proofs of specified theorems (proven by subsequences of the input), given by a comma-separated string ; \".\" to obtain a proof for each conclusion ; default: final theorem only\n"
				"         -i: decrease memory requirements but increase time consumption by not storing intermediate unfoldings that exceed a certain length ; default: -1\n"
				"         -l: abort computation when combined requested proof sequences exceed the given limit in bytes ; default: 134217728 (i.e. 128 MiB)\n"
				"         -w: wrap results\n"
				"         -f: proof summary is given by input file path ; ignores lines that are empty or starting with '%'\n"
				"         -o: redirect the result's output to the specified file\n"
				"         -d: print debug information\n";
		_[Task::SearchProofFiles] =
				"    --search <string> [-n] [-s] [-w] [-t] [-p] [-f] [-d]\n"
				"       Search in proof files at ./data/[<hash>/]/dProofs-withConclusions/ via comma-separated string of full formulas or full proofs ; [Hint: Generate missing files with '--variate 1 -s'.]\n"
				"         -n: specify formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -s: search for schemas of the given formulas\n"
				"         -w: search whole collections of schemas (i.e. enable multiple results per term) ; entails '-s'\n"
				"         -t: search for formulas of the given schemas (allows multiple results per term) ; used only when '-s' unspecified\n"
				"         -p: search proofs (rather than conclusions) ; used only when '-n', '-s' and '-t' unspecified\n"
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

#if 0
#include "logic/DlCore.h"
#include "tree/TreeNode.h"
string prover9Formula(const string& theorem, bool showLabel = false, bool printDot = true, bool TPTPConvention = false) {
	shared_ptr<DlFormula> consequent;
	if (!DlCore::fromPolishNotation(consequent, theorem)) {
		cerr << "Failed to parse " << theorem << "." << endl;
		return 0;
	}

	static const unordered_map<string, string> operatorNames = { { DlCore::terminalStr_and(), "K" }, { DlCore::terminalStr_or(), "A" }, { DlCore::terminalStr_nand(), "D" }, { DlCore::terminalStr_nor(), "X" }, { DlCore::terminalStr_imply(), "i" }, { DlCore::terminalStr_implied(), "B" }, { DlCore::terminalStr_nimply(), "F" }, { DlCore::terminalStr_nimplied(), "G" }, { DlCore::terminalStr_equiv(), "E" }, { DlCore::terminalStr_xor(), "J" }, { DlCore::terminalStr_com(), "S" }, { DlCore::terminalStr_app(), "U" }, { DlCore::terminalStr_not(), "n" }, { DlCore::terminalStr_nece(), "L" }, { DlCore::terminalStr_poss(), "M" }, { DlCore::terminalStr_obli(), "Z" }, { DlCore::terminalStr_perm(), "P" }, { DlCore::terminalStr_top(), "V" }, { DlCore::terminalStr_bot(), "O" } };
	map<string, string> operatorTranslations;
	map<string, string> variableTranslations;
	unsigned next = 0;
	auto recurse = [&](const shared_ptr<DlFormula>& node, const auto& me) -> string {
		auto valToString = [&](const string& s) -> string {
			// 1. Operator names
			map<string, string>::const_iterator itOperator = operatorTranslations.find(s);
			if (itOperator == operatorTranslations.end()) {
				unordered_map<string, string>::const_iterator searchResult = operatorNames.find(s);
				if (searchResult != operatorNames.end())
					return operatorTranslations[s] = searchResult->second;
			} else
				return itOperator->second;
			if (DlCore::dlOperators().count(s))
				return operatorTranslations[s] = "<" + s + ">"; // unsupported operator

			// 2. Variable names
			map<string, string>::const_iterator itVariable = variableTranslations.find(s);
			if (itVariable == variableTranslations.end())
				return variableTranslations[s] = (TPTPConvention ? "X" : "x") + to_string(next++);
			else
				return itVariable->second;
		};
		string str = valToString(node->getValue()->value);
		bool leaf = node->getChildren().empty();
		if (!leaf)
			str += "(";
		bool first= true;
		for (size_t i = 0; i < node->getChildren().size(); i++) {
			if (first)
				first = false;
			else
				str += ",";
			str += me(node->getChildren()[i], me);
		}
		return str + (leaf ? "" : ")");
	};
	return "t(" + recurse(consequent, recurse) + ")" + (showLabel ? " #label(" + theorem + ")" : "") + (printDot ? "." : "");
}
#endif

//#include <regex>
//#include <numeric>
//#include <cmath>
int main(int argc, char* argv[]) { // argc = 1 + N, argv = { <command>, <arg1>, ..., <argN> }
#if 0 //### ./CNFFromTopList ; create proof databases from smallest conclusion lists in TPTP's CNF format
	// e.g. ./CNFFromTopList CpCCqCprCCNrCCNstqCsr data/db25c49b13fec26ecf32e40bde65e4e2273f23b3c022cfd0fa986cff/top1000SmallestConclusions_1to43Steps.txt data/w2-top1000-cnf.txt
	if (argc <= 3) {
		cerr << "Need 1. axioms in normal Polish notation, 2. comma-separated list of paths to smallest conclusion list files, and 3. path for output file. Optional: 4. minimal proof length, 5. minimal conclusion length" << endl;
		return 0;
	}
	size_t minProofLen = 0;
	if (argc >= 5) {
		try {
			minProofLen = stoll(argv[4]);
			cout << "Minimal proof length set to " << minProofLen << "." << endl;
		} catch (...) {
			cerr << "Invalid format for \"4. minimal proof length\"." << endl;
			return 0;
		}
	}
	size_t minConcLen = 0;
	if (argc >= 6) {
		try {
			minConcLen = stoll(argv[5]);
			cout << "Minimal conclusion length set to " << minConcLen << "." << endl;
		} catch (...) {
			cerr << "Invalid format for \"5. minimal conclusion length\"." << endl;
			return 0;
		}
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	DlProofEnumerator::resetRepresentativesFor(&axioms, true);

	vector<string> inputFiles = FctHelper::stringSplit(argv[2], ",");
	string outputFile = argv[3];
	vector<string> contents(inputFiles.size());
	size_t i = 0;
	for (const string& inputFile : inputFiles) {
		if (!FctHelper::readFile(inputFile, contents[i])) {
			cerr << "Invalid file path \"" << inputFile << "\"" << endl;
			return 0;
		}
		i++;
	}

	//map<string, string, cmpStringGrow> dProofsWithConclusions;
	map<string, string, cmpStringGrow> conclusionsWithDProofs;
	for (const string& content : contents)
		for (string line : FctHelper::stringSplitAndSkip(content, "\n", "%", true)) {
			string::size_type posA = line.find_first_not_of(' ', line.find(' ', line.find_first_not_of(' ', line.find(' ') + 1) + 1) + 1);
			string::size_type posB = line.find(' ', posA + 1);
			string conclusion = line.substr(posA, posB - posA);
			string::size_type posC = line.find_first_not_of(' ', posB + 1);
			string::size_type posD = line.find(':', posC + 1);
			string dProof = line.substr(posC, posD - posC);
			if (conclusion.length() >= minConcLen && dProof.length() >= minProofLen) {
#if 0			// filter for useful formulas
				bool use = false;
				{
					map<char, set<size_t>> occurrences;
					size_t i = 0;
					for (char c : conclusion) {
						occurrences[c].emplace(i);
						i++;
					}
					size_t goodVars = 0;
					for (const pair<const char, set<size_t>>& p : occurrences) {
						const set<size_t>& occurrence = p.second;
						char c = p.first;
						if ('a' <= c && c <= 'z' && occurrence.size() >= 2) {
							if (occurrence.size() >= 3 || *occurrence.begin() + 1 < *next(occurrence.begin()))
								goodVars++;
						}
						if (goodVars >= 3)
							use = true;
					}
				}
#else
				bool use = true;
#endif
				//dProofsWithConclusions.emplace(dProof, conclusion);
				if (use)
					conclusionsWithDProofs.emplace(conclusion, dProof);
			}
		}

	//size_t tmpI = 0;
	size_t c = 0;
	stringstream ss;
	for (const pair<const string, string>& p : conclusionsWithDProofs) {
		ss << "% " << p.first << " (" << p.first.length() << " symbols, " << p.second.length() << " step" << (p.second.length() == 1 ? "" : "s") << ")\n";
		ss << "cnf(eax" << c++ << ", axiom, " << prover9Formula(p.first, false, false, true) << " ).\n";
		//tmpI++;
		//if (tmpI > 5)
		//	exit(0);
	}
	FctHelper::writeToFile(outputFile, ss.str());

	return 0;
#endif //###
#if 0 //### ./DBExtractBySummary ; extract those proofs from a proof database which appear in a given proof summary
	// NOTE: Requires '#include "logic/DlCore.h"'.
	// e.g. ./DBExtractBySummary data/exs/m-topDB.txt data/m.txt data/exs/m-relevantDB.txt
	if (argc <= 3) {
		cerr << "Need 1. path to proof database (with conclusions commented in normal Polish notation), 2. path to proof summary, and 3. path for output file." << endl;
		return 0;
	}
	string proofDBFile = argv[1];
	string proofSummaryFile = argv[2];
	string outputFile = argv[3];

	// 1. Obtain all conclusions used by proof summary (i.e. all which are relevant).
	string filterForTheorems = ".";
	DlProofEnumerator::recombineProofSummary(proofSummaryFile, true, nullptr, 1, SIZE_MAX, true, false, &filterForTheorems, true, SIZE_MAX, 134217728, false, false, &outputFile, false);
	unordered_set<string> conclusions;
	vector<DRuleParser::AxiomInfo> customAxioms;
	{
		//vector<DRuleParser::AxiomInfo> customAxioms;
		vector<string> abstractDProof;
		vector<DRuleParser::AxiomInfo> requiredIntermediateResults;
		DlProofEnumerator::convertProofSummaryToAbstractDProof(outputFile, &customAxioms, &abstractDProof, &requiredIntermediateResults, true, true, false);
		//#cout << "abstractDProof = " << FctHelper::vectorString(abstractDProof) << endl;
		//#cout << "|abstractDProof| = " << abstractDProof.size() << endl;
		//#cout << "requiredIntermediateResults = " << FctHelper::vectorStringF(requiredIntermediateResults, [](const DRuleParser::AxiomInfo& ax) { return DlCore::toPolishNotation(ax.refinedAxiom); }) << endl;
		//#cout << "|requiredIntermediateResults| = " << requiredIntermediateResults.size() << endl;
		for (const DRuleParser::AxiomInfo& info : requiredIntermediateResults)
			conclusions.emplace(DlCore::toPolishNotation(info.refinedAxiom));
	}
	cout << "Found " << conclusions.size() << " relevant conclusions." << endl;

	vector<string> dProofNamesInFile;
	vector<string> dProofsInFile = DRuleParser::readFromMmsolitaireFile(proofDBFile, &dProofNamesInFile, true);

	// 2. Copy relevant conclusion's D-proofs into new proof database.
	vector<size_t> relevantIndices;
	string result;
	for (size_t i = 0; i < dProofNamesInFile.size(); i++) {
		string dProof = dProofsInFile[i];
		//vector<DProofInfo> rawParseData = DRuleParser::parseDProof_raw(dProof, &customAxioms);
		//const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
		//string f_ = DlCore::toPolishNotation(conclusion);
		string dProofName = dProofNamesInFile[i];
		string::size_type pos = dProofName.find("; ! ");
		if (pos == string::npos) {
			cerr << "Invalid DB file" << endl;
			return 0;
		}
		string::size_type posEnd = dProofName.find(' ', pos + 5);
		string f = dProofName.substr(pos + 4, posEnd == string::npos ? string::npos : posEnd - pos - 4);
		//if (f != f_) {
		//	cerr << "f: " << f << ", f_: " << f_ << ", for " << dProofNamesInFile[i] << endl;
		//	return 0;
		//}
		if (conclusions.count(f)) {
			result += DRuleParser::toDBProof(dProof, &customAxioms, posEnd == string::npos ? f : dProofName.substr(pos + 4)) + "\n";
			relevantIndices.push_back(i);
		}
	}
	cout << "Copied for " << relevantIndices.size() << " relevant indices: " << FctHelper::vectorString(relevantIndices) << endl;

	if (!FctHelper::writeToFile(outputFile, result))
		cerr << "Failed." << endl;
	else
		cout << result.length() << " bytes written to \"" << outputFile<< "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./DBFromTopList ; create proof databases from smallest conclusion lists
	if (argc <= 3) {
		cerr << "Need 1. axioms in normal Polish notation, 2. comma-separated list of paths to smallest conclusion list files, and 3. path for output file. Optional: 4. minimal proof length" << endl;
		return 0;
	}
	size_t minProofLen = 0;
	if (argc >= 5) {
		try {
			minProofLen = stoll(argv[4]);
			cout << "Minimal proof length set to " << minProofLen << "." << endl;
		} catch (...) {
			cerr << "Invalid format for \"4. minimal proof length\"." << endl;
			return 0;
		}
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	DlProofEnumerator::resetRepresentativesFor(&axioms, true);
	// default:
	// ./DBFromTopList CpCqp,CCpCqrCCpqCpr,CCNpNqCqp data/top1000SmallestConclusions_1to39Steps.txt data/topDB.txt
	// m:
	// ./DBFromTopList CCCCCpqCNrNsrtCCtpCsp data/478804cd4793bc7f87041d99326aff4595662146d8a68175dda22bed/top1000SmallestConclusions_1to83Steps.txt data/m-topDB.txt
	// ./DBFromTopList CCCCCpqCNrNsrtCCtpCsp "data/exs/m/top131032SmallestConclusions_1to133Steps.txt,data/exs/m/top15254SmallestConclusions_1to203Steps.txt" data/exs/m-topDB-exs.txt
	// w1:
	// ./DBFromTopList CCpCCNpqrCsCCNtCrtCpt data/02974777ff5f71e12ef58ccebedeef133584aad66e06a2a13b2b4b2c/top1000SmallestConclusions_1to161Steps.txt data/w1-topDB.txt
	// ./DBFromTopList CCpCCNpqrCsCCNtCrtCpt "data/exs/w1/top371445SmallestConclusions_1to211Steps.txt,data/exs/w1/top79976SmallestConclusions_1to337Steps.txt,data/exs/w1/top21935SmallestConclusions_1to433Steps.txt,data/exs/w1/top11238SmallestConclusions_1to491Steps.txt" data/exs/w1-topDB-exs.txt
	// w2:
	// ./DBFromTopList CpCCqCprCCNrCCNstqCsr data/db25c49b13fec26ecf32e40bde65e4e2273f23b3c022cfd0fa986cff/top1000SmallestConclusions_1to43Steps.txt data/w2-topDB.txt
	// ./DBFromTopList CpCCqCprCCNrCCNstqCsr "data/exs/w2/top100000SmallestConclusions_1to139Steps.txt,data/exs/w2/top100000SmallestConclusions_1to177Steps.txt,data/exs/w2/top63668SmallestConclusions_1to277Steps.txt,data/exs/w2/top15790SmallestConclusions_1to313Steps.txt,data/exs/w2/top13235SmallestConclusions_1to339Steps.txt" data/exs/w2-topDB-exs.txt
	// w3:
	// ./DBFromTopList CpCCNqCCNrsCptCCtqCrq data/0df075acc552c62513b49b6ed674bfcde1c1b018e532c665be229314/top1000SmallestConclusions_1to73Steps.txt data/w3-topDB.txt
	// ./DBFromTopList CpCCNqCCNrsCptCCtqCrq "data/exs/w3/top61944SmallestConclusions_1to159Steps.txt,data/exs/w3/top50818SmallestConclusions_1to231Steps.txt,data/exs/w3/top18515SmallestConclusions_1to257Steps.txt,data/exs/w3/top16062SmallestConclusions_1to277Steps.txt,data/exs/w3/top4006SmallestConclusions_1to309Steps.txt" data/exs/w3-topDB-exs.txt
	// w4:
	// ./DBFromTopList CpCCNqCCNrsCtqCCrtCrq data/fe7117b8aad7634fae344172b9fee05f77e5e23b035276b17d8c6ec9/top1000SmallestConclusions_1to169Steps.txt data/w4-topDB.txt
	// ./DBFromTopList CpCCNqCCNrsCtqCCrtCrq "data/exs/w4/top160102SmallestConclusions_1to261Steps.txt,data/exs/w4/top6717SmallestConclusions_1to495Steps.txt" data/exs/w4-topDB-exs.txt
	// w5:
	// ./DBFromTopList CCpqCCCrCstCqCNsNpCps data/1d5f27494b1a2312e223b7f8dd3551abf717590ceef694c08dcbed72/top1000SmallestConclusions_1to55Steps.txt data/w5-topDB.txt
	// ./DBFromTopList CCpqCCCrCstCqCNsNpCps "data/exs/w5/top684361SmallestConclusions_1to111Steps.txt,data/exs/w5/top100000SmallestConclusions_1to149Steps.txt,data/exs/w5/top100000SmallestConclusions_1to159Steps.txt,data/exs/w5/top135154SmallestConclusions_1to161Steps.txt" data/exs/w5-topDB-exs.txt
	// w6:
	// ./DBFromTopList CCCpqCCCNrNsrtCCtpCsp data/7f473b6ba952b3deadf36cd7f1c4b5286ef32fef64808d14fff70a69/top1000SmallestConclusions_1to95Steps.txt data/w6-topDB.txt
	// ./DBFromTopList CCCpqCCCNrNsrtCCtpCsp "data/exs/w6/top297996SmallestConclusions_1to149Steps.txt,data/exs/w6/top16393SmallestConclusions_1to327Steps.txt" data/exs/w6-topDB-exs.txt
	// S5:
	// ./DBFromTopList CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp data/d03a044ec35d4d9a3f6d0f5118bc4f8a02a08e61fe7815b2002d007f/top1000SmallestConclusions_1to30Steps.txt data/s5-topDB.txt
	// ./DBFromTopList CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp "data/exs/s5/top244329SmallestConclusions_1to45Steps.txt,data/exs/s5/top39663SmallestConclusions_1to85Steps.txt" data/exs/s5-topDB-exs.txt
	vector<string> inputFiles = FctHelper::stringSplit(argv[2], ",");
	string outputFile = argv[3];
	vector<string> contents(inputFiles.size());
	size_t i = 0;
	for (const string& inputFile : inputFiles) {
		if (!FctHelper::readFile(inputFile, contents[i])) {
			cerr << "Invalid file path \"" << inputFile << "\"" << endl;
			return 0;
		}
		i++;
	}
	set<string, cmpStringGrow> dProofs;
	for (const string& content : contents)
		for (string line : FctHelper::stringSplitAndSkip(content, "\n", "%", true)) {
			string::size_type posC = line.find_first_not_of(' ', line.find(' ', line.find_first_not_of(' ', line.find(' ', line.find_first_not_of(' ', line.find(' ') + 1) + 1) + 1) + 1) + 1);
			string::size_type posD = line.find(':', posC + 1);
			string dProof = line.substr(posC, posD - posC);
			if (dProof.length() >= minProofLen)
				dProofs.emplace(dProof);
		}
	//#cout << FctHelper::setString(dProofs) << endl;

	string result;
	for (const string& dProof : dProofs)
		result += DRuleParser::toDBProof(dProof, DlProofEnumerator::getCustomAxioms()) + "\n";
	if (!FctHelper::writeToFile(outputFile, result))
		cerr << "Failed." << endl;
	else
		cout << result.length() << " bytes written to \"" << outputFile<< "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./dProofsFromDB ; extract comma-separated list of proofs from all proofs explicitly given in a proof database
	// e.g. ./dProofsFromDB data/s5proofs.txt data/s5-dProofs.txt 1 1
	if (argc <= 2) {
		cerr << "Need 1. path to proof database and 2. path for output file. Optional: 3. whether to only keep unique proofs (default: 0), 4. whether to remove proofs of length 1 (which are invalid in abstract proofs, default: 0)" << endl;
		return 0;
	}
	string outputFile = argv[2];
	bool filter = false;
	bool removeTrivial = false;
	if (argc >= 4) {
		string s = argv[3];
		filter = (s != "0" && s != "false");
	}
	if (argc >= 5) {
		string s = argv[4];
		removeTrivial = (s != "0" && s != "false");
	}
	vector<string> dProofs = DRuleParser::readFromMmsolitaireFile(argv[1], nullptr, true);
	if (filter) {
		set<string> s;
		vector<string> uniqueDProofs;
		for (const string& dProof : dProofs)
			if (s.emplace(dProof).second)
				uniqueDProofs.push_back(dProof);
		dProofs = uniqueDProofs;
	}
	if (removeTrivial) {
		for (vector<string>::iterator it = dProofs.begin(); it != dProofs.end();)
			if (it->length() == 1)
				it = dProofs.erase(it);
			else
				it++;
	}
	stringstream ss;
	for (size_t i = 0; i < dProofs.size(); i++) {
		if (i)
			ss << ",\n";
		ss << dProofs[i];
	}
	ss << "\n";
	if (!FctHelper::writeToFile(outputFile, ss.str()))
		cerr << "Failed." << endl;
	else
		cout << ss.str().length() << " bytes written to \"" << outputFile<< "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./dProofsToDB ; convert comma-separated proofs to proof database
	// e.g. ./dProofsToDB CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp data/s5-dProofs.txt data/s5proofs-part.txt
	if (argc <= 3) {
		cerr << "Need 1. axioms in normal Polish notation, 2. path to file with comma-separated proofs, and 3. path for new proof database." << endl;
		return 0;
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	DlProofEnumerator::resetRepresentativesFor(&axioms, true);
	chrono::time_point<chrono::steady_clock> startTime;
	string fileString;
	startTime = chrono::steady_clock::now();
	if (!FctHelper::readFile(argv[2], fileString)) {
		cerr << "Invalid file path" << endl;
		return 0;
	}
	string::size_type len = fileString.length();

	// Erase all '\r', '\n', '\t', ' ', and lines starting with '%'. ; NOTE: Much faster than using regular expressions.
	bool startOfLine = true;
	bool erasingLine = false;
	fileString.erase(remove_if(fileString.begin(), fileString.end(), [&](const char c) {
		switch (c) {
		case '\r':
		case '\n':
			startOfLine = true;
			erasingLine = false;
			return true;
		case '\t':
		case ' ':
			startOfLine = false;
			return true;
		case '%':
			if (startOfLine) {
				startOfLine = false;
				erasingLine = true;
				return true;
			} else {
				startOfLine = false;
				return false;
			}
		default:
			startOfLine = false;
			return erasingLine;
		}
	}), fileString.end());

	vector<string> dProofsFromFile = FctHelper::stringSplit(fileString, ",");
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to read and convert " << len << " bytes from \"" << argv[2] << "\"." << endl;
	string result;
	for (const string& dProof : dProofsFromFile)
		result += DRuleParser::toDBProof(dProof, DlProofEnumerator::getCustomAxioms()) + "\n";
	if (!FctHelper::writeToFile(argv[3], result))
		cerr << "Failed." << endl;
	else
		cout << result.length() << " bytes written to \"" << argv[3] << "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./excludeLists ; exclude comma-separated ordered lists of strings
	// e.g. ./excludeLists data/summary-formulasWithoutABC.txt data/summary-formulasA.txt,data/summary-formulasB.txt,data/summary-formulasC.txt
	if (argc <= 2) {
		cerr << "Need 1. path for file to modify, and 2. comma-separated list of paths to files with comma-separated elements." << endl;
		return 0;
	}
	string referenceFile = argv[1];
	vector<string> inputFiles = FctHelper::stringSplit(argv[2], ",");
	auto readElementsFromFile = [](const string& inputFile) -> vector<string> {
		string fileString;
		if (!FctHelper::readFile(inputFile, fileString))
			throw runtime_error("Failed to read file \"" + inputFile + "\".");

		// Erase all '\r', '\n', '\t', ' ', and lines starting with '%'. ; NOTE: Much faster than using regular expressions.
		bool startOfLine = true;
		bool erasingLine = false;
		fileString.erase(remove_if(fileString.begin(), fileString.end(), [&](const char c) {
			switch (c) {
			case '\r':
			case '\n':
				startOfLine = true;
				erasingLine = false;
				return true;
			case '\t':
			case ' ':
				startOfLine = false;
				return true;
			case '%':
				if (startOfLine) {
					startOfLine = false;
					erasingLine = true;
				}
				return erasingLine;
			default:
				startOfLine = false;
				return erasingLine;
			}
		}), fileString.end());

		return FctHelper::stringSplit(fileString, ",");
	};
	set<string, cmpStringGrow> unionOfExcludeLists;
	for (const string& inputFile : inputFiles) {
		vector<string> elements = readElementsFromFile(inputFile);
		cout << "Found " << elements.size() << " separated element" << (elements.size() == 1 ? "" : "s") << " in \"" << inputFile << "\"." << endl;
		unionOfExcludeLists.insert(elements.begin(), elements.end());
	}
	vector<string> elements = readElementsFromFile(referenceFile);
	cout << "Found " << elements.size() << " separated element" << (elements.size() == 1 ? "" : "s") << " in \"" << referenceFile << "\"." << endl;
	cout << "Excluding " << unionOfExcludeLists.size() << " different element" << (unionOfExcludeLists.size() == 1 ? "" : "s") << " from " << inputFiles.size() << " file" << (inputFiles.size() == 1 ? "" : "s") << "." << endl;

	set<string, cmpStringGrow> relevant(elements.begin(), elements.end());
	set<string, cmpStringGrow> difference;
	set_difference(relevant.begin(), relevant.end(), unionOfExcludeLists.begin(), unionOfExcludeLists.end(), inserter(difference, difference.begin()), cmpStringGrow());
	cout << "In total, kept " << difference.size() << " of " << relevant.size() << " different element" << (difference.size() == 1 ? "" : "s") << " of \"" << referenceFile << "\"." << endl;
	if (!difference.empty())
		cout << "Smallest element: " << *difference.begin() << "\n                  (length " << difference.begin()->length() << ")\nLargest element:  " << *difference.rbegin() << "\n                  (length " << difference.rbegin()->length() << ")" << endl;
	string result = FctHelper::setString(difference, { }, { }, ",");
	FctHelper::writeToFile(referenceFile, result);
	cout << result.length() << " bytes written to \"" << referenceFile<< "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./findCompactSummary ; determine which args for '--transform <param1> -f -n -t <param2> -j -1 -s <args>' yields a small output (in bytes)
	// NOTE: assumes that every formula is derived by a unique proof
	// e.g. ./findCompactSummary data/w3.txt CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,Cpp,CCpqCCqrCpr,CCNppp,CpCNpq
	if (argc <= 2) {
		cerr << "Need 1. path to proof summary, and 2. requested theorem list in normal Polish notation." << endl;
		return 0;
	}
	string tmpFile = "data/tmp.txt";

	string inputFile = argv[1];
	unsigned minUseAmountToCreateHelperProof = 2; // NOTE: Set initially to 1 for './findCompactSummary_1' variant, which in some cases is required to find improvements.
	size_t maxLengthToKeepProof = SIZE_MAX;
	string filterForTheorems = argv[2];
	size_t maxLengthToComputeDProof = 134217728;
	bool debug = true;
	DlProofEnumerator::recombineProofSummary(inputFile, true, nullptr, minUseAmountToCreateHelperProof, maxLengthToKeepProof, true, false, &filterForTheorems, true, SIZE_MAX, maxLengthToComputeDProof, false, false, &tmpFile, debug);
	string summary;
	if (!FctHelper::readFile(tmpFile, summary)) {
		cerr << "Invalid file path" << endl;
		return 0;
	}
	size_t smallestResultLen = summary.length();
	string bestDedicatedConclusions = "all of '-j 2'";
	cout << "|summary| = " << smallestResultLen << endl;
	vector<string> lines = FctHelper::stringSplitAndSkip(summary, "\n", " ", true);
	//#for (const string& line : lines)
	//#	cout << line << endl;
	for (size_t i = 0; i < lines.size(); i++) {
		string& line = lines[i];
		string::size_type start = line.find(' ');
		string::size_type end = line.find(' ', start + 1);
		if (start == string::npos || end == string::npos) {
			cerr << "Invalid summary: Could not read intermediate conclusions." << endl;
			return 0;
		}
		line = line.substr(start + 1, end - start - 1);
	}
	//#cout << "lines = " << FctHelper::vectorString(lines) << endl;
	minUseAmountToCreateHelperProof = -1;
	vector<string> theoremsVec = FctHelper::stringSplit(filterForTheorems, ",");
	//#cout << "theorems = " << FctHelper::vectorString(theoremsVec) << endl;
	set<string> theorems(theoremsVec.begin(), theoremsVec.end());
	vector<string> sharedConclusions;
	for (const string& line : lines)
		if (!theorems.count(line))
			sharedConclusions.push_back(line);
	cout << "sharedConclusions = " << FctHelper::vectorString(sharedConclusions) << endl;
	cout << "|sharedConclusions| = " << sharedConclusions.size() << endl;

#if 0 // NOTE: In case the function does not work properly (e.g. because there are redundancies in the abstract proof, causing it
	//         to be greater when using '--transform -s' such that '--transform -j 2' never gets undercut by single modifications),
	//         a pre-defined list can be used here as a starting point for successful reduction.
	string startList = "CCCpCCqrCsrtCCCqrCsrt,CCCCCpCCqrCsrtCCCqrCsrtuCvu,CCCpCqrsCCqrs,CCCCCpqrCqrsCts,CCpqCCCpqrCsr,CCCpqrCqr,CCCNpqrCpr,CCNpCCNqrCCCCCCstuCtuvCCvwCxwyCCypCqp,CCCCNpqCrqpCsp,CpCCpqCrq,CpCqCrp,CCCCCCpqCrqsNttCut,CCCNpqCCCCNrsCCtCutvCCvwCrwxCCxyCpy,CCCCCpqrCsrtCqt,CCCpCqrsCrs,CNNCpqCrCpq,CCNCCpCqpNrsCrs,CCCpqCNprCsCNpr,CpCCNCqrrCqr,CCCpCqpNCNNCNrrsCtr,CCpqCNNpq,CCCpqrCNpr,CCNNpqCpq,CCNpqCNCrpq,CCNpqCNCrCspq,CCpqCCNppq,CNCpqCrCsp,CCpCpqCpq,CCpqCCNqpq,CpCCpqq,CCpCqrCqCpr";
	vector<string> startList_vec = FctHelper::stringSplit(startList, ",");
	set<string> usedConclusions = set<string>(startList_vec.begin(), startList_vec.end());
#else
	set<string> usedConclusions = set<string>(sharedConclusions.begin(), sharedConclusions.end());
#endif
	size_t oldSmallestResultLen;
	do {
		oldSmallestResultLen = smallestResultLen;
		string usedSequence;
		for (set<string>::iterator it = usedConclusions.begin(); it != usedConclusions.end(); ++it) {
			if (it != usedConclusions.begin())
				usedSequence += ",";
			usedSequence += *it;
		}
		//#cout << "sharedConclusions = " << FctHelper::vectorString(sharedConclusions, { }, { }, ",") << endl;
		for (const string& conclusion : sharedConclusions) {
			string conclusionsWithHelperProofs;
			if (usedConclusions.count(conclusion)) { // used, try to not use it
				bool first = true;
				for (const string& c : sharedConclusions)
					if (usedConclusions.count(c) && c != conclusion) { // iterate used conclusion in correct order (since space for indices may vary)
						if (first)
							first = false;
						else
							conclusionsWithHelperProofs += ",";
						conclusionsWithHelperProofs += c;
					}
				//#cout << "[check] removed conclusion: " << conclusion << endl;
			} else { // not used, try to use it
				bool first = true;
				for (const string& c : sharedConclusions)
					if (usedConclusions.count(c) || c == conclusion) { // iterate used conclusion in correct order (since space for indices may vary)
						if (first)
							first = false;
						else
							conclusionsWithHelperProofs += ",";
						conclusionsWithHelperProofs += c;
					}
				//#cout << "[check] added conclusion: " << conclusion << endl;
			}
			//#cout << "[NOTE conclusion = " << conclusion << "] Trying " << conclusionsWithHelperProofs << "." << endl;

			string bestToggledConclusion;
			debug = false;
			try {
				DlProofEnumerator::recombineProofSummary(inputFile, true, &conclusionsWithHelperProofs, minUseAmountToCreateHelperProof, maxLengthToKeepProof, true, false, &filterForTheorems, true, SIZE_MAX, maxLengthToComputeDProof, false, false, &tmpFile, debug);
				if (!FctHelper::readFile(tmpFile, summary)) {
					cerr << "Invalid file path" << endl;
					return 0;
				}
				size_t resultLen = summary.length();
				//#cout << "[NOTE] Result: " << resultLen << "(best: " << smallestResultLen << ")" << endl;
				if (resultLen < smallestResultLen || (resultLen == smallestResultLen && conclusionsWithHelperProofs.length() < bestDedicatedConclusions.length() && bestDedicatedConclusions != "all of '-j 2'")) {
					smallestResultLen = resultLen;
					bestDedicatedConclusions = conclusionsWithHelperProofs;
					bestToggledConclusion = conclusion;
					cout << "new smallestResultLen: " << smallestResultLen << endl;
					cout << "new bestDedicatedConclusions: " << bestDedicatedConclusions << endl;
				}
			} catch (...) {
			}

			if (!bestToggledConclusion.empty()) {
				if (usedConclusions.count(bestToggledConclusion)) { // used, do not use it
					usedConclusions.erase(bestToggledConclusion);
				} else { // not used, use it
					usedConclusions.emplace(bestToggledConclusion);
				}
			}
		}
	} while (oldSmallestResultLen != smallestResultLen);
	return 0;
#endif //###
#if 0 //### ./formulasFromProofs ; intermediate conclusions from comma-separated proofs in normal polish notation
	// NOTE: Requires '#include <regex>'.
	// e.g. ./formulasFromProofs CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp data/s5-dProofs.txt data/s5-formulas.txt
	if (argc <= 3) {
		cerr << "Need 1. axioms in normal Polish notation, 2. path to file with comma-separated proofs, and 3. path for output file." << endl;
		return 0;
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	DlProofEnumerator::resetRepresentativesFor(&axioms, true);
	string inputFile = argv[2]; // e.g. "D:/Dropbox/eclipse/pmGenerator/Release64bitDynamicGcc11.3/data/w5-in.txt"
	string outputFile = argv[3];
	DlProofEnumerator::printProofs( { }, DlFormulaStyle::PolishStandard, false, true, 1, true, &inputFile, &outputFile, true);
	string fileString;
	if (!FctHelper::readFile(outputFile, fileString)) {
		cerr << "Invalid file path" << endl;
		return 0;
	}
	fileString = regex_replace(fileString, regex("    [^\n]+\n"), "");
	fileString = regex_replace(fileString, regex("\\[[0-9]+\\] "), "");
	fileString = regex_replace(fileString, regex(" = [^\n]+\n"), "\n");
	//#cout << fileString << flush;
	vector<string> formulas = FctHelper::stringSplit(fileString, "\n");
	stringstream ss;
	bool first = true;
	for (const string& f : formulas)
		if (!f.empty()) {
			if (first)
				first = false;
			else
				ss << ",";
			ss << f;
		}
	ss << "\n";
	if (!FctHelper::writeToFile(outputFile, ss.str()))
		cerr << "Failed." << endl;
	else
		cout << ss.str().length() << " bytes written to \"" << outputFile << "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./formulasFromSummaries ; extract comma-separated ordered list of formulas in normal Polish notation that are used in the given proof summaries
	// NOTE: Requires '#include "logic/DlCore.h"'
	// e.g. ./formulasFromSummaries data/summary-formulas.txt data/m.txt,data/w1.txt,data/w2.txt,data/w3.txt,data/w4.txt,data/w5.txt,data/w6.txt,data/s5.txt
	if (argc <= 2) {
		cerr << "Need 1. path for output file, and 2. comma-separated list of paths to proof summary files." << endl;
		return 0;
	}
	string tmpFile = "data/tmp.txt";
	string outputFile = argv[1];
	vector<string> inputFiles = FctHelper::stringSplit(argv[2], ",");
	set<string, cmpStringGrow> formulas;
	for (const string& proofSummaryFile : inputFiles) {
		string filterForTheorems = ".";
		DlProofEnumerator::recombineProofSummary(proofSummaryFile, true, nullptr, 1, SIZE_MAX, true, false, &filterForTheorems, true, SIZE_MAX, 134217728, false, false, &tmpFile, false);
		set<string, cmpStringGrow> conclusions;
		vector<DRuleParser::AxiomInfo> requiredIntermediateResults;
		DlProofEnumerator::convertProofSummaryToAbstractDProof(tmpFile, nullptr, nullptr, &requiredIntermediateResults, true, true, false);
		for (const DRuleParser::AxiomInfo& info : requiredIntermediateResults) {
			const shared_ptr<DlFormula>& f = info.refinedAxiom;
			conclusions.emplace(DlCore::toPolishNotation(f));
			//conclusions.emplace(DlCore::toPolishNotation_noRename(f));
		}
		cout << "Found " << conclusions.size() << " different intermediate conclusion" << (conclusions.size() == 1 ? "" : "s") << " in \"" << proofSummaryFile << "\"." << endl;
		formulas.insert(conclusions.begin(), conclusions.end());
	}
	cout << "In total, found " << formulas.size() << " different formula" << (formulas.size() == 1 ? "" : "s") << " in " << inputFiles.size() << " file" << (inputFiles.size() == 1 ? "" : "s") << "." << endl;
	if (!formulas.empty())
		cout << "Smallest formula: " << *formulas.begin() << "\n                  (length " << formulas.begin()->length() << ")\nLargest formula:  " << *formulas.rbegin() << "\n                  (length " << formulas.rbegin()->length() << ")" << endl;
	string result = FctHelper::setString(formulas, { }, { }, ",");
	FctHelper::writeToFile(outputFile, result);
	cout << result.length() << " bytes written to \"" << outputFile<< "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./gkcHintsFromProof ; extract hints from GKC output, parsed with "strategy":["hyper"]
	// e.g. ./gkcHintsFromProof gkc-out.txt
	if (argc <= 1) {
		cerr << "Need path to file with GKC output (with strategy 'hyper' used)." << endl;
		return 0;
	}
	string content;
	if (!FctHelper::readFile(argv[1]/*"D:/Dropbox/eclipse/pmGenerator/Release64bitDynamicGcc11.3/gkc-out.txt"*/, content)) {
		cerr << "Invalid file path" << endl;
		return 0;
	}
	boost::replace_all(content, "\r\n", "\n");
	vector<string> lines = FctHelper::stringSplit(content, "\n");
	{
		vector<string> _lines;
		for (const string& line : lines)
			if (line.starts_with(" ") && line.find('-') == string::npos) {
				string::size_type pos = line.find(" t(");
				if (pos != string::npos)
					_lines.push_back(line.substr(pos + 1));
			}
		lines = _lines;
	}
	cout << "formulas(hints).\n\n" << FctHelper::stringJoin("\n", lines) << "\n\nend_of_list." << endl;
	return 0;
#endif //###
#if 0 //### ./importExtractionFromDB ; import proofs from DB into proof files
	// NOTE: Requires '#include <tbb/concurrent_map.h>' and '#include <tbb/parallel_for.h>' before 'using namespace' directives.
	// e.g. ./importExtractionFromDB CpCCqCprCCNrCCNstqCsr data/exs/w2-topDB-shaky.txt
	//      ./importExtractionFromDB CpCCqCprCCNrCCNstqCsr data/exs/w2-topDB-modifications-shaky.txt
	if (argc <= 2) {
		cerr << "Need 1. axioms in normal Polish notation, and 2. path to proof database. Optional: 3. necessitation limit (or -1)" << endl;
		return 0;
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	string pathProofDB = argv[2];
	uint32_t necessitationLimit = 0;
	if (argc >= 4) {
		try {
			necessitationLimit = stoi(argv[3]);
			cout << "Necessitation limit set to " << necessitationLimit << "." << endl;
		} catch (...) {
			cerr << "Invalid format for \"3. necessitation limit (or -1)\"." << endl;
			return 0;
		}
	}
	vector<string> dProofsInFile = DRuleParser::readFromMmsolitaireFile(pathProofDB, nullptr, true);
	DlProofEnumerator::resetRepresentativesFor(&axioms, true, necessitationLimit);
	vector<string> conclusionsForFile(dProofsInFile.size());

	chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	cout << "Going to parse " << dProofsInFile.size() << " D-proofs." << endl;
	tbb::parallel_for(size_t(0), dProofsInFile.size(), [&dProofsInFile, &conclusionsForFile](size_t i) { // NOTE: Counts from i = start := 0 until i < end := representativesOfWordLengthLimit.size().
		const string& dProof = dProofsInFile[i];
		vector<DProofInfo> rawParseData = DRuleParser::parseDProof_raw(dProof, DlProofEnumerator::getCustomAxioms(), 1);
		const shared_ptr<DlFormula>& conclusion = get<0>(rawParseData.back().second).back();
		conclusionsForFile[i] = DlCore::toPolishNotation_noRename(conclusion);
	});
	//#cout << "conclusionsForFile = " << conclusionsForFile[0] << ", " << conclusionsForFile[1] << ", " << conclusionsForFile[2] << ", ..." << endl;
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to parse " << dProofsInFile.size() << " D-proofs." << endl;

	string axiomProofList;
	for (size_t i = 1; i <= axioms.size(); i++) {
		if (i > 1)
			axiomProofList += ",";
		axiomProofList += to_string(i);
	}
	//#cout << "axiomProofList = " << axiomProofList << endl;
	string targetDir;
	DlProofEnumerator::extractConclusions(ExtractionMethod::ProofSystemFromString, 0, &axiomProofList, true, false, 0, 0, true, &targetDir);
	targetDir += "dProofs-withConclusions/";
	if (!FctHelper::ensureDirExists(targetDir)) {
		cerr << "Created extraction folder, but failed to create \"" << targetDir << "\"." << endl;
		return 0;
	}
	cout << "Created target directory at \"" << targetDir << "\"." << endl;

	cout << "Going to arrange " << dProofsInFile.size() << " D-proofs with conclusions for new proof files." << endl;
	tbb::concurrent_map<size_t, tbb::concurrent_map<string, string, cmpStringGrow>> collections;
	startTime = chrono::steady_clock::now();
	tbb::parallel_for(size_t(0), dProofsInFile.size(), [&dProofsInFile, &conclusionsForFile, &collections](size_t i) { // NOTE: Counts from i = start := 0 until i < end := representativesOfWordLengthLimit.size().
		const string& dProof = dProofsInFile[i];
		collections[dProof.length()][dProof] = conclusionsForFile[i];
	});
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to arrange " << dProofsInFile.size() << " D-proofs into " << collections.size() << " collections." << endl;
	map<size_t, size_t> collectionSizes;
	for (tbb::concurrent_map<size_t, tbb::concurrent_map<string, string, cmpStringGrow>>::iterator it = collections.begin(); it != collections.end(); ++it)
		collectionSizes.emplace(it->first, it->second.size());
	cout << "\"<D-proof length>:<amount>\"-pairs: " << FctHelper::mapStringF(collectionSizes, [](const pair<const size_t, size_t>& p) { return to_string(p.first) + ":" + to_string(p.second); }, { }, { }) << endl;
	const uint32_t c = necessitationLimit ? 1 : 2;
	if (!collections.empty()) {
		size_t maxProofLen = prev(collectionSizes.end())->first;
		//#cout << "maxProofLen = " << maxProofLen << endl;
		size_t oldColSize = collections.size();
		for (size_t len = 1 + c; len < maxProofLen; len += c)
			collections[len];
		if (oldColSize < collections.size())
			cout << "Inserted " << collections.size() - oldColSize << " missing (empty) collections. There are now " << collections.size() << " collections." << endl;
	}

	cout << "Going to write " << dProofsInFile.size() << " D-proofs with conclusions into new proof files." << endl;
	startTime = chrono::steady_clock::now();
	mutex mtx_cout;
	tbb::parallel_for(collections.range(), [&](tbb::concurrent_map<size_t, tbb::concurrent_map<string, string, cmpStringGrow>>::range_type& range) {
		chrono::time_point<chrono::steady_clock> startTime;
		for (tbb::concurrent_map<size_t, tbb::concurrent_map<string, string, cmpStringGrow>>::const_iterator it_range = range.begin(); it_range != range.end(); ++it_range) {
			string targetFile = "dProofs" + to_string(it_range->first) + ".txt";
			const tbb::concurrent_map<string, string, cmpStringGrow>& collection = it_range->second;
			startTime = chrono::steady_clock::now();
			{
				ofstream fout(targetDir + targetFile, fstream::out | fstream::binary); // print directly to file to save memory
				for (tbb::concurrent_map<string, string, cmpStringGrow>::const_iterator it = collection.begin(); it != collection.end(); ++it) {
					if (it != collection.begin())
						fout << "\n";
					fout << it->first << ":" << it->second; // <dProof>:<conclusion>
				}
			}
			chrono::microseconds dur = chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime);
			lock_guard<mutex> lock(mtx_cout);
			cout << FctHelper::durationStringMs(dur) << " taken to write " << collection.size() << " D-proofs with conclusions to " << targetFile << "." << endl;
		}
	});
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to write all " << dProofsInFile.size() << " D-proofs." << endl;
	return 0;
#endif //###
#if 0 //### ./logVerifier ; log file verifier
	// NOTE: Requires '#include <regex>' and '#include <cmath>'.
	// To be called from project directory (which contains 'log/') to run log file checks.
	for (const filesystem::directory_entry& entry : filesystem::recursive_directory_iterator(filesystem::current_path())) {
		if (entry.path().string().find("\\log\\") == string::npos && entry.path().string().find("/log/") == string::npos)
			continue;
		string file;
		string ext = entry.path().extension().string();
		if (ext == ".txt") {
			string filename = entry.path().filename().string();
			if (filename == "jobsRSS.txt") {
				cout << entry.path().string() << ":" << endl;
				if (!FctHelper::readFile(entry.path().string(), file)) {
					cerr << "[FATAL ERROR] Failed to read." << endl;
					return 1;
				}
				regex r("\\n.*:\\n");
				size_t lastNum = 0;
				for (sregex_iterator it = sregex_iterator(file.begin(), file.end(), r); it != sregex_iterator(); ++it) {
					const smatch& m = *it;
					string numstr = m.str().substr(1, m.str().length() - 3);
					string::size_type dash = numstr.find('-');
					size_t num;
					try {
						num = stoll(dash == string::npos ? numstr : numstr.substr(0, dash));
					} catch (...) {
						cerr << "[ERROR] \"" << numstr << "\" should be a proof length." << endl;
						continue;
					}
					if (lastNum > num)
						cerr << "[WARNING] " << num << " < " << lastNum << " ; bad ordering" << endl;
					string remainder = file.substr(m.position() + m.length());
					string::size_type posLF = remainder.find('\n');
					string sacct = posLF == string::npos ? remainder : remainder.substr(0, posLF);
					smatch m_;
					if (posLF == string::npos || !regex_match(sacct, m_, regex("\\$ sacct -j [0-9]{8} --format=\"JobID,Partition,AllocCPUS,State,ExitCode,Elapsed,MaxRSS(%[0-9]+|)\"")))
						cerr << "[WARNING] Bad or missing sacct command after \"" << numstr << "\": " << sacct << endl;
					else if (remainder.substr(posLF, 3) != "\n> ")
						cerr << "[WARNING] Bad or missing sacct output after \"" << numstr << "\"." << endl;
					else {
						string::size_type pos = posLF + 3;
						vector<string> sacctOutput;
						size_t len = 0;
						while ((posLF = remainder.find('\n', pos)) != string::npos) {
							sacctOutput.push_back(remainder.substr(pos, posLF - pos));
							if (!len)
								len = sacctOutput.back().length();
							else if (sacctOutput.back().length() != len)
								cerr << "[WARNING] Uneven sacct output after \"" << numstr << "\"." << endl;
							if (remainder.substr(posLF, 3) != "\n> ")
								break;
							pos = posLF + 3;
						}
						//#cout << sacctOutput.size() << " lines:\n" << FctHelper::vectorString(sacctOutput, { }, { }, "\n") << endl;
						string relevantOutput;
						if (sacctOutput.size() == 6)
							relevantOutput = sacctOutput[5];
						else if (sacctOutput.size() == 5)
							relevantOutput = sacctOutput[3];
						else {
							cerr << "[ERROR] Found " << sacctOutput.size() << " lines for sacct output." << endl;
							continue;
						}
						if (!sacctOutput[0].ends_with("MaxRSS ")) {
							cerr << "[ERROR] First line of sacct output should end with \"MaxRSS \"." << endl;
							continue;
						}
						string::size_type end;
						string::size_type begin = relevantOutput.substr(0, (end = relevantOutput.find_last_not_of(' '))).find_last_of(' ');
						relevantOutput = relevantOutput.substr(begin + 1, end - begin);
						if (relevantOutput.empty() || (relevantOutput.back() != 'K' && relevantOutput.back() != 'M')) {
							cerr << "[ERROR] Found \"" << relevantOutput << "\" as relevant MaxRSS entry." << endl;
							continue;
						}
						string correctPrefix = relevantOutput.substr(0, relevantOutput.length() - 1);
						size_t ram;
						try {
							ram = stoll(correctPrefix);
						} catch (...) {
							cerr << "[ERROR] \"" << correctPrefix << "\" should be memory number." << endl;
							continue;
						}
						bool K = relevantOutput.back() == 'K';
						correctPrefix += string(" / 1024^") + (K ? "2" : "1") + " = " + to_string(ram / (K ? 1024 * 1024 : 1024));
						pos = posLF + 1;
						posLF = remainder.find('\n', pos + 1);
						string equation = remainder.substr(pos, posLF - pos);
						string correctPostfix = " ≈ " + FctHelper::round((long double) ram / (K ? 1024 * 1024 : 1024), 2);
						if (!equation.starts_with(correctPrefix) || !equation.ends_with(correctPostfix)) {
							cerr << "[WARNING] Is:" << equation << endl;
							cerr << "      Should:" << correctPrefix << "[...]" << correctPostfix << endl;
						}
						//#cerr << "[NOTE] Should:" << correctPrefix << "[...]" << correctPostfix << endl;
					}
				}
			}
		} else if (ext == ".log") {
			string filename = entry.path().filename().string();
			if (filename.starts_with("dProof")) { // e.g. "dProofs29_6node_288cpu.log"
				cout << entry.path().string() << ":" << endl;
				if (!FctHelper::readFile(entry.path().string(), file)) {
					cerr << "[FATAL ERROR] Failed to read." << endl;
					return 1;
				}
				size_t node = 1;
				size_t cpu = 0;
				smatch m;
				if (regex_search(filename, m, regex("_[0-9]+node")))
					node = stoll(m.str().substr(1, m.str().length() - 5));
				if (regex_search(filename, m, regex("_[0-9]+cpu")))
					cpu = stoll(m.str().substr(1, m.str().length() - 4));
				else {
					cerr << "[ERROR] No cpu amount in file name." << endl;
					continue;
				}
				vector<string> lines = FctHelper::stringSplit(file, "\n");
				if (lines.size() < 9) {
					cerr << "[ERROR] Bad line amount." << endl;
					continue;
				}
				if (!lines[1].starts_with("  The run was executed on " + (node == 1 ? "a" : to_string(node)))) {
					cerr << "[ERROR] Bad node amount." << endl;
					continue;
				}
				while (lines[lines.size() - 2].starts_with("srun: ") || lines[lines.size() - 2].starts_with("slurmstepd: ")) {
					lines.pop_back();
					lines.back() = "";
					if (lines.size() < 9) {
						cerr << "[ERROR] Bad line amount." << endl;
						continue;
					}
				}
				size_t cpuPerNode = cpu / node;
				if (cpuPerNode * node != cpu) {
					cerr << "[ERROR] Bad cpu / node amounts." << endl;
					continue;
				} else if (lines[2].find("(" + to_string(cpuPerNode) + " cores total per node)") == string::npos) {
					cerr << "[ERROR] Missing or invalid 'cores total per node'." << endl;
					continue;
				} else if (node > 1 && file.find("; " + to_string(node) + " processes]") == string::npos) {
					cerr << "[ERROR] Missing or invalid process amount via MPI." << endl;
					continue;
				} else if (!lines[4].starts_with("  Wall-clock time: ")) {
					cerr << "[ERROR] Missing wall-clock time." << endl;
					continue;
				} else if (!lines[5].starts_with("  CPU utilization: ")) {
					cerr << "[ERROR] Missing CPU utilization." << endl;
					continue;
				} else if (lines[6].find(": Process started") == string::npos) {
					cerr << "[ERROR] Missing 'Process started'." << endl;
					continue;
				} else if (!lines.back().empty()) {
					cerr << "[ERROR] Missing final empty line." << endl;
					continue;
				} else if (lines[lines.size() - 2].find(": Process terminated") == string::npos) {
					cerr << "[ERROR] Missing 'Process terminated'." << endl;
					continue;
				}
				string ct = lines[4].substr(19);
				string::size_type ct_offset;
				ct = ct.substr(ct_offset = ct.find_first_not_of(' '));
				ct = ct.substr(0, ct.find_first_of(' '));
				string ut = lines[5].substr(19);
				string::size_type ut_offset;
				ut = ut.substr(ut_offset = ut.find_first_not_of(' '));
				if (ut_offset != 0) {
					cerr << "[ERROR] Extra offset for CPU utilization." << endl;
					continue;
				}
				ut = ut.substr(0, ut.find_first_of(' '));
				if (!lines[4].substr(19 + ct_offset + ct.length()).starts_with(" h")) {
					cerr << "[ERROR] Missing or invalid ' h'." << endl;
					continue;
				} else if (!lines[5].substr(19 + ut.length()).starts_with(" core-h")) {
					cerr << "[ERROR] Missing or invalid ' core-h'." << endl;
					continue;
				}
				string::size_type ct_dot = ct.find('.') != string::npos ? lines[4].find(ct, 19) + ct.find('.') : lines[4].find(ct, 19) + ct.size();
				string::size_type ut_dot = ut.find('.') != string::npos ? lines[5].find(ut, 19) + ut.find('.') : lines[5].find(ut, 19) + ut.size();
				if (ct_dot != ut_dot) {
					cerr << "[ERROR] Uneven offsets." << endl;
					continue;
				}
				string::size_type ct_dots = ct.find("…");
				string::size_type ut_dots = ut.find("…");
				ct = ct.substr(0, ct_dots);
				ut = ut.substr(0, ut_dots);
				if (ut_dots != string::npos)
					ut += ut.substr(ut.size() - 3);
				long double ut_num = stold(ut);
				stringstream ss_ct_calc;
				ss_ct_calc << setprecision(static_cast<int>(ct.length())) << ut_num / cpu;
				if ((ct_dots == string::npos && ss_ct_calc.str() != ct) || (ct_dots != string::npos && ss_ct_calc.str().substr(0, ct.length() - 1) != ct.substr(0, ct.length() - 1)))
					cerr << "[WARNING] Unmatching read and calculated wall-clock times " << (ct_dots == string::npos ? ss_ct_calc.str() + " and " + ct : ss_ct_calc.str().substr(0, ct.length() - 1) + " and " + ct.substr(0, ct.length() - 1)) << "." << endl;
				size_t coreSeconds = static_cast<size_t>(round(ut_num * 3600));
				string dateStart = lines[6].substr(0, lines[6].find(": Process started")).substr(4);
				string dateEnd = lines[lines.size() - 2].substr(0, lines[lines.size() - 2].find(": Process terminated")).substr(4);
				auto strToTime = [](string s) -> chrono::time_point<chrono::system_clock> { if (s[4] == ' ') s[4] = '0'; tm time = { }; stringstream ss(s); ss >> get_time(&time, "%b %d %H:%M:%S %Y"); return chrono::system_clock::from_time_t(mktime(&time)); };
				chrono::seconds durSecondsProvided = chrono::duration_cast<chrono::seconds>(strToTime(dateEnd) - strToTime(dateStart));
				if (coreSeconds != durSecondsProvided.count() * cpu)
					cerr << "[WARNING] Unmatching read and calculated core-s durations " << coreSeconds << " and " << durSecondsProvided.count() * cpu << ". (from dateStart " << dateStart << " to " << dateEnd << " are " << durSecondsProvided.count() << " seconds, and " << durSecondsProvided.count() << " * " << cpu << " = " << durSecondsProvided.count() * cpu << ")" << endl;
			} else { // e.g. "29.log" or "31-31.log"
				smatch m;
				if (regex_match(filename, m, regex("[0-9]+(-[0-9]+|)\\.log"))) {
					cout << entry.path().string() << ":" << endl;
					if (!FctHelper::readFile(entry.path().string(), file)) {
						cerr << "[FATAL ERROR] Failed to read." << endl;
						return 1;
					}
					vector<string> lines = FctHelper::stringSplit(file, "\n");
					if (lines.size() < 20) {
						cerr << "[ERROR] Bad line amount." << endl;
						continue;
					}
					if (!lines[1].starts_with("  The run was executed on a ")) {
						cerr << "[ERROR] Bad node amount." << endl;
						continue;
					}
					while (lines[lines.size() - 2].starts_with("srun: ") || lines[lines.size() - 2].starts_with("slurmstepd: ")) {
						lines.pop_back();
						lines.back() = "";
						if (lines.size() < 20) {
							cerr << "[ERROR] Bad line amount." << endl;
							continue;
						}
					}
					string maxRssBehind = lines[9].substr(lines[9].size() - 2);
					if (maxRssBehind != "K " && maxRssBehind != "M ") {
						cerr << "[ERROR] Unknown suffix \"" << maxRssBehind << "\"." << endl;
						continue;
					} else if (!regex_match(lines[5], m, regex("   \\$ sacct --format=\"JobID,Partition,AllocCPUS,State,ExitCode,Elapsed,MaxRSS(%[0-9]+|)\""))) {
						cerr << "[ERROR] Missing or invalid sacct command." << endl;
						continue;
					} else if (lines[6].length() != lines[7].length() || lines[7].length() != lines[8].length() || lines[8].length() != lines[9].length() || lines[9].length() != lines[10].length()) {
						cerr << "[ERROR] Invalid sacct output." << endl;
						continue;
					} else if (lines[12].find(": Process started") == string::npos) {
						cerr << "[ERROR] Missing 'Process started'." << endl;
						continue;
					} else if (!lines.back().empty()) {
						cerr << "[ERROR] Missing final empty line." << endl;
						continue;
					} else if (lines[lines.size() - 2].find(": Process terminated") == string::npos) {
						cerr << "[ERROR] Missing 'Process terminated'." << endl;
						continue;
					} else if (lines[0].starts_with("( This log file was generated by executing 'pmGenerator -c")) {
						string::size_type pos = lines[0].find(" -s ", 58);
						if (pos != string::npos) {
							string system = lines[0].substr(pos + 4, lines[0].find_first_of(' ', pos + 4) - pos - 4);
							if (lines[0].find(" -s " + system + " --iterate -u'") == string::npos)
								cerr << "[WARNING] Missing or invalid call information." << endl;
							if (entry.path().string().find(system + "\\") == string::npos && entry.path().string().find(system + "/") == string::npos)
								cerr << "[WARNING] System " << system << " missing from path." << endl;
							if (!lines[14].starts_with("1. resetRepresentativesFor(\"" + system + "\"")) {
								cerr << "[ERROR] Conflicting system declaration and selection." << endl;
								continue;
							}
						} else
							cerr << "[WARNING] Missing or invalid '-s <system>'." << endl;
					} else {
						cerr << "[NOTE] No 'pmGenerator -c [...]' comment." << endl;
						if (lines[0].find("'DlProofEnumerator::countNextIterationAmount(false, true)'") == string::npos && lines[0].find("'pmGenerator --iterate -u'") == string::npos)
							cerr << "[WARNING] Missing or invalid call information." << endl;
					}
					string correctPrefix = lines[9].substr(0, lines[9].size() - 2);
					correctPrefix = correctPrefix.substr(correctPrefix.find_last_of(' ') + 1);
					size_t ram;
					try {
						ram = stoll(correctPrefix);
					} catch (...) {
						cerr << "[ERROR] \"" << correctPrefix << "\" should be memory number." << endl;
						continue;
					}
					bool K = maxRssBehind == "K ";
					correctPrefix = "  By " + to_string(ram) + (K ? " KiB" : " MiB") + " = (" + to_string(ram) + " / 1024^" + (K ? "2" : "1") + ") GiB = " + to_string(ram / (K ? 1024 * 1024 : 1024));
					string correctPostfix = " GiB, it used approximately " + FctHelper::round((long double) ram / (K ? 1024 * 1024 : 1024), 2) + " gibibytes of memory. )";
					if (!lines[11].starts_with(correctPrefix) || !lines[11].ends_with(correctPostfix)) {
						cerr << "[WARNING] Is:" << lines[11] << endl;
						cerr << "      Should:" << correctPrefix << "[...]" << correctPostfix << endl;
					}
				}
			}
		}
	}
	return 0;
#endif //###
#if 0 //### ./prover9Formulas ; formulas in normal polish notation to OTTER / Prover9 format
	// e.g. ./prover9Formulas CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp
	if (argc <= 1) {
		cerr << "Need formulas in normal polish notation." << endl;
		return 0;
	}
	vector<string> formulas = FctHelper::stringSplit(argv[1], ",");
	for (const string& f : formulas)
		cout << prover9Formula(f) << endl;
	return 0;
#endif //###
#if 0 //### ./prover9HintsFromProofs ; intermediate conclusions from comma-separated proofs in normal polish notation to OTTER / Prover9 format
	// NOTE: Requires '#include <regex>'.
	// e.g. ./prover9HintsFromProofs CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp data/s5-dProofs.txt data/s5-formulas-p9.txt
	if (argc <= 3) {
		cerr << "Need 1. axioms in normal Polish notation, 2. path to file with comma-separated proofs, and 3. path for output file." << endl;
		return 0;
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	DlProofEnumerator::resetRepresentativesFor(&axioms, true);
	string inputFile = argv[2]; // e.g. "D:/Dropbox/eclipse/pmGenerator/Release64bitDynamicGcc11.3/data/w5-in.txt"
	string outputFile = argv[3];
	DlProofEnumerator::printProofs( { }, DlFormulaStyle::PolishStandard, false, true, 1, true, &inputFile, &outputFile, true);
	string fileString;
	if (!FctHelper::readFile(outputFile, fileString)) {
		cerr << "Invalid file path" << endl;
		return 0;
	}
	fileString = regex_replace(fileString, regex("    [^\n]+\n"), "");
	fileString = regex_replace(fileString, regex("\\[[0-9]+\\] "), "");
	fileString = regex_replace(fileString, regex(" = [^\n]+\n"), "\n");
	//#cout << fileString << flush;
	vector<string> formulas = FctHelper::stringSplit(fileString, "\n");
	stringstream ss;
	ss << "formulas(hints).\n\n";
	for (const string& f : formulas)
		if (!f.empty())
			ss << prover9Formula(f) << "\n";
	ss << "\nend_of_list.\n";
	if (!FctHelper::writeToFile(outputFile, ss.str()))
		cerr << "Failed." << endl;
	else
		cout << ss.str().length() << " bytes written to \"" << outputFile << "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./prover9HintsFromSeparateProofs ; individual intermediate conclusions from comma-separated proofs in normal polish notation to OTTER / Prover9 format
	// NOTE: Requires '#include <regex>'.
	// e.g. ./prover9HintsFromSeparateProofs CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,CLpp,CLCpqCLpLq,CNLNpLNLNp data/s5-dProofs.txt data/s5-formulas-p9.txt
	if (argc <= 3) {
		cerr << "Need 1. axioms in normal Polish notation, 2. path to file with comma-separated proofs, and 3. path for output file." << endl;
		return 0;
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	DlProofEnumerator::resetRepresentativesFor(&axioms, true);
	string inputFile = argv[2]; // e.g. "D:/Dropbox/eclipse/pmGenerator/Release64bitDynamicGcc11.3/data/w5-in.txt"
	string outputFile = argv[3];
	//###
	string fileString;
	chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	if (!FctHelper::readFile(inputFile, fileString))
		throw runtime_error("Failed to read file \"" + inputFile + "\".");
	string::size_type len = fileString.length();

	// Erase all '\r', '\n', '\t', ' ', and lines starting with '%'. ; NOTE: Much faster than using regular expressions.
	bool startOfLine = true;
	bool erasingLine = false;
	fileString.erase(remove_if(fileString.begin(), fileString.end(), [&](const char c) {
		switch (c) {
		case '\r':
		case '\n':
			startOfLine = true;
			erasingLine = false;
			return true;
		case '\t':
		case ' ':
			startOfLine = false;
			return true;
		case '%':
			if (startOfLine) {
				startOfLine = false;
				erasingLine = true;
				return true;
			} else {
				startOfLine = false;
				return false;
			}
		default:
			startOfLine = false;
			return erasingLine;
		}
	}), fileString.end());

	vector<string> dProofsFromFile = FctHelper::stringSplit(fileString, ",");
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to read and convert " << len << " bytes from \"" << inputFile << "\"." << endl;
	vector<vector<string>> allFormulas;
	//###
	for (const string& dProof : dProofsFromFile) {
		DlProofEnumerator::printProofs( { dProof }, DlFormulaStyle::PolishStandard, false, true, 1, true, nullptr, &outputFile, true);
		string fileString;
		if (!FctHelper::readFile(outputFile, fileString)) {
			cerr << "Invalid file path" << endl;
			return 0;
		}
		fileString = regex_replace(fileString, regex("    [^\n]+\n"), "");
		fileString = regex_replace(fileString, regex("\\[[0-9]+\\] "), "");
		fileString = regex_replace(fileString, regex(" = [^\n]+\n"), "\n");
		//#cout << fileString << flush;
		allFormulas.resize(allFormulas.size() + 1);
		allFormulas.back() = FctHelper::stringSplit(fileString, "\n");
	}
	stringstream ss;
	ss << "formulas(hints).\n\n";
	bool first = true;
	for (const vector<string>& formulas : allFormulas) {
		if (first)
			first = false;
		else
			ss << "\n";
		for (const string& f : formulas)
			if (!f.empty())
				ss << prover9Formula(f) << "\n";
	}
	ss << "\nend_of_list.\n";
	if (!FctHelper::writeToFile(outputFile, ss.str()))
		cerr << "Failed." << endl;
	else
		cout << ss.str().length() << " bytes written to \"" << outputFile << "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./prover9HintsFromTopList ; create hints from smallest conclusion lists
	// NOTE: Requires '#include <regex>'.
	if (argc <= 3) {
		//cerr << "Need 1. axioms in normal Polish notation, 2. path to file with comma-separated proofs, and 3. path for output file." << endl;
		cerr << "Need 1. axioms in normal Polish notation, 2. path to smallest conclusion list file, and 3. path for output file." << endl;
		return 0;
	}
	vector<string> axioms = FctHelper::stringSplit(argv[1], ",");
	DlProofEnumerator::resetRepresentativesFor(&axioms, true);
	// default:
	// "data/top1000SmallestConclusions_1to39Steps.txt"
	// m:
	// ./prover9HintsFromTopList CCCCCpqCNrNsrtCCtpCsp data/478804cd4793bc7f87041d99326aff4595662146d8a68175dda22bed/top1000SmallestConclusions_1to83Steps.txt data/m-topHints.txt
	// w1:
	// ./prover9HintsFromTopList CCpCCNpqrCsCCNtCrtCpt data/02974777ff5f71e12ef58ccebedeef133584aad66e06a2a13b2b4b2c/top1000SmallestConclusions_1to161Steps.txt data/w1-topHints.txt
	// w2:
	// ./prover9HintsFromTopList CpCCqCprCCNrCCNstqCsr data/db25c49b13fec26ecf32e40bde65e4e2273f23b3c022cfd0fa986cff/top1000SmallestConclusions_1to43Steps.txt data/w2-topHints.txt
	// w3:
	// ./prover9HintsFromTopList CpCCNqCCNrsCptCCtqCrq data/0df075acc552c62513b49b6ed674bfcde1c1b018e532c665be229314/top1000SmallestConclusions_1to73Steps.txt data/w3-topHints.txt
	// w4:
	// ./prover9HintsFromTopList CpCCNqCCNrsCtqCCrtCrq data/fe7117b8aad7634fae344172b9fee05f77e5e23b035276b17d8c6ec9/top1000SmallestConclusions_1to169Steps.txt data/w4-topHints.txt
	// w5:
	// ./prover9HintsFromTopList CCpqCCCrCstCqCNsNpCps data/1d5f27494b1a2312e223b7f8dd3551abf717590ceef694c08dcbed72/top1000SmallestConclusions_1to55Steps.txt data/w5-topHints.txt
	// w6:
	// ./prover9HintsFromTopList CCCpqCCCNrNsrtCCtpCsp data/7f473b6ba952b3deadf36cd7f1c4b5286ef32fef64808d14fff70a69/top1000SmallestConclusions_1to95Steps.txt data/w6-topHints.txt
	// NOTE: Proof translations from extracted modified systems are not supported.
	string inputFile = argv[2];
	string outputFile = argv[3];
	string content;
	if (!FctHelper::readFile(inputFile, content)) {
		cerr << "Invalid file path" << endl;
		return 0;
	}
	vector<string> dProofs;
	for (string line : FctHelper::stringSplitAndSkip(content, "\n", "%", true)) {
		string::size_type posC = line.find_first_not_of(' ', line.find(' ', line.find_first_not_of(' ', line.find(' ', line.find_first_not_of(' ', line.find(' ') + 1) + 1) + 1) + 1) + 1);
		string::size_type posD = line.find(':', posC + 1);
		dProofs.push_back(line.substr(posC, posD - posC));
	}
	//#cout << FctHelper::vectorString(dProofs) << endl;

	//#for (const string& dProof : dProofs)
	//#	DlProofEnumerator::printProofs( { dProof }, DlFormulaStyle::PolishStandard, false, true, 2, true, nullptr, nullptr, true);
	//#exit(0);

	DlProofEnumerator::printProofs(dProofs, DlFormulaStyle::PolishStandard, false, true, 1, true, nullptr, &outputFile, true);
	string fileString;
	if (!FctHelper::readFile(outputFile, fileString)) {
		cerr << "Invalid file path" << endl;
		return 0;
	}
	fileString = regex_replace(fileString, regex("    [^\n]+\n"), "");
	fileString = regex_replace(fileString, regex("\\[[0-9]+\\] "), "");
	fileString = regex_replace(fileString, regex(" = [^\n]+\n"), "\n");
	//#cout << fileString << flush;
	vector<string> formulas = FctHelper::stringSplit(fileString, "\n");
	stringstream ss;
	ss << "formulas(hints).\n\n";
	for (const string& f : formulas)
		if (!f.empty())
			ss << prover9Formula(f) << "\n";
	ss << "\nend_of_list.\n";
	if (!FctHelper::writeToFile(outputFile, ss.str()))
		cerr << "Failed." << endl;
	else
		cout << ss.str().length() << " bytes written to \"" << outputFile << "\"." << endl;
	return 0;
#endif //###
#if 0 //### ./prover9OutputConverter ; parse proofs from Prover9 output
	// NOTE: Requires '#include <regex>'.
	// e.g. ./prover9OutputConverter w2-A2.out data/w2-A2.txt
	if (argc <= 1) {
		cerr << "Need 1. path to file with Prover9 output. Optional: 2. output file path" << endl;
		return 0;
	}
	string _outputFile;
	string* outputFile = nullptr;
	if (argc >= 3) {
		_outputFile = argv[2];
		outputFile = &_outputFile;
	}

	// 1. Extract proof steps.
	map<size_t, string> formulas;
	map<size_t, string> reasons;
	map<size_t, set<string>> labels;
	set<size_t> finalIndices;
	{
		string content;
		if (!FctHelper::readFile(argv[1]/*"D:/Dropbox/eclipse/pmGenerator/Release64bitDynamicGcc11.3/w2-proof-l2_1.txt"*/, content)) {
			cerr << "Invalid file path" << endl;
			return 0;
		}
		boost::replace_all(content, "\r\n", "\n");
		stringstream ss(content);
		string line;
		smatch m;
		while (getline(ss, line))
			if (regex_search(line, m, regex("[0-9]+ ")) && !m.position()) {
				string id_str = line.substr(0, m.length() - 1);
				size_t id = strtoull(id_str.c_str(), nullptr, 10);
				line = line.substr(FctHelper::digitsNum_uint64(id) + 1);
				//#cout << "[" << id << "] " << line << endl;

				string::size_type pos = line.find("  ");
				string step = line.substr(0, pos);
				string type = line.substr(pos + 2);
				//#cout << "[" << id << "] \"" << step << "\" ; \"" << type << "\"" << endl;
				bool isPos = step.starts_with("t(");
				bool isNeg = step.starts_with("-t(");
				bool isEnd = step.starts_with("$F");
				if (!isPos && !isNeg && !isEnd) {
					cerr << "[" << id << "] Step \"" << step << "\" starts with neither \"t(\", nor \"-t(\", nor \"$F\"." << endl;
					return 0;
				}
				if (!step.ends_with(".")) {
					cerr << "[" << id << "] Step \"" << step << "\" does not end with '.'." << endl;
					return 0;
				}
				if (!type.starts_with("[")) {
					cerr << "[" << id << "] Type \"" << type << "\" does not start with '['." << endl;
					return 0;
				}
				if (!type.ends_with("].")) {
					cerr << "[" << id << "] Type \"" << type << "\" does not end with \"].\"." << endl;
					return 0;
				}
				string formula;
				string reason = type.substr(1, type.length() - 3);
				vector<string> labelSeq;
				pos = step.find(" # ");
				if (pos == string::npos) {
					formula = step.substr(0, step.length() - 1);
				} else {
					formula = step.substr(0, pos);
					while (pos != string::npos) {
						string::size_type nextPos = step.find(" # ", pos + 1);
						if (nextPos == string::npos)
							labelSeq.push_back(step.substr(pos + 3, step.length() - pos - 4)); // without ending '.'
						else
							labelSeq.push_back(step.substr(pos + 3, nextPos - pos - 3));
						pos = nextPos;
					}
				}
				//#cout << "[" << id << "] formula = \"" << formula << "\", reason = \"" << reason << "\", labelSeq = " << FctHelper::vectorStringF(labelSeq, [](const string& s) { return "\"" + s + "\""; }) << endl;
				formulas.emplace(id, formula);
				reasons.emplace(id, reason);
				labels.emplace(id, set<string>(labelSeq.begin(), labelSeq.end()));
				if (isEnd)
					finalIndices.emplace(id);
			}
	}

	// 2. Extract assumptions.
	unordered_set<size_t> isModusPonensAssumption;
	unordered_set<size_t> isNecessitationAssumption;
	unordered_map<size_t, string> isGoalDeclaration;
	for (const pair<const size_t, set<string>>& p : labels) {
		const set<string>& m = p.second;
		if (m.count("label(non_clause)")) {
			//cout << FctHelper::setString(m) << endl;
			if (m.count("label(MP)"))
				isModusPonensAssumption.emplace(p.first);
			if (m.count("label(NE)"))
				isNecessitationAssumption.emplace(p.first);
			if (m.count("label(goal)")) {
				if (m.size() < 3) {
					cerr << "[" << p.first << "] Goal is missing a custom label." << endl;
					return 0;
				}
				string name;
				for (set<string>::const_iterator it = m.begin(); it != m.end(); ++it)
					if (*it != "label(non_clause)" && *it != "label(goal)") {
						const string& s = *it;
						if (s.starts_with("label(") && s.ends_with(")")) {
							name = s.substr(6, s.length() - 7);
							break;
						} else if (s.starts_with("answer(") && s.ends_with(")")) {
							name = s.substr(7, s.length() - 8);
							break;
						}
					}
				if (name.empty()) {
					cerr << "[" << p.first << "] Goal is missing a custom label." << endl;
					return 0;
				}
				isGoalDeclaration.emplace(p.first, name);
			}
		}
	}
	//#cout << "isModusPonensAssumption = " << FctHelper::setString(set<size_t>(isModusPonensAssumption.begin(), isModusPonensAssumption.end())) << endl;
	//#cout << "isNecessitationAssumption = " << FctHelper::setString(set<size_t>(isNecessitationAssumption.begin(), isNecessitationAssumption.end())) << endl;
	//#cout << "isGoalDeclaration = " << FctHelper::mapString(map<size_t, string>(isGoalDeclaration.begin(), isGoalDeclaration.end())) << endl;

	// 3. Obtain connections.
	unordered_set<size_t> isModusPonens;
	unordered_set<size_t> isNecessitation;
	unordered_map<size_t, string> isAxiom;
	unordered_map<size_t, string> isGoalNegation;
	auto toParamList = [](const string& s) {
		vector<size_t> paramList;
		vector<string> args = FctHelper::stringSplit(s, ",");
		for (const string& a : args) {
			size_t link = 0;
			try {
				link = strtoull(a.c_str(), nullptr, 10);
			} catch (...) {
			}
			if (link)
				paramList.push_back(link);
		}
		return paramList;
	};
	map<size_t, array<size_t, 2>> refs;
	map<size_t, string> conclusionsById;
	for (map<size_t, string>::const_iterator it = reasons.begin(); it != reasons.end(); ++it) {
		//#cout << it->first << ":" << it->second << endl;
		const string& reason = it->second;
		if (reason.starts_with("hyper(")) {
			string link_str = reason.substr(6, reason.length() - 7);
			vector<size_t> params = toParamList(link_str);
			//#cout << "[" << it->first << ", hyper] " << link_str << " ; " << FctHelper::vectorString(params) << endl;
			if (isModusPonens.count(params[0])) {
				if (params.size() != 3) {
					cerr << "[" << it->first << "] (MP) Hyper param list has length " << params.size() << " != 3." << endl;
					return 0;
				}
				refs.emplace(it->first, array<size_t, 2> { params[1], params[2] });
			} else if (isNecessitation.count(params[0])) {
				if (params.size() != 2) {
					cerr << "[" << it->first << "] (NE) Hyper param list has length " << params.size() << " != 2." << endl;
					return 0;
				}
				refs.emplace(it->first, array<size_t, 2> { params[1], 0 });
			} else {
				cerr << "[" << it->first << "] Hyper param list does not start with (MP) (but with " << params[0] << ")." << endl;
				return 0;
			}

		} else if (reason.starts_with("resolve(")) {
			string link_str = reason.substr(8, reason.length() - 9);
			vector<size_t> params = toParamList(link_str);
			//cout << "[" << it->first << ", resolve] " << link_str << " ; " << FctHelper::vectorString(params) << endl;
			if (params.size() != 2) {
				cerr << "[" << it->first << "] Resolve param list has length " << params.size() << " != 2." << endl;
				return 0;
			}
			// One param needs to be in isGoalNegation, the other one should be the conclusion.
			if (isGoalNegation.count(params[0]))
				conclusionsById.emplace(params[1], isGoalNegation.at(params[0]));
			else if (isGoalNegation.count(params[1]))
				conclusionsById.emplace(params[0], isGoalNegation.at(params[1]));
			else {
				cerr << "[" << it->first << "] Resolve param list is missing a goal negation. (isGoalNegation: " << FctHelper::mapString(map<size_t, string>(isGoalNegation.begin(), isGoalNegation.end())) << ")" << endl;
				return 0;
			}
		} else if (reason.starts_with("clausify(")) {
			string link_str = reason.substr(9, reason.length() - 10);
			//#cout << "[" << it->first << ", clausify] " << link_str << endl;
			size_t link = strtoull(link_str.c_str(), nullptr, 10);
			if (isModusPonensAssumption.count(link))
				isModusPonens.emplace(it->first);
			else if (isNecessitationAssumption.count(link))
				isNecessitation.emplace(it->first);
			else {
				cerr << "[" << it->first << "] " << "Clausified non-(MP)/(NE) rule." << endl;
				return 0;
			}
		} else if (reason.starts_with("deny(")) {
			string link_str = reason.substr(5, reason.length() - 6);
			//#cout << "[" << it->first << ", deny] " << link_str << endl;
			size_t link = strtoull(link_str.c_str(), nullptr, 10);
			if (!isGoalDeclaration.count(link)) {
				cerr << "[" << it->first << "] Denied non-goal." << endl;
				return 0;
			}
			isGoalNegation.emplace(it->first, isGoalDeclaration.at(link));
		} else if (reason == "assumption") {
			if (!isModusPonensAssumption.count(it->first) && !isNecessitationAssumption.count(it->first)) {
				const set<string>& s = labels.at(it->first);
				if (s.size() > 1) {
					cerr << "[" << it->first << "] Axiom resolve has " << s.size() << " != 1 labels. (labels: " << FctHelper::setString(s) << ")" << endl;
					return 0;
				}
				string label = *s.begin();
				if (!label.starts_with("label(") || !label.ends_with(")")) {
					cerr << "[" << it->first << "] Axiom resolve has invalid label \"" << label << "\"." << endl;
					return 0;
				}
				label = label.substr(6, label.length() - 7);
				//#cout << "[" << it->first << ", assumption] " << it->second << " (axiom: " << label << ")" << endl;
				isAxiom.emplace(it->first, label);
			}
		}
	}

	// 4. Obtain axiom order
	map<string, set<size_t>> axiomNames;
	map<size_t, string> axioms;
	for (const pair<const size_t, string>& p : isAxiom)
		axiomNames[p.second].emplace(p.first);
	size_t num = 1;
	for (const pair<const string, set<size_t>>& p : axiomNames) {
		if (num > 35) {
			cerr << "Too many axioms." << endl;
			return 0;
		}
		string ax = num < 10 ? to_string(num) : string { char('a' - 10 + num) };
		for (size_t id : p.second)
			axioms.emplace(id, ax);
		num++;
	}
	cout << "Axiom translations: " << FctHelper::mapStringF(axioms, [&](const pair<const size_t, string>& p) { return "(id:" + to_string(p.first) + ",name:" + isAxiom.at(p.first) + ",translation:" + p.second + ")"; }) << endl;

	// 5. Build proofs.
	for (const pair<const size_t, string>& conclusion : conclusionsById) {
		cout << "% " << conclusion.second << " : " << formulas[conclusion.first] << endl;

		set<size_t> relevantIndices;
		set<size_t> recent;
		if (!isAxiom.count(conclusion.first))
			recent.emplace(conclusion.first);
		while (!recent.empty()) {
			relevantIndices.insert(recent.begin(), recent.end());
			set<size_t> newCandidates;
			for (size_t i : recent) {
				const array<size_t, 2>& a = refs.at(i);
				if (!isAxiom.count(a[0]))
					newCandidates.emplace(a[0]);
				if (a[1] && !isAxiom.count(a[1]))
					newCandidates.emplace(a[1]);
			}
			recent = newCandidates;
		}
		//#cout << "relevantIndices = " << FctHelper::setString(relevantIndices) << endl;
		unordered_map<size_t, size_t> idTranslations;
		for (size_t id : relevantIndices)
			idTranslations.emplace(id, idTranslations.size());
		//#cout << "idTranslations = " << FctHelper::mapString(map<size_t, size_t>(idTranslations.begin(), idTranslations.end())) << endl;

		vector<string> abstractDProof(relevantIndices.size());
		for (size_t id : relevantIndices) {
			size_t i = idTranslations.at(id);
			const array<size_t, 2>& a = refs.at(id);
			if (a[1]) // (MP)
				abstractDProof[i] = "D" + (isAxiom.count(a[1]) ? axioms.at(a[1]) : "[" + to_string(idTranslations.at(a[1])) + "]") + (isAxiom.count(a[0]) ? axioms.at(a[0]) : "[" + to_string(idTranslations.at(a[0])) + "]");
			else // (NE)
				abstractDProof[i] = "N" + (isAxiom.count(a[0]) ? axioms.at(a[0]) : "[" + to_string(idTranslations.at(a[0])) + "]");
		}
		//#cout << FctHelper::vectorString(abstractDProof) << endl;

		vector<DRuleParser::AxiomInfo> customAxioms;
		for (const pair<const string, set<size_t>>& p : axiomNames) {
			size_t id = *p.second.begin();
			string axStr = formulas.at(id);
			if (!axStr.starts_with("t(") || !axStr.ends_with(")")) {
				cerr << "[" << id << "] Invalid axiom formula \"" << axStr << "\"." << endl;
				return 0;
			}

			//Translate formula to polish notation with variable strings encapsulated by '<' and '>', e.g. "t(i(x,i(i(y,i(x,z)),i(i(n(z),i(i(n(u),w),y)),i(u,z)))))" -> "C<x>CC<y>C<x><z>CCN<z>CCN<u><w><y>C<u><z>"
			axStr = axStr.substr(2, axStr.length() - 3);
			boost::replace_all(axStr, "i(", "C(");
			boost::replace_all(axStr, "n(", "N(");
			boost::replace_all(axStr, "nece(", "L(");
			boost::replace_all(axStr, "(", "<");
			boost::replace_all(axStr, ")", ">");
			boost::replace_all(axStr, ",", "><");
			axStr = regex_replace(axStr, regex(">+"), ">");
			axStr = regex_replace(axStr, regex("<+"), "<");
			boost::replace_all(axStr, "<C", "C");
			boost::replace_all(axStr, "<N", "N");
			boost::replace_all(axStr, "<L", "L");

			shared_ptr<DlFormula> f;
			if (!DlCore::fromPolishNotation(f, axStr)) {
				cerr << "[" << id << "] Invalid axiom formula \"" << axStr << "\"." << endl;
				return 0;
			}
			customAxioms.push_back(DRuleParser::AxiomInfo(axioms.at(id), f));
		}

		vector<shared_ptr<DlFormula>> conclusions;
		bool normalPolishNotation = true; //###
		//#cout << "abstractDProof = " << FctHelper::vectorString(abstractDProof) << endl;
		abstractDProof = DRuleParser::recombineAbstractDProof(abstractDProof, conclusions, &customAxioms, nullptr, nullptr, 2, nullptr, true, -2);
		//#cout << "conclusions = " << FctHelper::vectorStringF(conclusions, [](const shared_ptr<DlFormula>& f) { return DlCore::toPolishNotation(f); }) << endl;
		auto print = [&](ostream& mout) -> string::size_type {
			string::size_type bytes = 0;
			for (const DRuleParser::AxiomInfo& ax : customAxioms) {
				string f = normalPolishNotation ? DlCore::toPolishNotation(ax.refinedAxiom) : DlCore::toPolishNotation_noRename(ax.refinedAxiom);
				mout << "    " << f << " = " << ax.name << "\n";
				bytes += 9 + f.length();
			}
			for (size_t i = 0; i < abstractDProof.size(); i++) {
				string f = normalPolishNotation ? DlCore::toPolishNotation(conclusions[i]) : DlCore::toPolishNotation_noRename(conclusions[i]);
				const string& p = abstractDProof[i];
				mout << "[" << i << "] " << f << " = " << p << "\n";
				bytes += 7 + FctHelper::digitsNum_uint64(i) + f.length() + p.length();
			}
			return bytes;
		};
		chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
		if (outputFile) {
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
	}
	return 0;
#endif //###
#if 0 //### ./searchShorterSubproofs ; search shorter proofs for conclusions used in a given proof summary
	// NOTE: Requires '#include "logic/DlCore.h"' and '#include <numeric>'.
	// e.g. ./searchShorterSubproofs data/w3.txt 0 data/tmp.txt CpCqp,CCpCqrCCpqCpr,CCNpNqCqp,Cpp,CCpqCCqrCpr,CCNppp,CpCNpq 0
	if (argc <= 1) {
		cerr << "Need 1. path to proof summary. Optional: 2. necessitation limit (or -1), 3. output file path, 4. target theorems in normal Polish notation, 5. extracted system ID" << endl;
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
	if (argc >= 5) {
		vector<string> theorems = FctHelper::stringSplit(argv[4], ",");
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
	string _extractedSystemId;
	string* extractedSystemId = nullptr;
	if (argc >= 6) {
		_extractedSystemId = argv[5];
		extractedSystemId = &_extractedSystemId;
	}

	// 1. Obtain all conclusions used by proof summary (i.e. all which are relevant).
	string filterForTheorems = ".";
	DlProofEnumerator::recombineProofSummary(proofSummaryFile, true, nullptr, 1, SIZE_MAX, true, false, &filterForTheorems, true, SIZE_MAX, 134217728, false, false, &tmpFile, false);
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
	improvedAbstractDProof = DRuleParser::recombineAbstractDProof(improvedAbstractDProof, improvedConclusions, &customAxioms, targetTheorems, nullptr, 2, &requiredIntermediateResults, true, -2);

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
#if 0 //### ./uniteLists ; combine comma-separated ordered lists of strings
	// e.g. ./uniteLists data/summary-formulas.txt data/summary-formulas1.txt,data/summary-formulas2.txt,data/summary-formulas3.txt
	if (argc <= 2) {
		cerr << "Need 1. path for output file, and 2. comma-separated list of paths to files with comma-separated elements." << endl;
		return 0;
	}
	string outputFile = argv[1];
	vector<string> inputFiles = FctHelper::stringSplit(argv[2], ",");
	set<string, cmpStringGrow> unionOfLists;
	for (const string& inputFile : inputFiles) {
		string fileString;
		if (!FctHelper::readFile(inputFile, fileString))
			throw runtime_error("Failed to read file \"" + inputFile + "\".");

		// Erase all '\r', '\n', '\t', ' ', and lines starting with '%'. ; NOTE: Much faster than using regular expressions.
		bool startOfLine = true;
		bool erasingLine = false;
		fileString.erase(remove_if(fileString.begin(), fileString.end(), [&](const char c) {
			switch (c) {
			case '\r':
			case '\n':
				startOfLine = true;
				erasingLine = false;
				return true;
			case '\t':
			case ' ':
				startOfLine = false;
				return true;
			case '%':
				if (startOfLine) {
					startOfLine = false;
					erasingLine = true;
				}
				return erasingLine;
			default:
				startOfLine = false;
				return erasingLine;
			}
		}), fileString.end());

		vector<string> elements = FctHelper::stringSplit(fileString, ",");
		cout << "Found " << elements.size() << " separated element" << (elements.size() == 1 ? "" : "s") << " in \"" << inputFile << "\"." << endl;
		unionOfLists.insert(elements.begin(), elements.end());
	}
	cout << "In total, found " << unionOfLists.size() << " different element" << (unionOfLists.size() == 1 ? "" : "s") << " in " << inputFiles.size() << " file" << (inputFiles.size() == 1 ? "" : "s") << "." << endl;
	if (!unionOfLists.empty())
		cout << "Smallest element: " << *unionOfLists.begin() << "\n                  (length " << unionOfLists.begin()->length() << ")\nLargest element:  " << *unionOfLists.rbegin() << "\n                  (length " << unionOfLists.rbegin()->length() << ")" << endl;
	string result = FctHelper::setString(unionOfLists, { }, { }, ",");
	FctHelper::writeToFile(outputFile, result);
	cout << result.length() << " bytes written to \"" << outputFile<< "\"." << endl;
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
			} else if (command == "transform") { // --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-u] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-b] [-z] [-y] [-f] [-o <output file>] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::TransformProofSummary, map<string, string> { { "string", argv[++i] }, { "conclusionsWithHelperProofs", "" }, { "filterForTheorems", "" }, { "outputFile", "" } }, map<string, int64_t> { { "minUseAmountToCreateHelperProof", 2 }, { "maxLengthToKeepProof", -1 }, { "storeIntermediateUnfoldingLimit", -1 }, { "maxLengthToComputeDProof", 134217728 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "normalPolishNotation", false }, { "printInfixUnicode", false }, { "abstractProofStrings", true }, { "removeDuplicateConclusions", false }, { "compress", false }, { "compress_concurrent", true }, { "debug", false }, { "whether -s was called", false }, { "whether -t was called", false } });
			} else if (command == "unfold") { // --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-f] [-o <output file>] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::UnfoldProofSummary, map<string, string> { { "string", argv[++i] }, { "filterForTheorems", "" }, { "outputFile", "" } }, map<string, int64_t> { { "storeIntermediateUnfoldingLimit", -1 }, { "maxLengthToComputeDProof", 134217728 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "normalPolishNotation", false }, { "wrap", false }, { "debug", false }, { "whether -t was called", false } });
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
		case 'w':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent());
			case Task::ApplyReplacements: //        -a -w (wrap results)
			case Task::UnfoldProofSummary: // --unfold -w (wrap results)
				tasks.back().bln["wrap"] = true;
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
					ss << ++index << ". recombineProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << (t.bln["whether -s was called"] ? "\"" + t.str["conclusionsWithHelperProofs"] + "\"" : "null") << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << (size_t) t.num["maxLengthToKeepProof"] << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << bstr(t.bln["printInfixUnicode"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["removeDuplicateConclusions"]) << ", " << bstr(t.bln["compress"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ", " << bstr(t.bln["compress_concurrent"]) << ")\n";
					break;
				case Task::UnfoldProofSummary: // --unfold
					ss << ++index << ". unfoldProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["wrap"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")\n";
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
			case Task::TransformProofSummary: // --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-u] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-b] [-z] [-y] [-f] [-o <output file>] [-d]
				cout << "[Main] Calling recombineProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << (t.bln["whether -s was called"] ? "\"" + t.str["conclusionsWithHelperProofs"] + "\"" : "null") << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << (size_t) t.num["maxLengthToKeepProof"] << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << bstr(t.bln["printInfixUnicode"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["removeDuplicateConclusions"]) << ", " << bstr(t.bln["compress"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ", " << bstr(t.bln["compress_concurrent"]) << ")." << endl;
				if (!t.bln["useInputFile"])
					boost::replace_all(t.str["string"], ",", "\n");
				DlProofEnumerator::recombineProofSummary(t.str["string"], t.bln["useInputFile"], t.bln["whether -s was called"] ? &t.str["conclusionsWithHelperProofs"] : nullptr, (unsigned) t.num["minUseAmountToCreateHelperProof"], t.num["maxLengthToKeepProof"], t.bln["normalPolishNotation"], t.bln["printInfixUnicode"], t.bln["whether -t was called"] ? &t.str["filterForTheorems"] : nullptr, t.bln["abstractProofStrings"], t.num["storeIntermediateUnfoldingLimit"], t.num["maxLengthToComputeDProof"], t.bln["removeDuplicateConclusions"], t.bln["compress"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["debug"], t.bln["compress_concurrent"]);
				break;
			case Task::UnfoldProofSummary: // --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-f] [-o <output file>] [-d]
				cout << "[Main] Calling unfoldProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << (size_t) t.num["storeIntermediateUnfoldingLimit"] << ", " << (size_t) t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["wrap"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				if (!t.bln["useInputFile"])
					boost::replace_all(t.str["string"], ",", "\n");
				DlProofEnumerator::unfoldProofSummary(t.str["string"], t.bln["useInputFile"], t.bln["normalPolishNotation"], t.bln["whether -t was called"] ? &t.str["filterForTheorems"] : nullptr, t.num["storeIntermediateUnfoldingLimit"], t.num["maxLengthToComputeDProof"], t.bln["wrap"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["debug"]);
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
