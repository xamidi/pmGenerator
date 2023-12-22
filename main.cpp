#include "helper/FctHelper.h"
#include "helper/Version.h"
#include "metamath/DRuleReducer.h"
#include "logic/DlProofEnumerator.h"

#include <boost/algorithm/string.hpp>

#include <cstring>
#include <ctime>
#include <regex>
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
				"    -g <limit or -1> [-u] [-q <limit>] [-s]\n"
				"       Generate proof files ; at ./data/[<hash>/]/dProofs-withConclusions/ when '-s' unspecified ; otherwise at ./data/[<hash>/]/dProofs-withoutConclusions/\n"
				"         -u: unfiltered (significantly faster, but generates redundant proofs)\n"
				"         -q: limit number of proof candidate strings queued per worker thread (may lower memory requirements for systems with low acceptance rates)\n"
				"         -s: proof files without conclusions, requires additional parsing\n";
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
				"    --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-f] [-o <output file>] [-d]\n"
				"       Transform proof summary (as by '--parse [...] -s') into recombined variant ; ignores configured system (proof summaries provide their own axioms) ; \",\" represents LF\n"
				"         -s: list a subproof with its conclusion if it occurs in the given comma-separated list of conclusions\n"
				"         -j: join common subproofs together when they are used at least a given amount of times ; default: 2\n"
				"         -p: only keep subproofs with primitive lengths not exceeding the given limit ; default: -1\n"
				"         -n: specify and print formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -t: only transform proofs of specified theorems (proven by subsequences of the input), given by a comma-separated string ; \".\" to keep all conclusions ; default: final theorem only\n"
				"         -e: keep expanded proof strings ; show fully detailed condensed detachment proofs rather than allowing them to contain references\n"
				"         -i: decrease memory requirements but increase time consumption by not storing intermediate unfoldings that exceed a certain length ; default: -1\n"
				"         -l: abort computation when combined requested proof sequences exceed the given limit in bytes ; default: 134217728 (i.e. 128 MiB)\n"
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
				"    --search <string> [-n] [-s] [-w] [-p] [-f] [-d]\n"
				"       Search in proof files at ./data/[<hash>/]/dProofs-withConclusions/ via comma-separated string of full formulas or full proofs ; [Hint: Generate missing files with '--variate 1 -s'.]\n"
				"         -n: specify formulas in normal Polish notation (e.g. \"CpCqp\"), not with numeric variables (e.g. \"C0C1.0\")\n"
				"         -s: search for schemas of the given formulas\n"
				"         -w: search whole collections of schemas (i.e. enable multiple results per term) ; entails '-s'\n"
				"         -p: search proofs (rather than conclusions) ; used only when '-n' and '-s' unspecified\n"
				"         -f: search terms are given by input file path (where a comma-separated string is stored), ignoring all CR, LF, whitespace, and lines starting with '%'\n"
				"         -d: print debug information\n";
		_[Task::ExtractFromProofFiles] =
				"    --extract [-t <limit or -1>] [-o <output file>] [-s] [-# <amount up to 35>] [-h <string>] [-f] [-d]\n"
				"       Various options to extract information from proof files ; [Hint: Generate missing files with '--variate 1 -s'.]\n"
				"         -t: compose file with up to the given amount of smallest conclusions that occur in proof files ; includes origins, symbolic lengths, proofs, and formulas in normal Polish notation\n"
				"         -o: specify output file path for '-t' ; relative to effective data location ; default: \"top<amount>SmallestConclusions_<min proof length>to<max proof length>Steps<unfiltered info>.txt\"\n"
				"         -s: redundant schema removal for '-t' ; very time-intensive for requesting huge collections from unfiltered proof files - better pre-filter via '-g' or '-m' instead ; default: false\n"
				"         -#: initialize proof system at ./data/[<hash>/]/extraction-<id>/ with the given amount of smallest filtered conclusions that occur in proof files ; specify with '-c <parent system> -e <id>'\n"
				"         -h: similar to '-#' ; hand-pick conclusions with a comma-separated string of proofs\n"
				"         -f: proofs for '-h' are given by input file path (where a comma-separated string is stored), ignoring all CR, LF, whitespace, and lines starting with '%'\n"
				"         -d: print debug information\n";
		_[Task::IterateProofCandidates] =
				"    --iterate [-u] [-s]\n"
				"       Iterate proof candidates currently next up for generation and print (and store for custom proof systems) their amount for prediction purposes\n"
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

void orderLog(const string& path) {
	string s;
	if (!FctHelper::readFile(path, s)) {
		cerr << "Failed to read file at \"" + path + "\"." << endl;
		return;
	}
	vector<string> lines = FctHelper::stringSplit(s, "\n");
	set<size_t> configLineNumbers;
	map<size_t, string> configLines;
	set<size_t> callLineNumbers;
	map<size_t, string> callLines;
	set<size_t> startLineNumbers;
	map<size_t, string> startLines;
	set<size_t> completeLineNumbers;
	map<size_t, string> completeLines;
	for (size_t i = 0; i < lines.size(); i++) {
		const string& line = lines[i];
		smatch m;
		if (regex_search(line, m, regex("\\[Rank [0-9]+[^\\]]+\\] Calling reset.+, silently\\."))) {
			configLineNumbers.emplace(i);
			//cout << "#1 Match for: " << line << endl;
			string::size_type a = line.find("[Rank ") + 6;
			size_t rank = stoll(line.substr(a, line.find(" ", a) - a + 1));
			configLines.emplace(rank, line);

		}
		if (regex_search(line, m, regex("\\[Rank [0-9]+[^\\]]+\\] Calling mpi_"))) {
			callLineNumbers.emplace(i);
			//cout << "#2 Match for: " << line << endl;
			string::size_type a = line.find("[Rank ") + 6;
			size_t rank = stoll(line.substr(a, line.find(" ", a) - a + 1));
			callLines.emplace(rank, line);
		}
		if (regex_search(line, m, regex("started\\. \\[rank [0-9]+ on"))) {
			startLineNumbers.emplace(i);
			//cout << "#3 Match for: " << line << endl;
			string::size_type a = line.find(". [rank ") + 8;
			size_t rank = stoll(line.substr(a, line.find(" ", a) - a + 1));
			startLines.emplace(rank, line);
		}
		if (regex_search(line, m, regex("complete\\. \\[rank [0-9]+ on"))) {
			string::size_type a = line.find(". [rank ") + 8;
			size_t rank = stoll(line.substr(a, line.find(" ", a) - a + 1));
			if (rank) {
				completeLineNumbers.emplace(i);
				//cout << "#4 Match for: " << line << endl;
				completeLines.emplace(rank, line);
			}
		}
	}
	set<size_t> targetLineNumbers = configLineNumbers;
	targetLineNumbers.insert(callLineNumbers.begin(), callLineNumbers.end());
	targetLineNumbers.insert(startLineNumbers.begin(), startLineNumbers.end());
	targetLineNumbers.insert(completeLineNumbers.begin(), completeLineNumbers.end());
	size_t changeAmount = configLineNumbers.size() + callLineNumbers.size() + startLineNumbers.size() + completeLineNumbers.size();
	if (targetLineNumbers.size() != changeAmount) {
		cerr << "Overlappings found! Aborting." << endl;
		return;
	}
	vector<size_t> indices(targetLineNumbers.begin(), targetLineNumbers.end());
	size_t i = 0;
	for (const pair<const size_t, string>& p : configLines)
		lines[indices[i++]] = p.second;
	for (const pair<const size_t, string>& p : callLines)
		lines[indices[i++]] = p.second;
	for (const pair<const size_t, string>& p : startLines)
		lines[indices[i++]] = p.second;
	for (const pair<const size_t, string>& p : completeLines)
		lines[indices[i++]] = p.second;
	FctHelper::writeToFile(path, FctHelper::stringJoin("\n", lines));
	cout << "Permuted " << indices.size() << " lines" << endl;
}

//#include <cmath>
int main(int argc, char* argv[]) { // argc = 1 + N, argv = { <command>, <arg1>, ..., <argN> }
#if 0 //### entropy calculation
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
#if 0 //### string sort performance test (due to long durations of CpCCNqCCNrsCptCCtqCrq / 0df075acc552c62513b49b6ed674bfcde1c1b018e532c665be229314 generations - formulas with long prefixes)
	chrono::time_point<chrono::steady_clock> startTime = chrono::steady_clock::now();
	uint32_t num = 61;
	vector<string> conclusions;
	{
		vector<string> lines;
		{
			string s;
			FctHelper::readFile("data/0df075acc552c62513b49b6ed674bfcde1c1b018e532c665be229314/dProofs-withConclusions/dProofs" + to_string(num) + ".txt", s);
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to read " << s.length() << " bytes." << endl;
			// e.g. 6367.70 ms (6 s 367.70 ms) taken to read 1786902420 bytes.
			startTime = chrono::steady_clock::now();
			lines = FctHelper::stringSplit(s, "\n");
			cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to split into " << lines.size() << " lines." << endl;
			// e.g. 2200.61 ms (2 s 200.61 ms) taken to split into 3652191 lines.
		}
		cout << "Starting to extract conclusions." << endl;
		startTime = chrono::steady_clock::now();
		conclusions.resize(lines.size());
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to reserve " << lines.size() << " strings." << endl;
		// e.g. 37.75 ms taken to reserve 3652191 strings.
		startTime = chrono::steady_clock::now();
		for (size_t i = 0; i < lines.size(); i++)
			conclusions[i] = lines[i].substr(num + 1);
		cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to extract " << conclusions.size() << " conclusions." << endl;
		// e.g. 924.73 ms taken to extract 3652191 conclusions.
	}
	cout << "Starting to sort conclusions." << endl;
	sort(conclusions.begin(), conclusions.end(), cmpStringGrow()); // around "3435.57 ms (3 s 435.57 ms) taken to sort 3652191 strings"
	//sort(conclusions.begin(), conclusions.end()); // around "3769.33 ms (3 s 769.33 ms) taken to sort 3652191 strings"
	cout << FctHelper::durationStringMs(chrono::duration_cast<chrono::microseconds>(chrono::steady_clock::now() - startTime)) << " taken to sort " << conclusions.size() << " strings." << endl;
	return 0;
#endif //###
#if 0 //### unification finder
	for (size_t w = 1; w <= 15; w += 2) {
		cout << "dProofs" + to_string(w) + ".txt" << endl;
		string s1 = "CCCC0.0C0.0CCC0.0C0.0CNCC1.1C1.1CCC1.1C1.1CC1.1C1.1CCC0.0C0.0CNCC1.1C1.1CCC1.1C1.1CC1.1C1.1"; //"CCCC0.0C0.0CCC0.0C0.0CNC1.1CC1.1C1.1CCC0.0C0.0CNC1.1CC1.1C1.1"; //"CCCC0.0C0.0CCC0.0C0.0CN1C1.1CCC0.0C0.0CN1C1.1"; //"CCC0.0CC0.0CN1C1.1CC0.0CN1C1.1"; //"CCC0.0C1CN2C2.2C1CN2C2.2";
		boost::replace_all(s1, "0", "z");
		boost::replace_all(s1, "1", "y");
		boost::replace_all(s1, "2", "x");
		boost::replace_all(s1, "3", "w");
		boost::replace_all(s1, "4", "v");
		boost::replace_all(s1, "5", "u");
		boost::replace_all(s1, "6", "t");
		boost::replace_all(s1, "7", "s");
		boost::replace_all(s1, "8", "r");
		boost::replace_all(s1, "9", "q");
		shared_ptr<DlFormula> f1;
		DlCore::fromPolishNotation_noRename(f1, s1);
		string content;
		if (!FctHelper::readFile("data/dProofs-withConclusions/dProofs" + to_string(w) + ".txt", content)) {
			cerr << "Failed to read." << endl;
			return 0;
		}
		vector<string> lines = FctHelper::stringSplit(content, "\n");
		for (const string& line : lines) {
			string s2 = line.substr(line.find(':') + 1);
			shared_ptr<DlFormula> f2;
			DlCore::fromPolishNotation_noRename(f2, s2);
			map<string, shared_ptr<DlFormula>> substitutions;
			if (DlCore::tryUnifyTrees(f1, f2, &substitutions)) {
				string s1s2 = DlCore::toPolishNotation_numVars(DlCore::substitute(f1, substitutions));
				cout << "Unification succeeded for " << s2 <<". Result: " << s1s2 << endl;
			}
		}
	}
	return 0;
#endif //###
	//#orderLog("log/custom/tmp.txt"); return 0; // edit multi-node computation logs ; sorts initialization and completion messages with rank numbers for better readability
	//#cout << "argc = " << argc << ", argv = { " << [&]() { string s; for (int i = 0; i < argc; i++) { if (i) s += ", "; s += string { argv[i] }; } return s; }() << " }" << endl;
	auto printUsage = [&](const string& error, Task task) {
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
		return printUsage("", Task::Invalid);
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
	for (int i = 1; i < argc; i++) {
		auto recent = [&](const string& s) {
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
			return printUsage("Invalid argument \"" + string { argv[i] } + "\".", recent("?"));
		const char c = argv[i][1];
		switch (c) {

		// Commands
		case 'c': // -c [-i <file>] [-s <string>] [-n] [-N <limit or -1>] [-l] [-e <id>] [-d]
			if (!mpiArg.empty())
				return printUsage("Invalid argument \"-" + string { c } + "\": Cannot configure after \"" + mpiArg + "\".", Task::Invalid);
			tasks.emplace_back(Task::Customize, map<string, string> { { "axiomString", "C0C1.0,CC0C1.2CC0.1C0.2,CCN0N1C1.0" }, { "axiomFilePath", "" }, { "extractedSystemId", "" } }, map<string, int64_t> { { "necessitationLimit", 0 } }, map<string, bool> { { "useInputFile", false }, { "normalPolishNotation", false }, { "speedupN", true }, { "extractedSystem", false }, { "defaultSystem", false } });
			mpiIgnoreCount++;
			break;
		case 'g': // -g <limit or -1> [-u] [-q <limit>] [-s]
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
			try {
				tasks.emplace_back(Task::Generate, map<string, string> { }, map<string, int64_t> { { "limit", stoi(argv[++i]) }, { "candidateQueueCapacities", 0 } }, map<string, bool> { { "redundantSchemaRemoval", true }, { "withConclusions", true }, { "whether -q was called", false } });
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
				return printUsage("Invalid argument \"-" + string { c } + "\": Can only be combined with preceding configuring commands.", Task::Invalid);
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
			else {
				string param = string(argv[++i]);
				unsigned value;
				if (!FctHelper::toUInt(param, value))
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
			} else if (command == "transform") { // --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-f] [-o <output file>] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::TransformProofSummary, map<string, string> { { "string", argv[++i] }, { "conclusionsWithHelperProofs", "" }, { "filterForTheorems", "" }, { "outputFile", "" } }, map<string, int64_t> { { "minUseAmountToCreateHelperProof", 2 }, { "maxLengthToKeepProof", -1 }, { "storeIntermediateUnfoldingLimit", -1 }, { "maxLengthToComputeDProof", 134217728 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "normalPolishNotation", false }, { "abstractProofStrings", true }, { "debug", false }, { "whether -s was called", false }, { "whether -t was called", false } });
			} else if (command == "unfold") { // --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-f] [-o <output file>] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::UnfoldProofSummary, map<string, string> { { "string", argv[++i] }, { "filterForTheorems", "" }, { "outputFile", "" } }, map<string, int64_t> { { "storeIntermediateUnfoldingLimit", -1 }, { "maxLengthToComputeDProof", 134217728 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "normalPolishNotation", false }, { "wrap", false }, { "debug", false }, { "whether -t was called", false } });
			} else if (command == "search") { // --search <string> [-n] [-s] [-w] [-p] [-f] [-d]
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"--" + command + "\".", recent(command));
				tasks.emplace_back(Task::SearchProofFiles, map<string, string> { { "string", argv[++i] } }, map<string, int64_t> { }, map<string, bool> { { "useInputFile", false }, { "normalPolishNotation", false }, { "searchProofs", false }, { "schemaSearch", false }, { "multiSchemaSearch", false }, { "debug", false } });
			} else if (command == "extract") // --extract [-t <limit or -1>] [-o <output file>] [-s] [-# <amount up to 35>] [-h <string>] [-f] [-d]
				tasks.emplace_back(Task::ExtractFromProofFiles, map<string, string> { { "proofs", "" }, { "outputFile", "" } }, map<string, int64_t> { { "extractToFileAmount", 0 }, { "extractToSystemAmount", 0 } }, map<string, bool> { { "useInputFile", false }, { "useOutputFile", false }, { "allowRedundantSchemaRemoval", false }, { "debug", false }, { "whether -f was called", false }, { "whether -# was called", false }, { "whether -h was called", false } });
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
				tasks.emplace_back(Task::ConclusionLengthPlot, map<string, string> { { "dataLocation", "data" }, { "inputFilePrefix", "dProofs-withConclusions/dProofs" }, { "mout", "" } }, map<string, int64_t> { { "cutX", -1 }, { "cutY", -1 } }, map<string, bool> { { "measureSymbolicLength", false }, { "table", false }, { "debug", false } });
			else
				return printUsage("Invalid argument \"--" + command + "\".", recent(command));
			break;
		}
		// Arguments
		case '#':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
			case Task::ParseAndPrintProofs: // --parse -b (only print conclusions of the given proofs)
				tasks.back().bln["conclusionsOnly"] = true;
				if (!tasks.back().bln["whether -j was called"])
					tasks.back().num["minUseAmountToCreateHelperProof"] = 1;
				break;
			}
			break;
		case 'd':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
			case Task::FileConversion: //          --variate -d (print debug information)
			case Task::ConclusionLengthPlot: //       --plot -d (print debug information)
				tasks.back().bln["debug"] = true;
				break;
			}
			break;
		case 'e':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
			case Task::Customize: // -c -e <id> (specify extracted system with the given identifie)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["extractedSystemId"] = argv[++i];
				tasks.back().bln["extractedSystem"] = true;
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
		case 'l':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
			}
			break;
		case 'n':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
			case Task::Customize: // -c -s <string> (specify axioms by comma-separated string)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["axiomString"] = argv[++i];
				break;
			case Task::Generate: //                      -g -s (proof files without conclusions)
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
			case Task::TransformProofSummary: // --transform -t <string> (only transform proofs of specified theorems)
			case Task::UnfoldProofSummary: //       --unfold -t <string> (obtain proofs of specified theorems)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				tasks.back().str["filterForTheorems"] = argv[++i];
				tasks.back().bln["whether -t was called"] = true;
				break;
			case Task::ExtractFromProofFiles: // --extract -t <limit or -1> (compose file with up to the given amount of smallest conclusions that occur in proof files)
				if (i + 1 >= argc)
					return printUsage("Missing parameter for \"-" + string { c } + "\".", recent(string { c }));
				try {
					tasks.back().num["extractToFileAmount"] = stoi(argv[++i]);
				} catch (...) {
					return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-" + string { c } + "\".", recent(string { c }));
				}
				tasks.back().bln["whether -f was called"] = true;
				break;
			case Task::ConclusionLengthPlot: // --plot -t (table arrangement)
				tasks.back().bln["table"] = true;
				break;
			}
			break;
		case 'u':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
			case Task::Generate: //                      -g -u (unfiltered)
			case Task::IterateProofCandidates: // --iterate -u (use unfiltered proof files)
				tasks.back().bln["redundantSchemaRemoval"] = false;
				break;
			case Task::ParseAndPrintProofs: // --parse -u (print formulas in infix notation with operators as Unicode characters)
				tasks.back().bln["unicodeInfixNotation"] = true;
				break;
			}
			break;
		case 'w':
			switch (lastTask()) {
			default:
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
				return printUsage("Invalid argument \"-" + string { c } + "\".", recent("?"));
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
		default:
			return printUsage("Invalid argument \"" + string { argv[i] } + "\".", recent("?"));
		}
	}
	int mpi_size;
	int mpi_rank;
	if (!mpiArg.empty()) {
		if (tasks.size() > 1 + mpiIgnoreCount)
			return printUsage("Invalid argument \"" + mpiArg + "\": Can only be combined with preceding configuring commands.", Task::Invalid);

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
				case Task::Generate: // -g
					ss << ++index << ". generateDProofRepresentativeFiles(" << (unsigned) t.num["limit"] << ", " << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << (t.bln["whether -q was called"] ? ", " + to_string(size_t(t.num["candidateQueueCapacities"])) : "") << ")\n";
					break;
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
					ss << ++index << ". recombineProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << (t.bln["whether -s was called"] ? "\"" + t.str["conclusionsWithHelperProofs"] + "\"" : "null") << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << t.num["maxLengthToKeepProof"] << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << t.num["storeIntermediateUnfoldingLimit"] << ", " << t.num["maxLengthToComputeDProof"] << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::UnfoldProofSummary: // --unfold
					ss << ++index << ". unfoldProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << t.num["storeIntermediateUnfoldingLimit"] << ", " << t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["wrap"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::SearchProofFiles: // --search
					ss << ++index << ". searchProofFiles(" << (t.bln["useInputFile"] ? "{ }" : "\"" + t.str["string"] + "\"") << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << bstr(t.bln["searchProofs"]) << ", " << (t.bln["multiSchemaSearch"] ? 2 : t.bln["schemaSearch"] ? 1 : 0) << ", " << (t.bln["useInputFile"] ? "\"" + t.str["string"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")\n";
					break;
				case Task::ExtractFromProofFiles: // --extract
					if (t.bln["whether -f was called"])
						ss << ++index << ". extractConclusions(ExtractionMethod::TopListFile, " << (unsigned) t.num["extractToFileAmount"] << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["allowRedundantSchemaRemoval"]) << ", " << bstr(t.bln["debug"]) << ")\n";
					if (t.bln["whether -# was called"])
						ss << ++index << ". extractConclusions(ExtractionMethod::ProofSystemFromTopList, " << (unsigned) t.num["extractToSystemAmount"] << ", null, true, " << bstr(t.bln["debug"]) << ")\n";
					if (t.bln["whether -h was called"])
						ss << ++index << ". extractConclusions(" << (t.bln["useInputFile"] ? "ExtractionMethod::ProofSystemFromFile" : "ExtractionMethod::ProofSystemFromString") << ", 0, \"" << t.str["proofs"] << "\", true, " << bstr(t.bln["debug"]) << ")\n";
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
					ss << ++index << ". printConclusionLengthPlotData(" << bstr(t.bln["measureSymbolicLength"]) << ", " << bstr(t.bln["table"]) << ", " << t.num["cutX"] << ", " << t.num["cutY"] << ", \"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", " << (t.str["mout"].empty() ? "null" : "\"" + t.str["mout"] + "\"") << ", " << bstr(t.bln["debug"]) << ")\n";
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
			case Task::Generate: { // -g <limit or -1> [-u] [-q <limit>] [-s]
				cout << "[Main] Calling generateDProofRepresentativeFiles(" << (unsigned) t.num["limit"] << ", " << bstr(t.bln["redundantSchemaRemoval"]) << ", " << bstr(t.bln["withConclusions"]) << (t.bln["whether -q was called"] ? ", " + to_string(size_t(t.num["candidateQueueCapacities"])) : "") << ")." << endl;
				size_t candidateQueueCapacities = static_cast<size_t>(t.num["candidateQueueCapacities"]);
				DlProofEnumerator::generateDProofRepresentativeFiles((unsigned) t.num["limit"], t.bln["redundantSchemaRemoval"], t.bln["withConclusions"], t.bln["whether -q was called"] ? &candidateQueueCapacities : nullptr);
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
			case Task::TransformProofSummary: // --transform <string> [-s <string>] [-j <limit or -1>] [-p <limit or -1>] [-n] [-t <string>] [-e] [-i <limit or -1>] [-l <limit or -1>] [-f] [-o <output file>] [-d]
				cout << "[Main] Calling recombineProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << (t.bln["whether -s was called"] ? "\"" + t.str["conclusionsWithHelperProofs"] + "\"" : "null") << ", " << (unsigned) t.num["minUseAmountToCreateHelperProof"] << ", " << t.num["maxLengthToKeepProof"] << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << bstr(t.bln["abstractProofStrings"]) << ", " << t.num["storeIntermediateUnfoldingLimit"] << ", " << t.num["maxLengthToComputeDProof"] << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				if (!t.bln["useInputFile"])
					boost::replace_all(t.str["string"], ",", "\n");
				DlProofEnumerator::recombineProofSummary(t.str["string"], t.bln["useInputFile"], t.bln["whether -s was called"] ? &t.str["conclusionsWithHelperProofs"] : nullptr, (unsigned) t.num["minUseAmountToCreateHelperProof"], t.num["maxLengthToKeepProof"], t.bln["normalPolishNotation"], t.bln["whether -t was called"] ? &t.str["filterForTheorems"] : nullptr, t.bln["abstractProofStrings"], t.num["storeIntermediateUnfoldingLimit"], t.num["maxLengthToComputeDProof"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["debug"]);
				break;
			case Task::UnfoldProofSummary: // --unfold <string> [-n] [-t <string>] [-i <limit or -1>] [-l <limit or -1>] [-w] [-f] [-o <output file>] [-d]
				cout << "[Main] Calling unfoldProofSummary(\"" << t.str["string"] << "\", " << bstr(t.bln["useInputFile"]) << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["whether -t was called"] ? "\"" + t.str["filterForTheorems"] + "\"" : "null") << ", " << t.num["storeIntermediateUnfoldingLimit"] << ", " << t.num["maxLengthToComputeDProof"] << ", " << bstr(t.bln["wrap"]) << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				if (!t.bln["useInputFile"])
					boost::replace_all(t.str["string"], ",", "\n");
				DlProofEnumerator::unfoldProofSummary(t.str["string"], t.bln["useInputFile"], t.bln["normalPolishNotation"], t.bln["whether -t was called"] ? &t.str["filterForTheorems"] : nullptr, t.num["storeIntermediateUnfoldingLimit"], t.num["maxLengthToComputeDProof"], t.bln["wrap"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["debug"]);
				break;
			case Task::SearchProofFiles: // --search <string> [-n] [-s] [-w] [-p] [-f] [-d]
				cout << "[Main] Calling searchProofFiles(" << (t.bln["useInputFile"] ? "{ }" : "\"" + t.str["string"] + "\"") << ", " << bstr(t.bln["normalPolishNotation"]) << ", " << (t.bln["multiSchemaSearch"] ? 2 : t.bln["schemaSearch"] ? 1 : 0) << ", " << bstr(t.bln["schemaSearch"]) << ", " << (t.bln["useInputFile"] ? "\"" + t.str["string"] + "\"" : "null") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				DlProofEnumerator::searchProofFiles(t.bln["useInputFile"] ? vector<string> { } : FctHelper::stringSplit(t.str["string"], ","), t.bln["normalPolishNotation"], t.bln["searchProofs"], t.bln["multiSchemaSearch"] ? 2 : t.bln["schemaSearch"] ? 1 : 0, t.bln["useInputFile"] ? &t.str["string"] : nullptr , t.bln["debug"]);
				break;
			case Task::ExtractFromProofFiles: // --extract [-t <limit or -1>] [-o <output file>] [-s] [-# <amount up to 35>] [-h <string>] [-f] [-d]
				if (t.bln["whether -f was called"]) {
					cout << "[Main] Calling extractConclusions(ExtractionMethod::TopListFile, " << (unsigned) t.num["extractToFileAmount"] << ", " << (t.bln["useOutputFile"] ? "\"" + t.str["outputFile"] + "\"" : "null") << ", " << bstr(t.bln["allowRedundantSchemaRemoval"]) << ", " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::extractConclusions(ExtractionMethod::TopListFile, (unsigned) t.num["extractToFileAmount"], t.bln["useOutputFile"] ? &t.str["outputFile"] : nullptr, t.bln["allowRedundantSchemaRemoval"], t.bln["debug"]);
				}
				if (t.bln["whether -# was called"]) {
					cout << "[Main] Calling extractConclusions(ExtractionMethod::ProofSystemFromTopList, " << (unsigned) t.num["extractToSystemAmount"] << ", null, true, " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::extractConclusions(ExtractionMethod::ProofSystemFromTopList, (unsigned) t.num["extractToSystemAmount"], nullptr, true, t.bln["debug"]);
				}
				if (t.bln["whether -h was called"]) {
					cout << "[Main] Calling extractConclusions(" << (t.bln["useInputFile"] ? "ExtractionMethod::ProofSystemFromFile" : "ExtractionMethod::ProofSystemFromString") << ", 0, \"" << t.str["proofs"] << "\", true, " << bstr(t.bln["debug"]) << ")." << endl;
					DlProofEnumerator::extractConclusions(t.bln["useInputFile"] ? ExtractionMethod::ProofSystemFromFile : ExtractionMethod::ProofSystemFromString, 0, &t.str["proofs"], true, t.bln["debug"]);
				}
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
				cout << "[Main] Calling printConclusionLengthPlotData(" << bstr(t.bln["measureSymbolicLength"]) << ", " << bstr(t.bln["table"]) << ", " << t.num["cutX"] << ", " << t.num["cutY"] << ", \"" << t.str["dataLocation"] << "\", \"" << t.str["inputFilePrefix"] << "\", " << (t.str["mout"].empty() ? "null" : "\"" + t.str["mout"] + "\"") << ", " << bstr(t.bln["debug"]) << ")." << endl;
				if (t.str["mout"].empty())
					DlProofEnumerator::printConclusionLengthPlotData(t.bln["measureSymbolicLength"], t.bln["table"], t.num["cutX"], t.num["cutY"], t.str["dataLocation"], t.str["inputFilePrefix"], nullptr, t.bln["debug"]);
				else {
					string path = t.str["mout"];
					FctHelper::ensureDirExists(path);
					ofstream fout(path, fstream::out | fstream::binary);
					if (!fout.is_open())
						throw invalid_argument("Cannot write to file \"" + string(path) + "\".");
					DlProofEnumerator::printConclusionLengthPlotData(t.bln["measureSymbolicLength"], t.bln["table"], t.num["cutX"], t.num["cutY"], t.str["dataLocation"], t.str["inputFilePrefix"], &fout, t.bln["debug"]);
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
