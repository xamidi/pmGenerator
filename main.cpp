#include "helper/FctHelper.h"
#include "metamath/DRuleReducer.h"
#include "nortmann/DlProofEnumerator.h"

#include <ctime>
#include <iostream>

using namespace std;
using namespace xamid::helper;
using namespace xamid::metamath;
using namespace xamid::nortmann;

struct A {
	A() {
		time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
		cout << strtok(ctime(&time), "\n") << ": Process started." << endl;
	}
	~A() {
		time_t time = chrono::system_clock::to_time_t(chrono::system_clock::now());
		cout << strtok(ctime(&time), "\n") << ": Process terminated." << endl;
	}
} a;

int main(int argc, char* argv[]) { // argc = 1 + N, argv = { <command>, <arg0>, ..., <argN> }
	//#cout << "argc = " << argc << ", argv = { " << [&]() { string s; for (int i = 0; i < argc; i++) { if (i) s += ", "; s += string { argv[i] }; } return s; }() << " }" << endl;
	auto printUsage = [](string error = "") {
		if (!error.empty())
			cerr << error << endl;
		cout << "Usage:\n"
				"    pmGenerator ( -g <limit> [-u] | -r <pmproofs file> <output file> [-m] [-d] | -a <initials> <replacements file> <pmproofs file> <output file> [-s] [-l] [-w] [-d] )+\n"
				"    -g: Generate proof files\n"
				"        -u: unfiltered (faster, but generates redundant proofs)\n"
				"    -r: Replacements file creation based on proof files\n"
				"        -m: disable memory reduction (distributed formula lookup data, requires more RAM)\n"
				"        -d: print debug information\n"
				"    -a: Apply replacements file\n"
				"        -s: style all proofs (replace proofs with alphanumerically smaller variants)\n"
				"        -l: list all proofs (i.e. not only modified proofs)\n"
				"        -w: wrap results\n"
				"        -d: print debug information\n"
				"Examples:\n"
				"    pmGenerator -g 19\n"
				"    pmGenerator -r \"data/pmproofs.txt\" \"data/pmproofs-reducer.txt\" -d\n"
				"    pmGenerator -a SD data/pmproofs-reducer.txt data/pmproofs.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w -d\n"
				"    pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -d -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w -d" << endl;
		return 0;
	};
#if 0 // default command
	if (argc <= 1) {
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-all.txt -l -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-all.txt -s -l -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-modifiedOnly.txt -w", " ");
		static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly-noWrap.txt -s", " ");
		argc = customCmd.size();
		argv = new char*[customCmd.size()];
		for (size_t i = 0; i < customCmd.size(); i++)
			argv[i] = const_cast<char*>(customCmd[i].c_str());
	}
#endif
	if (argc <= 1)
		return printUsage();
	enum class Task {
		Generate, // get<6> = filtered
		CreateReplacements, // get<6> = debug, get<7> = memReduction
		ApplyReplacements // get<6> = debug, get<7> = styleAll, get<8> = listAll, get<9> = wrap
	};
	vector<tuple<Task, unsigned, string, string, string, string, bool, bool, bool, bool>> tasks;

	for (int i = 1; i < argc; i++) {
		if (argv[i][0] != '-' || argv[i][1] == '\0' || argv[i][2] != '\0')
			return printUsage("Invalid argument \"" + string { argv[i] } + "\".");
		switch (argv[i][1]) {
		case 'g':
			if (i + 1 >= argc)
				return printUsage("Missing argument for \"-g\".");
			tasks.emplace_back(Task::Generate, stoi(argv[++i]), "", "", "", "", true, false, false, false);
			break;
		case 'u':
			if (tasks.empty() || get<0>(tasks.back()) != Task::Generate)
				return printUsage("Invalid argument \"-u\".");
			get<6>(tasks.back()) = false; // filtered := false
			break;
		case 'm':
			if (tasks.empty() || get<0>(tasks.back()) != Task::CreateReplacements)
				return printUsage("Invalid argument \"-m\".");
			get<7>(tasks.back()) = false; // memReduction := false
			break;
		case 'r':
			if (i + 2 >= argc)
				return printUsage("Missing argument for \"-r\".");
			tasks.emplace_back(Task::CreateReplacements, 0, argv[i + 1], argv[i + 2], "", "", false, true, false, false);
			i += 2;
			break;
		case 'd':
			if (tasks.empty() || (get<0>(tasks.back()) != Task::CreateReplacements && get<0>(tasks.back()) != Task::ApplyReplacements))
				return printUsage("Invalid argument \"-d\".");
			get<6>(tasks.back()) = true; // debug := true
			break;
		case 'a':
			if (i + 4 >= argc)
				return printUsage("Missing argument for \"-a\".");
			tasks.emplace_back(Task::ApplyReplacements, 0, argv[i + 1], argv[i + 2], argv[i + 3], argv[i + 4], false, false, false, false);
			i += 4;
			break;
		case 's':
			if (tasks.empty() || get<0>(tasks.back()) != Task::ApplyReplacements)
				return printUsage("Invalid argument \"-s\".");
			get<7>(tasks.back()) = true; // styleAll := true
			break;
		case 'l':
			if (tasks.empty() || get<0>(tasks.back()) != Task::ApplyReplacements)
				return printUsage("Invalid argument \"-l\".");
			get<8>(tasks.back()) = true; // listAll := true
			break;
		case 'w':
			if (tasks.empty() || get<0>(tasks.back()) != Task::ApplyReplacements)
				return printUsage("Invalid argument \"-w\".");
			get<9>(tasks.back()) = true; // wrap := true
			break;
		default:
			return printUsage();
		}
	}
	auto bstr = [](bool b) { return b ? "true" : "false"; };
	stringstream ss;
	size_t index = 0;
	for (const tuple<Task, unsigned, string, string, string, string, bool, bool, bool, bool>& t : tasks)
		switch (get<0>(t)) {
		case Task::Generate:
			ss << ++index << ". generateDProofRepresentativeFiles(" << get<1>(t) << ", " << bstr(get<6>(t)) << ")\n";
			break;
		case Task::CreateReplacements:
			ss << ++index << ". createReplacementsFile(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<6>(t)) << ")\n";
			break;
		case Task::ApplyReplacements:
			ss << ++index << ". applyReplacements(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", \"" << get<4>(t) << "\", \"" << get<5>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<8>(t)) << ", " << bstr(get<9>(t)) << ", " << bstr(get<6>(t)) << ")\n";
			break;
		}
	cout << "Tasks:\n" << ss.str() << endl;
	try {
		for (const tuple<Task, unsigned, string, string, string, string, bool, bool, bool, bool>& t : tasks)
			switch (get<0>(t)) {
			case Task::Generate:
				cout << "[Main] Calling generateDProofRepresentativeFiles(" << get<1>(t) << ", " << bstr(get<6>(t)) << ")." << endl;
				DlProofEnumerator::generateDProofRepresentativeFiles(get<1>(t), get<6>(t));
				break;
			case Task::CreateReplacements:
				cout << "[Main] Calling createReplacementsFile(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<6>(t)) << ")." << endl;
				DRuleReducer::createReplacementsFile(get<2>(t), get<3>(t), get<7>(t), get<6>(t));
				break;
			case Task::ApplyReplacements:
				cout << "[Main] Calling applyReplacements(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", \"" << get<4>(t) << "\", \"" << get<5>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<8>(t)) << ", " << bstr(get<9>(t)) << ", " << bstr(get<6>(t)) << ")." << endl;
				DRuleReducer::applyReplacements(get<2>(t), get<3>(t), get<4>(t), get<5>(t), get<7>(t), get<8>(t), get<9>(t), get<6>(t));
				break;
			}
	} catch (exception& e) {
		cerr << "ERROR exception thrown: " << e.what() << endl;
	}
	return 0;
}
