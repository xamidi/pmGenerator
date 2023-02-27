#include "helper/FctHelper.h"
#include "metamath/DRuleReducer.h"
#include "nortmann/DlProofEnumerator.h"

#include <cstring>
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

int main(int argc, char* argv[]) { // argc = 1 + N, argv = { <command>, <arg1>, ..., <argN> }
	//#cout << "argc = " << argc << ", argv = { " << [&]() { string s; for (int i = 0; i < argc; i++) { if (i) s += ", "; s += string { argv[i] }; } return s; }() << " }" << endl;
	auto printUsage = [](const string& error = "") {
		if (!error.empty())
			cerr << error << endl;
		cout << "Usage:\n"
				"    pmGenerator ( -g <limit> [-u] [-c] | -r <pmproofs file> <output file> [-i <prefix>] [-c] [-d] | -a <initials> <replacements file> <pmproofs file> <output file> [-s] [-l] [-w] [-d] | -f ( 0 | 1 ) [-i <prefix>] [-o <prefix>] [-d] | -p [-i <prefix>] [-s] [-t] [-x <limit>] [-y <limit>] [-o <output file>] [-d] )+\n"
				"    -g: Generate proof files\n"
				"        -u: unfiltered (significantly faster, but generates redundant proofs)\n"
				"        -c: proof files without conclusions, requires additional parsing\n"
				"    -r: Replacements file creation based on proof files\n"
				"        -i: customize input file path prefix ; default: \"data/dProofs-withConclusions/dProofs\"\n"
				"        -c: proof files without conclusions, requires additional parsing ; sets default input file path prefix to \"data/dProofs-withoutConclusions/dProofs\"\n"
				"        -d: print debug information\n"
				"    -a: Apply replacements file\n"
				"        -s: style all proofs (replace proofs with alphanumerically smaller variants)\n"
				"        -l: list all proofs (i.e. not only modified proofs)\n"
				"        -w: wrap results\n"
				"        -d: print debug information\n"
				"    -f: Create proof files with removed (-f 0) or added (-f 1) conclusions from proof files of the other variant\n"
				"        -i: customize input file path prefix ; default: \"data/dProofs-withConclusions/dProofs\" or \"data/dProofs-withoutConclusions/dProofs\"\n"
				"        -o: customize output file path prefix ; default: \"data/dProofs-withoutConclusions/dProofs\" or \"data/dProofs-withConclusions/dProofs\"\n"
				"        -d: print debug information\n"
				"    -p: Print conclusion length plot data\n"
				"        -i: customize input file path prefix ; requires files with conclusions ; default: \"data/dProofs-withConclusions/dProofs\"\n"
				"        -s: measure symbolic length (in contrast to conclusion representation length)\n"
				"        -t: table arrangement, one data point per row\n"
				"        -x: upper horizontal limit\n"
				"        -y: upper vertical limit\n"
				"        -o: print to given output file\n"
				"        -d: print debug information\n"
				"Examples:\n"
				"    pmGenerator -g -1\n"
				"    pmGenerator -r \"data/pmproofs.txt\" \"data/pmproofs-reducer.txt\" -i \"data/dProofs\" -c -d\n"
				"    pmGenerator -a SD data/pmproofs-reducer.txt data/pmproofs.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w -d\n"
				"    pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -d -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w -d\n"
				"    pmGenerator -f 0 -o data/dProofs-withoutConclusions_ALL/dProofs -d\n"
				"    pmGenerator -p -s -d -p -s -t -x 50 -y 100 -o data/plot_data_x50_y100.txt" << endl;
		return 0;
	};
#if 0 // default command
	if (argc <= 1) {
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-all.txt -l -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-all.txt -s -l -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-modifiedOnly.txt -w", " ");
		//#static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -p -s -d -p -s -t -x 50 -y 100 -o data/plot_data_x50_y100.txt", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -r data/pmproofs-unified.txt data/pmproofs-reducer33.txt -d", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -a SD data/pmproofs-reducer33.txt data/pmproofs-unified.txt data/pmproofs-unified33-modifiedOnly-noWrap.txt -s", " ");
		//static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -a SD data/pmproofs-reducer33.txt data/pmproofs-unified.txt data/pmproofs-unified33.txt -s -l -w -d", " ");
		static vector<string> customCmd = FctHelper::stringSplit("pmGenerator -g 35 -u", " ");
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
		Generate, // get<6> = redundantSchemaRemoval, get<7> = withConclusions, get<8> : whether -i was called
		CreateReplacements, // get<4> = inputFilePrefix, get<6> = debug, get<7> = withConclusions
		ApplyReplacements, // get<6> = debug, get<7> = styleAll, get<8> = listAll, get<9> = wrap
		FileConversion, // get<2> = inputFilePrefix, get<3> = outputFilePrefix, get<6> = debug, get<7> ? createGeneratorFilesWithConclusions(...) : createGeneratorFilesWithoutConclusions(...)
		ConclusionLengthPlot // get<2> = inputFilePrefix, get<3> = mout, get<6> = debug, get<7> = measureSymbolicLength, get<8> = table, get<10> = cutX, get<11> = cutY
	};
	vector<tuple<Task, unsigned, string, string, string, string, bool, bool, bool, bool, int64_t, int64_t>> tasks;

	for (int i = 1; i < argc; i++) {
		if (argv[i][0] != '-' || argv[i][1] == '\0' || argv[i][2] != '\0')
			return printUsage("Invalid argument \"" + string { argv[i] } + "\".");
		switch (argv[i][1]) {
		case 'g':
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-g\".");
			try {
				tasks.emplace_back(Task::Generate, stoi(argv[++i]), "", "", "", "", true, true, false, false, 0, 0);
			} catch (exception& e) {
				return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-g\".");
			}
			break;
		case 'u':
			if (tasks.empty() || get<0>(tasks.back()) != Task::Generate)
				return printUsage("Invalid argument \"-u\".");
			get<6>(tasks.back()) = false; // redundantSchemaRemoval := false
			break;
		case 'c':
			if (tasks.empty() || (get<0>(tasks.back()) != Task::Generate && get<0>(tasks.back()) != Task::CreateReplacements))
				return printUsage("Invalid argument \"-c\".");
			get<7>(tasks.back()) = false; // withConclusions := false
			if (get<0>(tasks.back()) == Task::CreateReplacements && !get<8>(tasks.back()))
				get<4>(tasks.back()) = "data/dProofs-withoutConclusions/dProofs"; // get<4> = inputFilePrefix
			break;
		case 'i':
			if (tasks.empty() || (get<0>(tasks.back()) != Task::FileConversion && get<0>(tasks.back()) != Task::CreateReplacements && get<0>(tasks.back()) != Task::ConclusionLengthPlot))
				return printUsage("Invalid argument \"-i\".");
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-i\".");
			if (get<0>(tasks.back()) == Task::CreateReplacements) {
				get<4>(tasks.back()) = argv[++i]; // get<4> = inputFilePrefix
				get<8>(tasks.back()) = true; // get<8> : whether -i was called
			} else
				get<2>(tasks.back()) = argv[++i]; // get<2> = inputFilePrefix
			break;
		case 'r':
			if (i + 2 >= argc)
				return printUsage("Missing parameter for \"-r\".");
			tasks.emplace_back(Task::CreateReplacements, 0, argv[i + 1], argv[i + 2], "data/dProofs-withConclusions/dProofs", "", false, true, false, false, 0, 0);
			i += 2;
			break;
		case 'd':
			if (tasks.empty() || (get<0>(tasks.back()) != Task::CreateReplacements && get<0>(tasks.back()) != Task::ApplyReplacements && get<0>(tasks.back()) != Task::FileConversion && get<0>(tasks.back()) != Task::ConclusionLengthPlot))
				return printUsage("Invalid argument \"-d\".");
			get<6>(tasks.back()) = true; // debug := true
			break;
		case 'a':
			if (i + 4 >= argc)
				return printUsage("Missing parameter for \"-a\".");
			tasks.emplace_back(Task::ApplyReplacements, 0, argv[i + 1], argv[i + 2], argv[i + 3], argv[i + 4], false, false, false, false, 0, 0);
			i += 4;
			break;
		case 's':
			if (tasks.empty() || (get<0>(tasks.back()) != Task::ApplyReplacements && get<0>(tasks.back()) != Task::ConclusionLengthPlot))
				return printUsage("Invalid argument \"-s\".");
			get<7>(tasks.back()) = true; // styleAll := true, or measureSymbolicLength := true
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
		case 'f':
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-f\".");
			else {
				string param = string(argv[++i]);
				if (param != "0" && param != "1")
					return printUsage("Invalid parameter \"" + param + "\" for \"-f\".");
				bool with = param == "1";
				tasks.emplace_back(Task::FileConversion, 0, with ? "data/dProofs-withoutConclusions/dProofs" : "data/dProofs-withConclusions/dProofs", with ? "data/dProofs-withConclusions/dProofs" : "data/dProofs-withoutConclusions/dProofs", "", "", false, with, false, false, 0, 0);
			}
			break;
		case 'o':
			if (tasks.empty() || (get<0>(tasks.back()) != Task::FileConversion && get<0>(tasks.back()) != Task::ConclusionLengthPlot))
				return printUsage("Invalid argument \"-o\".");
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-o\".");
			get<3>(tasks.back()) = argv[++i]; // get<3> = outputFilePrefix, or get<3> = mout
			break;
		case 'p':
			tasks.emplace_back(Task::ConclusionLengthPlot, 0, "data/dProofs-withConclusions/dProofs", "", "", "", false, false, false, false, -1, -1);
			break;
		case 't':
			if (tasks.empty() || get<0>(tasks.back()) != Task::ConclusionLengthPlot)
				return printUsage("Invalid argument \"-t\".");
			get<8>(tasks.back()) = true; // table := true
			break;
		case 'x':
			if (tasks.empty() || get<0>(tasks.back()) != Task::ConclusionLengthPlot)
				return printUsage("Invalid argument \"-x\".");
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-x\".");
			try {
				get<10>(tasks.back()) = stoll(argv[++i]); // get<10> = cutX
			} catch (exception& e) {
				return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-x\".");
			}
			break;
		case 'y':
			if (tasks.empty() || get<0>(tasks.back()) != Task::ConclusionLengthPlot)
				return printUsage("Invalid argument \"-y\".");
			if (i + 1 >= argc)
				return printUsage("Missing parameter for \"-y\".");
			try {
				get<11>(tasks.back()) = stoll(argv[++i]); // get<11> = cutY
			} catch (exception& e) {
				return printUsage("Invalid parameter \"" + string(argv[i]) + "\" for \"-y\".");
			}
			break;
		default:
			return printUsage("Invalid argument \"" + string { argv[i] } + "\".");
		}
	}
	auto bstr = [](bool b) { return b ? "true" : "false"; };
	stringstream ss;
	size_t index = 0;
	for (const tuple<Task, unsigned, string, string, string, string, bool, bool, bool, bool, int64_t, int64_t>& t : tasks)
		switch (get<0>(t)) {
		case Task::Generate:
			ss << ++index << ". generateDProofRepresentativeFiles(" << get<1>(t) << ", " << bstr(get<6>(t)) << ", " << bstr(get<7>(t)) << ")\n";
			break;
		case Task::CreateReplacements:
			ss << ++index << ". createReplacementsFile(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", \"" << get<4>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<6>(t)) << ")\n";
			break;
		case Task::ApplyReplacements:
			ss << ++index << ". applyReplacements(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", \"" << get<4>(t) << "\", \"" << get<5>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<8>(t)) << ", " << bstr(get<9>(t)) << ", " << bstr(get<6>(t)) << ")\n";
			break;
		case Task::FileConversion:
			if (get<7>(t))
				ss << ++index << ". createGeneratorFilesWithConclusions(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", " << bstr(get<6>(t)) << ")\n";
			else
				ss << ++index << ". createGeneratorFilesWithoutConclusions(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", " << bstr(get<6>(t)) << ")\n";
			break;
		case Task::ConclusionLengthPlot:
			ss << ++index << ". printConclusionLengthPlotData(" << bstr(get<7>(t)) << ", " << bstr(get<8>(t)) << ", " << get<10>(t) << ", " << get<11>(t) << ", \"" << get<2>(t) << "\", " << (get<3>(t).empty() ? "null" : "\"" + get<3>(t) + "\"") << ", " << bstr(get<6>(t)) << ")\n";
			break;
		}
	cout << "Tasks:\n" << ss.str() << endl;
	try {
		for (const tuple<Task, unsigned, string, string, string, string, bool, bool, bool, bool, int64_t, int64_t>& t : tasks)
			switch (get<0>(t)) {
			case Task::Generate:
				cout << "[Main] Calling generateDProofRepresentativeFiles(" << get<1>(t) << ", " << bstr(get<6>(t)) << ", " << bstr(get<7>(t)) << ")." << endl;
				DlProofEnumerator::generateDProofRepresentativeFiles(get<1>(t), get<6>(t), get<7>(t));
				break;
			case Task::CreateReplacements:
				cout << "[Main] Calling createReplacementsFile(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", \"" << get<4>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<6>(t)) << ")." << endl;
				DRuleReducer::createReplacementsFile(get<2>(t), get<3>(t), get<4>(t), get<7>(t), get<6>(t));
				break;
			case Task::ApplyReplacements:
				cout << "[Main] Calling applyReplacements(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", \"" << get<4>(t) << "\", \"" << get<5>(t) << "\", " << bstr(get<7>(t)) << ", " << bstr(get<8>(t)) << ", " << bstr(get<9>(t)) << ", " << bstr(get<6>(t)) << ")." << endl;
				DRuleReducer::applyReplacements(get<2>(t), get<3>(t), get<4>(t), get<5>(t), get<7>(t), get<8>(t), get<9>(t), get<6>(t));
				break;
			case Task::FileConversion:
				if (get<7>(t)) {
					cout << "[Main] Calling  createGeneratorFilesWithConclusions(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", " << bstr(get<6>(t)) << ")." << endl;
					DlProofEnumerator::createGeneratorFilesWithConclusions(get<2>(t), get<3>(t), get<6>(t));
				} else {
					cout << "[Main] Calling  createGeneratorFilesWithoutConclusions(\"" << get<2>(t) << "\", \"" << get<3>(t) << "\", " << bstr(get<6>(t)) << ")." << endl;
					DlProofEnumerator::createGeneratorFilesWithoutConclusions(get<2>(t), get<3>(t), get<6>(t));
				}
				break;
			case Task::ConclusionLengthPlot:
				cout << "[Main] Calling printConclusionLengthPlotData(" << bstr(get<7>(t)) << ", " << bstr(get<8>(t)) << ", " << get<10>(t) << ", " << get<11>(t) << ", \"" << get<2>(t) << "\", " << (get<3>(t).empty() ? "null" : "\"" + get<3>(t) + "\"") << ", " << bstr(get<6>(t)) << ")." << endl;
				if (get<3>(t).empty())
					DlProofEnumerator::printConclusionLengthPlotData(get<7>(t), get<8>(t), get<10>(t), get<11>(t), get<2>(t), nullptr, get<6>(t));
				else {
					string path = get<3>(t);
					FctHelper::ensureDirExists(path);
					ofstream fout(filesystem::u8path(path), fstream::out | fstream::binary);
					if (!fout.is_open())
						throw invalid_argument("Cannot write to file \"" + string(path) + "\".");
					DlProofEnumerator::printConclusionLengthPlotData(get<7>(t), get<8>(t), get<10>(t), get<11>(t), get<2>(t), &fout, get<6>(t));
				}
				break;
			}
	} catch (exception& e) {
		cerr << "ERROR exception thrown: " << e.what() << endl;
	}
	return 0;
}
