#include "FctHelper.h"

#include <iostream>
#include <math.h>
#include <mpi.h>

using namespace std;

namespace xamid {
namespace helper {

bool cmpStringShrink::operator()(const string& a, const string& b) const {
	if (a.length() < b.length())
		return false;
	else if (a.length() > b.length())
		return true;
	else
		return a < b;
}

bool cmpStringGrow::operator()(const string& a, const string& b) const {
	if (a.length() < b.length())
		return true;
	else if (a.length() > b.length())
		return false;
	else
		return a < b;
}

void FctHelper::mpi_sendString(int rank, const string& s, int dest, bool debug) {
	if (debug)
		cout << rank << "->" << dest << ": Sending " << s << ". (length " << s.length() << ")" << endl;
	// Actually send s.size() + 1 chars, since s.c_str() is null-terminated.
	MPI_Send(s.c_str(), static_cast<int>(s.size() + 1), MPI_CHAR, dest, 0, MPI_COMM_WORLD);
}

string FctHelper::mpi_recvString(int rank, int source, bool debug) {
	MPI_Status status_recv;
	MPI_Probe(source, 0, MPI_COMM_WORLD, &status_recv);
	int size;
	MPI_Get_count(&status_recv, MPI_CHAR, &size);
	if (debug)
		cout << source << "->" << rank << ": Will receive " << size << " chars." << endl;
	ManagedArray<char> arr(size);
	MPI_Recv(arr.data, size, MPI_CHAR, source, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	if (debug)
		cout << source << "->" << rank << ": Received: " << arr.data << ". (length " << string(arr.data).length() << ")" << endl;
	return arr.data;
}

bool FctHelper::mpi_tryRecvString(int rank, int source, string& result, bool debug) {
	int flag;
	MPI_Status status_recv;
	MPI_Iprobe(source, 0, MPI_COMM_WORLD, &flag, &status_recv);
	if (flag) {
		int size;
		MPI_Get_count(&status_recv, MPI_CHAR, &size);
		if (debug)
			cout << source << "->" << rank << ": Will receive " << size << " chars." << endl;
		ManagedArray<char> arr(size);
		MPI_Recv(arr.data, size, MPI_CHAR, source, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
		if (debug)
			cout << source << "->" << rank << ": Received: " << arr.data << ". (length " << string(arr.data).length() << ")" << endl;
		result = arr.data;
	}
	return flag;
}

unsigned FctHelper::digitsNum_uint32(uint32_t n) {
	static constexpr uint32_t MaxTable[9] = { 10u, 100u, 1000u, 10000u, 100000u, 1000000u, 10000000u, 100000000u, 1000000000u };  // to_string(numeric_limits<uint32_t>::max()) = "4294967295" has length 10
	return 1 + static_cast<unsigned>(upper_bound(MaxTable, MaxTable + 9, n) - MaxTable);
}

unsigned FctHelper::digitsNum_uint64(uint64_t n) {
	static constexpr uint64_t MaxTable[19] = { 10uLL, 100uLL, 1000uLL, 10000uLL, 100000uLL, 1000000uLL, 10000000uLL, 100000000uLL, 1000000000uLL, 10000000000uLL, 100000000000uLL, 1000000000000uLL, 10000000000000uLL, 100000000000000uLL, 1000000000000000uLL, 10000000000000000uLL, 100000000000000000uLL, 1000000000000000000uLL, 10000000000000000000uLL };  // to_string(numeric_limits<uint64_t>::max()) = "18446744073709551615" has length 20
	return 1 + static_cast<unsigned>(upper_bound(MaxTable, MaxTable + 19, n) - MaxTable);
}

string FctHelper::round(long double x, unsigned n, char separator) {
	if (n == 0) {
		stringstream ss;
		ss << fixed << std::round(x) << scientific;
		string result = ss.str();
		string::size_type i = result.find_first_not_of("0123456789-");
		if (i == string::npos)
			return result;
		else
			return result.substr(0, i);
	}
	auto toStringWithoutTrailingZeroes = [&](long double f) -> string {
		auto removeTrailingZeros = [&](const string& s) -> string { string::size_type i = s.find_first_not_of("0123456789-"); if (i == string::npos) return s; i = s.find_last_not_of('0'); return s.substr(0, i + 1); };
		stringstream ss;
		ss << fixed << f << scientific;
		return removeTrailingZeros(ss.str());
	};
	string result = toStringWithoutTrailingZeroes(x);
	string::size_type i = result.find_first_not_of("0123456789-");
	if (i == string::npos)
		return result + string { separator } + string(n, '0');
	if (result.size() <= n + i + 1) {
		if (result[i] != separator)
			result[i] = separator;
		string::size_type missingTrailingZeroes = n + 1 - (result.size() - i);
		return result + string(missingTrailingZeroes, '0');
	}
	int d = 0;
	if (floor(x * std::pow(10, n + 1) - 10 * floor(x * std::pow(10, n))) > 4)
		d = 1;
	x = (floor(x * std::pow(10, n)) + d) / std::pow(10, n);
	result = toStringWithoutTrailingZeroes(x);
	i = result.find_first_not_of("0123456789-");
	if (i == string::npos)
		return result + string { separator } + string(n, '0');
	if (result[i] != separator)
		result[i] = separator;
	if (result.size() <= n + i + 1) {
		string::size_type missingTrailingZeroes = n + 1 - (result.size() - i);
		return result + string(missingTrailingZeroes, '0');
	}
	// the operation did not eliminate all superfluous digits (because IEEE 754 floating-point arithmetic sucks) => just cut
	return result.substr(0, n + i + 1);
}

string FctHelper::durationYearsToMs(const chrono::microseconds& dur, bool innerAlign, unsigned round, bool showMonths, bool showWeeks, bool wolframAlphaMode, const string& yrId, const string& moId, const string& wkId, const string& dId, const string& hId, const string& minId, const string& sId, const string& msId) {
	int64_t durationUs = dur.count();
	bool negative = durationUs < 0;

	// NOTE: Bounds are as follows.
	//       !wolframAlphaMode =>  -2^63  µs = -292277 yr  0 mo -1 wk -1 d -23 h -52 min -30 s -775.808 ms
	//                             2^63+1 µs =  292277 yr  0 mo  1 wk  1 d  23 h  52 min  30 s  775.807 ms
	//        wolframAlphaMode =>  -2^63  µs = -292471 yr -2 mo -2 wk -1 d  -8 h   0 min -54 s -775.808 ms
	//                             2^63+1 µs =  292471 yr  2 mo  2 wk  1 d   8 h   0 min  54 s  775.807 ms
	constexpr intmax_t yearUs = chrono::years::period::num * chrono::microseconds::period::den; //     1 yr  = 31556952000000 µs ; NOTE: 31556952 s / yr include leap years, otherwise it would be 60 * 60 * 24 * 365 = 31540000 s / yr.
	constexpr intmax_t monthUs = chrono::months::period::num * chrono::microseconds::period::den; //   1 mo  =  2629746000000 µs ;       2629746 s / mo include leap years, otherwise it would be 31540000 / 12 = 7885000 / 3 = 2628333.333.. s / mo.
	constexpr intmax_t weekUs = chrono::weeks::period::num * chrono::microseconds::period::den; //     1 wk  =   604800000000 µs ;       60 * 60 * 24 * 7 = 604800 s / wk, i.e. from here down, the C++ standard's leap years do not influence values.
	constexpr intmax_t dayUs = chrono::days::period::num * chrono::microseconds::period::den; //       1 d   =    86400000000 µs
	constexpr intmax_t hourUs = chrono::hours::period::num * chrono::microseconds::period::den; //     1 h   =     3600000000 µs
	constexpr intmax_t minuteUs = chrono::minutes::period::num * chrono::microseconds::period::den; // 1 min =       60000000 µs
	constexpr intmax_t secondUs = chrono::seconds::period::num * chrono::microseconds::period::den; // 1 s   =        1000000 µs
	intmax_t yearUs_used = wolframAlphaMode ? 31536000000000LL : yearUs; //  NOTE: Technically 60 * 60 * 24 * 365 = 31540000 s / yr without leap years, but WolframAlpha uses 31536000 s / yr : https://www.wolframalpha.com/input?i=31536000+s+-+1+year.
	intmax_t monthUs_used = wolframAlphaMode ? 2628000000000LL : monthUs; // NOTE: Technically 31540000 / 12 = 2628333.333.. s / mo without leap years, but WolframAlpha uses  2628000 s / mo : https://www.wolframalpha.com/input?i=2628000+s+-+1+month.

	int64_t years = durationUs / yearUs_used;
	durationUs -= years * yearUs_used;
	int64_t months = 0;
	if (showMonths) {
		months = durationUs / monthUs_used;
		durationUs -= months * monthUs_used;
	}
	int64_t weeks = 0;
	if (showWeeks) {
		weeks = durationUs / weekUs;
		durationUs -= weeks * weekUs;
	}
	int64_t days = durationUs / dayUs;
	durationUs -= days * dayUs;
	int64_t hours = durationUs / hourUs;
	durationUs -= hours * hourUs;
	int64_t minutes = durationUs / minuteUs;
	durationUs -= minutes * minuteUs;
	int64_t seconds = durationUs / secondUs;
	durationUs -= seconds * secondUs;
	double milliseconds = static_cast<double>(durationUs) / 1000.0;

	stringstream ss;
	bool empty = true;
	auto spaceIfNonEmpty = [&]() {
		return empty ? "" : " ";
	};
	auto requestedIndent = [&](unsigned indent, const string& num) -> string {
		if (innerAlign && !empty) {
			if (negative)
				indent++;
			string::size_type len = num.length();
			if (indent <= len)
				return "";
			return string(indent - len, ' ');
		} else
			return "";
	};
	auto appendRequestedBlankIndent = [&](string::size_type indent) {
		if (innerAlign && !empty) {
			if (negative)
				indent++;
			ss << spaceIfNonEmpty() << string(indent, ' ');
		}
	};
	if (years) {
		ss << years << yrId;
		empty = false;
	}
	if (months) {
		string mo = to_string(months);
		ss << spaceIfNonEmpty() << requestedIndent(2, mo) << mo << moId;
		if (empty)
			empty = false;
	} else
		appendRequestedBlankIndent(2 + moId.length());
	if (weeks) {
		string wk = to_string(weeks);
		ss << spaceIfNonEmpty() << requestedIndent(2, wk) << wk << wkId;
		if (empty)
			empty = false;
	} else
		appendRequestedBlankIndent(2 + wkId.length());
	if (days) {
		string d = to_string(days);
		ss << spaceIfNonEmpty() << requestedIndent(showWeeks ? 1 : showMonths ? 2 : 3, d) << d << dId;
		if (empty)
			empty = false;
	} else
		appendRequestedBlankIndent((showWeeks ? 1 : showMonths ? 2 : 3) + dId.length());
	if (hours) {
		string h = to_string(hours);
		ss << spaceIfNonEmpty() << requestedIndent(2, h) << h << hId;
		if (empty)
			empty = false;
	} else
		appendRequestedBlankIndent(2 + hId.length());
	if (minutes) {
		string min = to_string(minutes);
		ss << spaceIfNonEmpty() << requestedIndent(2, min) << min << minId;
		if (empty)
			empty = false;
	} else
		appendRequestedBlankIndent(2 + minId.length());
	if (seconds) {
		string s = to_string(seconds);
		ss << spaceIfNonEmpty() << requestedIndent(2, s) << s << sId;
		if (empty)
			empty = false;
	} else
		appendRequestedBlankIndent(2 + sId.length());
	if (milliseconds || empty) {
		string ms = FctHelper::round(milliseconds, round);
		ss << spaceIfNonEmpty() << requestedIndent(round ? 4 + round : 3, ms) << ms << msId;
	} else
		appendRequestedBlankIndent((round ? 4 + round : 3) + msId.length());
	return ss.str();
}

string FctHelper::durationStringMs(const chrono::microseconds& dur, bool innerAlign, unsigned round, bool showMonths, bool showWeeks, bool wolframAlphaMode, const string& yrId, const string& moId, const string& wkId, const string& dId, const string& hId, const string& minId, const string& sId, const string& msId) {
	stringstream ss;
	if (dur.count() >= 1000000)
		ss << FctHelper::round(static_cast<long double>(dur.count()) / 1000.0, 2) << msId << " (" << durationYearsToMs(dur, innerAlign, round, showMonths, showWeeks, wolframAlphaMode, yrId, moId, wkId, dId, hId, minId, sId, msId) << ")";
	else
		ss << FctHelper::round(static_cast<long double>(dur.count()) / 1000.0, 2) << msId;
	return ss.str();
}

bool FctHelper::ensureDirExists(const string& path) {
	string::size_type dirMarkerIndex = path.find_last_of("/\\");
	if (dirMarkerIndex != string::npos) { // If there is a path to another directory given, make sure that the directory exists.
		string dir = path.substr(0, dirMarkerIndex);
		if (!filesystem::is_directory(dir)) { // Need to create that directory, but in order to do so, must first ensure that its parent directory exists.
			if (!ensureDirExists(dir))
				return false;
			if (!filesystem::create_directories(dir)) {
				cerr << "Failed to create directory \"" << dir << "\"." << endl;
				return false;
			}
		}
	}
	return true;
}

bool FctHelper::writeToFile(const string& file, const string& content, fstream::openmode mode) {
	return _writeToFile(filesystem::u8path(file), content, mode);
}

bool FctHelper::_writeToFile(const filesystem::path& file, const string& content, fstream::openmode mode) {
	// 1. Ensure directory exists
	if (!filesystem::exists(file) && !ensureDirExists(file.string()))
		return false;
	// 2. Save file
	ofstream fout(file, mode);
	if (!fout.is_open()) {
		cerr << "Cannot write to file \"" << file.string() << "\"." << endl;
		return false;
	}
	fout << content;
	return true;
}

bool FctHelper::readFile(const string& file, string& out_content, fstream::openmode mode) {
	return _readFile(filesystem::u8path(file), out_content, mode);
}

bool FctHelper::_readFile(const filesystem::path& file, string& out_content, fstream::openmode mode) {
	ifstream fin(file, mode);
	if (!fin.is_open()) {
		cerr << "Cannot read from file \"" << file.string() << "\"." << endl;
		return false;
	}
	stringstream buffer;
	buffer << fin.rdbuf();
	out_content = buffer.str();
	return true;
}

wstring FctHelper::utf8toWide(const string& in) {
	return utf8toWide(in.c_str());
}

wstring FctHelper::utf8toWide(const char* in) {
	wstring out;
	if (!in)
		return out;
	uint32_t codepoint = 0;
	while (*in) {
		unsigned char ch = static_cast<unsigned char>(*in);
		if (ch <= 0x7f)
			codepoint = ch;
		else if (ch <= 0xbf)
			codepoint = (codepoint << 6) | (ch & 0x3f);
		else if (ch <= 0xdf)
			codepoint = ch & 0x1f;
		else if (ch <= 0xef)
			codepoint = ch & 0x0f;
		else
			codepoint = ch & 0x07;
		++in;
		if (((*in & 0xc0) != 0x80) && (codepoint <= 0x10ffff)) {
			if (codepoint > 0xffff) {
				out.append(1, static_cast<wchar_t>(0xd800 + (codepoint >> 10)));
				out.append(1, static_cast<wchar_t>(0xdc00 + (codepoint & 0x03ff)));
			} else if (codepoint < 0xd800 || codepoint >= 0xe000)
				out.append(1, static_cast<wchar_t>(codepoint));
		}
	}
	return out;
}

vector<string> FctHelper::stringSplit(const string& str, const string& sep) {
	vector<string> parts;
	string::size_type start = 0;
	string::size_type end = str.find(sep);
	while (end != string::npos) {
		parts.push_back(str.substr(start, end - start));
		start = end + sep.length();
		end = str.find(sep, start);
	}
	parts.push_back(str.substr(start, end));
	return parts;
}

string FctHelper::stringJoin(const vector<string>& elements) {
	if (!elements.empty()) {
		stringstream ss;
		vector<string>::const_iterator it = elements.begin();
		while (it != elements.end())
			ss << *it++;
		return ss.str();
	}
	return {};
}

string FctHelper::stringJoin(const string& separator, const vector<string>& elements) {
	if (!elements.empty()) {
		stringstream ss;
		vector<string>::const_iterator it = elements.begin();
		while (it != elements.end()) {
			ss << *it++;
			if (it != elements.end())
				ss << separator;
		}
		return ss.str();
	}
	return {};
}

}
}
