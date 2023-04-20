#ifndef XAMID_HELPER_FCTHELPER_H
#define XAMID_HELPER_FCTHELPER_H

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace xamid {
namespace helper {

struct cmpStringGrow {
	// Shorter strings first ; Returns true iff |a| < |b| or (|a| = |b| and a < b).
	bool operator()(const std::string& a, const std::string& b) const;
};

struct cmpStringShrink {
	// Longer strings first ; Returns true iff |a| > |b| or (|a| = |b| and a < b).
	bool operator()(const std::string& a, const std::string& b) const;
};

template<typename T>
struct ManagedArray { // for RAII on dynamic arrays
	T* data;
	ManagedArray() : data(nullptr) { }
	ManagedArray(std::size_t size) : data(new T[size]) { }
	~ManagedArray() { delete data; }
};

struct FctHelper {
	static void mpi_sendString(int rank, const std::string& s, int dest, bool debug = false);
	static std::string mpi_recvString(int rank, int source, bool debug = false);
	static bool mpi_tryRecvString(int rank, int source, std::string& result, bool debug = false);

	template<typename T>
	static bool toUInt(const std::string& str, T& value) {
		if (*str.c_str() == '0' && str.length() != 1)
			return false;
		T num = 0;
		for (char c : str) {
			T before = num;
			switch (c) {
			case '0':
				num = 10 * num;
				break;
			case '1':
				num = 10 * num + 1;
				break;
			case '2':
				num = 10 * num + 2;
				break;
			case '3':
				num = 10 * num + 3;
				break;
			case '4':
				num = 10 * num + 4;
				break;
			case '5':
				num = 10 * num + 5;
				break;
			case '6':
				num = 10 * num + 6;
				break;
			case '7':
				num = 10 * num + 7;
				break;
			case '8':
				num = 10 * num + 8;
				break;
			case '9':
				num = 10 * num + 9;
				break;
			default:
				return false;
			}
			if (num < before) // overflow
				return false;
		}
		value = num;
		return true;
	}

	// Functions to quickly calculate to_string(n).length()
	static unsigned digitsNum_uint32(std::uint32_t n);
	static unsigned digitsNum_uint64(std::uint64_t n);

	// To round 'x' to precisely 'n' digits after the decimal separator
	static std::string round(long double x, unsigned n, char separator = '.');

	// Creates a formated string representing 'dur'. Uses C++ standard specific constants, except uses 31536000 s / yr and 2628000 s / mo in case of 'wolframAlphaMode'.
	// Milliseconds are rounded to 'round' digits after their decimal separator, thus 3 means no rounding since full microseconds are given.
	static std::string durationYearsToMs(const std::chrono::microseconds& dur, bool innerAlign = true, unsigned round = 2, bool showMonths = false, bool showWeeks = false, bool wolframAlphaMode = false, const std::string& yrId = " yr", const std::string& moId = " mo", const std::string& wkId = " wk", const std::string& dId = " d", const std::string& hId = " h", const std::string& minId = " min", const std::string& sId = " s", const std::string& msId = " ms");

	// Creates string "[amount of milliseconds]" + 'msId', and additionally appends " ([formatted duration from years to milliseconds])" if the duration is at least 1 second.
	static std::string durationStringMs(const std::chrono::microseconds& dur, bool innerAlign = false, unsigned round = 2, bool showMonths = false, bool showWeeks = false, bool wolframAlphaMode = false, const std::string& yrId = " yr", const std::string& moId = " mo", const std::string& wkId = " wk", const std::string& dId = " d", const std::string& hId = " h", const std::string& minId = " min", const std::string& sId = " s", const std::string& msId = " ms");

	// Ensures existing directories of a path, e.g. may create one folder "data" for path "data/file", but may create two folders "data" and "data/dir" for path "data/dir/".
	static bool ensureDirExists(const std::string& path);

	static bool writeToFile(const std::string& file, const std::string& content, std::fstream::openmode mode = std::fstream::out | std::fstream::binary);
	static bool readFile(const std::string& file, std::string& out_content, std::fstream::openmode mode = std::fstream::in | std::fstream::binary);

	static std::wstring utf8toWide(const std::string& in);
	static std::wstring utf8toWide(const char* in);
	static std::vector<std::string> stringSplit(const std::string& str, const std::string& sep);
	static std::string stringJoin(const std::vector<std::string>& elements);
	static std::string stringJoin(const std::string& separator, const std::vector<std::string>& elements);

	template<typename T, typename U>
	static std::string vectorString(const std::vector<T, U>& v, const std::string& leftDelimiter = "[", const std::string& rightDelimiter = "]", const std::string& sep = ", ") {
		std::stringstream ss;
		ss << leftDelimiter;
		for (std::size_t i = 0; i < v.size(); ++i) {
			if (i)
				ss << sep;
			ss << v[i];
		}
		ss << rightDelimiter;
		return ss.str();
	}

	template<typename T, typename U, typename Func>
	static std::string vectorStringF(const std::vector<T, U>& v, const Func& f, const std::string& leftDelimiter = "[", const std::string& rightDelimiter = "]", const std::string& sep = ", ") {
		std::stringstream ss;
		ss << leftDelimiter;
		for (std::size_t i = 0; i < v.size(); ++i) {
			if (i)
				ss << sep;
			ss << f(v[i]);
		}
		ss << rightDelimiter;
		return ss.str();
	}

	template<typename T, typename U, typename V, typename W>
	static std::string mapString(const std::map<T, U, V, W>& m, const std::string& leftDelimiter = "{", const std::string& rightDelimiter = "}", const std::string& sep = ", ") {
		std::stringstream ss;
		ss << leftDelimiter;
		for (typename std::map<T, U, V, W>::const_iterator it = m.begin(); it != m.end(); ++it) {
			if (it != m.begin())
				ss << sep;
			ss << "(" << it->first << "," << it->second << ")";
		}
		ss << rightDelimiter;
		return ss.str();
	}

	template<typename T, typename U, typename V, typename W, typename Func>
	static std::string mapStringF(const std::map<T, U, V, W>& m, const Func& f, const std::string& leftDelimiter = "{", const std::string& rightDelimiter = "}", const std::string& sep = ", ") {
		std::stringstream ss;
		ss << leftDelimiter;
		for (typename std::map<T, U, V, W>::const_iterator it = m.begin(); it != m.end(); ++it) {
			if (it != m.begin())
				ss << sep;
			ss << f(*it);
		}
		ss << rightDelimiter;
		return ss.str();
	}

	template<typename T, typename U>
	static bool vectorContains(const std::vector<T, U>& v, const T& obj) {
		return std::find(v.begin(), v.end(), obj) != v.end();
	}

	template<typename T, typename U>
	static bool vectorContainsReverse(const std::vector<T, U>& v, const T& obj) {
		return std::find(v.rbegin(), v.rend(), obj) != v.rend();
	}

	template<typename T, typename U, typename V>
	static std::string setString(const std::set<T, U, V>& v, const std::string& leftDelimiter = "{", const std::string& rightDelimiter = "}", const std::string& sep = ", ") {
		std::stringstream ss;
		ss << leftDelimiter;
		for (typename std::set<T, U, V>::const_iterator it = v.begin(); it != v.end(); ++it) {
			if (it != v.begin())
				ss << sep;
			ss << *it;
		}
		ss << rightDelimiter;
		return ss.str();
	}

	template<typename T, typename U>
	static std::string dequeString(const std::deque<T, U>& v, const std::string& leftDelimiter = "(", const std::string& rightDelimiter = ")", const std::string& sep = ", ") {
		std::stringstream ss;
		ss << leftDelimiter;
		for (typename std::deque<T, U>::const_iterator it = v.begin(); it != v.end(); ++it) {
			if (it != v.begin())
				ss << sep;
			ss << *it;
		}
		ss << rightDelimiter;
		return ss.str();
	}
};

}
}

#endif // XAMID_HELPER_FCTHELPER_H
