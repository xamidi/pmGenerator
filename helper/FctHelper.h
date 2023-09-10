#ifndef XAMIDI_HELPER_FCTHELPER_H
#define XAMIDI_HELPER_FCTHELPER_H

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <fstream>
#include <map>
#include <mpi.h>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace xamidi {
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
	ManagedArray(ManagedArray<T>&& old) : data(old.data) { old.data = nullptr; } // move ; prohibit copying ; data shall be managed by a single object
	~ManagedArray() { delete[] data; }
	void alloc(std::size_t size) { delete[] data; data = new T[size]; }
};

struct FctHelper {
	static std::string mpi_nodeName();
	enum mpi_tag : int {
		mpi_tag_unspecified = 0, // not used by any helper function
		mpi_tag_bool = 1,
		mpi_tag_int = 2,
		mpi_tag_uint64 = 3,
		mpi_tag_string = 4,
		mpi_tag_pair_uint64 = 5,
		mpi_tag_custom = 6 // highest value ; to be added upon for custom tags
	};

	static void mpi_sendBool(int rank, const bool num, int dest, int tag = mpi_tag_bool, bool debug = false);
	static bool mpi_recvBool(int rank, int source, int tag = mpi_tag_bool, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);
	static bool mpi_tryRecvBool(int rank, int source, bool& result, int tag = mpi_tag_bool, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);

	static void mpi_sendInt(int rank, const int num, int dest, int tag = mpi_tag_int, bool debug = false);
	static int mpi_recvInt(int rank, int source, int tag = mpi_tag_int, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);
	static bool mpi_tryRecvInt(int rank, int source, int& result, int tag = mpi_tag_int, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);

	static void mpi_sendUint64(int rank, const std::uint64_t num, int dest, int tag = mpi_tag_uint64, bool debug = false);
	static std::uint64_t mpi_recvUint64(int rank, int source, int tag = mpi_tag_uint64, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);
	static bool mpi_tryRecvUint64(int rank, int source, std::uint64_t& result, int tag = mpi_tag_uint64, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);

	static void mpi_sendString(int rank, const std::string& s, int dest, int tag = mpi_tag_string, bool debug = false);
	static std::string mpi_recvString(int rank, int source, int tag = mpi_tag_string, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);
	static bool mpi_tryRecvString(int rank, int source, std::string& result, int tag = mpi_tag_string, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);

	static void mpi_sendPairUint64(int rank, const std::array<std::uint64_t, 2>& arr, int dest, int tag = mpi_tag_pair_uint64, bool debug = false);
	static std::array<std::uint64_t, 2> mpi_recvPairUint64(int rank, int source, int tag = mpi_tag_pair_uint64, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);
	static bool mpi_tryRecvPairUint64(int rank, int source, std::array<std::uint64_t, 2>& result, int tag = mpi_tag_pair_uint64, MPI_Status* optOut_status = MPI_STATUS_IGNORE, bool debug = false);

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

#endif // XAMIDI_HELPER_FCTHELPER_H
