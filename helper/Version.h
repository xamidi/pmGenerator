#ifndef XAMIDI_HELPER_VERSION_H
#define XAMIDI_HELPER_VERSION_H

#include <array>
#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <utility>

#define TOOL_NAME "pmGenerator"
#define TOOL_REPOSITORY "https://github.com/xamidi/pmGenerator"
#define TOOL_VERSION_MAJOR 1
#define TOOL_VERSION_MINOR 2
#define TOOL_VERSION_PATCH 3
#define TOOL_VERSION_SPEC "1.2.3"
#define TOOL_VERSION_BRANCH "master"

#define BUILD_YEAR \
	( \
		(__DATE__[10] >= '0' && __DATE__[10] <= '9') ? \
		(__DATE__[ 7] >= '0' && __DATE__[ 7] <= '9' ? (__DATE__[7] - '0') * 1000 : 0) + \
		(__DATE__[ 8] >= '0' && __DATE__[ 8] <= '9' ? (__DATE__[8] - '0') * 100 : 0) + \
		(__DATE__[ 9] >= '0' && __DATE__[ 9] <= '9' ? (__DATE__[9] - '0') * 10 : 0) + (__DATE__[10] - '0') : UINT32_MAX \
	)
static_assert(BUILD_YEAR != UINT32_MAX, "indeterminate build year");

#define BUILD_MONTH \
	( \
		(__DATE__[0] == 'J' && __DATE__[1] == 'a' && __DATE__[2] == 'n') ?  1 : \
		(__DATE__[0] == 'F')                                             ?  2 : \
		(__DATE__[0] == 'M' && __DATE__[1] == 'a' && __DATE__[2] == 'r') ?  3 : \
		(__DATE__[0] == 'A' && __DATE__[1] == 'p')                       ?  4 : \
		(__DATE__[0] == 'M' && __DATE__[1] == 'a' && __DATE__[2] == 'y') ?  5 : \
		(__DATE__[0] == 'J' && __DATE__[1] == 'u' && __DATE__[2] == 'n') ?  6 : \
		(__DATE__[0] == 'J' && __DATE__[1] == 'u' && __DATE__[2] == 'l') ?  7 : \
		(__DATE__[0] == 'A' && __DATE__[1] == 'u')                       ?  8 : \
		(__DATE__[0] == 'S')                                             ?  9 : \
		(__DATE__[0] == 'O')                                             ? 10 : \
		(__DATE__[0] == 'N')                                             ? 11 : \
		(__DATE__[0] == 'D')                                             ? 12 : \
		UINT32_MAX \
	)
static_assert(BUILD_MONTH != UINT32_MAX, "indeterminate build month");

#define BUILD_DAY \
	( \
		(__DATE__[5] >= '0' && __DATE__[5] <= '9') ? \
		(__DATE__[4] >= '0' && __DATE__[4] <= '9' ? (__DATE__[4] - '0') * 10 : 0) + (__DATE__[5] - '0') : UINT32_MAX \
	)
static_assert(BUILD_DAY != UINT32_MAX, "indeterminate build day");

#define BUILD_HOUR \
	( \
		(__TIME__[0] >= '0' && __TIME__[0] <= '9' && \
		 __TIME__[1] >= '0' && __TIME__[1] <= '9') ? \
		(__TIME__[0] - '0') * 10 + __TIME__[1] - '0' : UINT32_MAX \
	)
static_assert(BUILD_HOUR != UINT32_MAX, "indeterminate build hour");

#define BUILD_MINUTE \
	( \
		(__TIME__[3] >= '0' && __TIME__[3] <= '9' && \
		 __TIME__[4] >= '0' && __TIME__[4] <= '9') ? \
		(__TIME__[3] - '0') * 10 + __TIME__[4] - '0' : UINT32_MAX \
	)
static_assert(BUILD_MINUTE != UINT32_MAX, "indeterminate build minute");

#define BUILD_SECOND \
	( \
		(__TIME__[6] >= '0' && __TIME__[6] <= '9' && \
		 __TIME__[7] >= '0' && __TIME__[7] <= '9') ? \
		(__TIME__[6] - '0') * 10 + __TIME__[7] - '0' : UINT32_MAX \
	)
static_assert(BUILD_SECOND != UINT32_MAX, "indeterminate build second");

namespace xamidi {
namespace helper {

// Functional programming with templates to obtain constexpr char arrays
template<std::uint8_t ... Digits> constexpr std::array<char, sizeof...(Digits) + 1> num_array_string = { ('0' + Digits)..., 0 };
template<std::size_t Add, std::uint8_t ... Digits> constexpr std::enable_if_t<Add == 0, std::array<char, sizeof...(Digits) + Add + 1>> add_leading_zeros() {
	return num_array_string<Digits...>;
}
template<std::size_t Add, std::uint8_t ... Digits> constexpr std::enable_if_t<Add != 0, std::array<char, sizeof...(Digits) + Add + 1>> add_leading_zeros() {
	return add_leading_zeros<Add - 1, 0, Digits...>();
}
template<typename UInt, UInt Num, std::size_t Len = 1, std::uint8_t ... Digits> constexpr std::enable_if_t<Num == 0, std::array<char, Len + 1>> num_to_string() {
	return add_leading_zeros<sizeof...(Digits) < Len ? Len - sizeof...(Digits) : 0, Digits...>();
}
template<typename UInt, UInt Num, std::size_t Len = 1, std::uint8_t ... Digits> constexpr std::enable_if_t<Num != 0, std::array<char, Len + 1>> num_to_string() {
	return num_to_string<UInt, Num / 10, Len, Num % 10, Digits...>();
}

template<std::size_t N, std::size_t ... Indices> constexpr std::array<char, N> to_string(const char (&s)[N], std::index_sequence<Indices...>) {
	return { {s[Indices]...}};
}
template<std::size_t N> constexpr std::array<char, N> to_string(const char (&s)[N]) {
	return to_string(s, std::make_index_sequence<N>());
}
template<std::size_t N> constexpr std::array<char, N> to_string(std::array<char, N> s) {
	return s;
}

template<typename T, std::size_t ... Lengths> constexpr auto _concatenate(const std::array<T, Lengths>& ... strings) { // for null-terminated strings
	std::array<T, ((Lengths - 1) + ...) + 1> result;
	std::size_t index = 0;
	((std::copy_n(strings.begin(), Lengths, result.begin() + index), index += (Lengths - 1)), ...);
	return result;
}
template<typename ... Strings> constexpr auto concatenate(const Strings& ... strings) {
	return _concatenate(to_string(strings)...);
}

constexpr std::array<char, 5> __buildYear = num_to_string<std::uint32_t, BUILD_YEAR, 4>();
constexpr std::array<char, 3> __buildMonth = num_to_string<std::uint32_t, BUILD_MONTH, 2>();
constexpr std::array<char, 3> __buildDay = num_to_string<std::uint32_t, BUILD_DAY, 2>();
constexpr std::array<char, 3> __buildHour = num_to_string<std::uint32_t, BUILD_HOUR, 2>();
constexpr std::array<char, 3> __buildMinute = num_to_string<std::uint32_t, BUILD_MINUTE, 2>();
constexpr std::array<char, 3> __buildSecond = num_to_string<std::uint32_t, BUILD_SECOND, 2>();
constexpr std::array<char, 11> __buildDate = concatenate(__buildYear, ".", __buildMonth, ".", __buildDay);
constexpr std::array<char, 9> __buildTime = concatenate(__buildHour, ":", __buildMinute, ":", __buildSecond);
constexpr std::array<char, 16> __buildIdentifier = concatenate(__buildDate, ".", __buildHour, __buildMinute);
constexpr auto __version = concatenate(TOOL_NAME, " ", TOOL_VERSION_SPEC, " ", __buildIdentifier, " ('", TOOL_VERSION_BRANCH, "' branch)");
constexpr auto __repository = to_string(TOOL_REPOSITORY);

} // END namespace helper

constexpr const char* buildYear = helper::__buildYear.data();
constexpr const char* buildMonth = helper::__buildMonth.data();
constexpr const char* buildDay = helper::__buildDay.data();
constexpr const char* buildDate = helper::__buildDate.data();
constexpr const char* buildTime = helper::__buildTime.data();
constexpr const char* buildIdentifier = helper::__buildIdentifier.data();
constexpr const char* version = helper::__version.data();
constexpr const char* repository = helper::__repository.data();

}

#endif // XAMIDI_HELPER_VERSION_H
