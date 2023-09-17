#ifndef XAMIDI_HELPER_VERSION_H
#define XAMIDI_HELPER_VERSION_H

#include <cstddef>
#include <cstdint>
#include <type_traits>

#define TOOL_NAME "pmGenerator"
#define TOOL_REPOSITORY "https://github.com/xamidi/pmGenerator"
#define TOOL_VERSION_MAJOR 1
#define TOOL_VERSION_MINOR 1
#define TOOL_VERSION_PATCH 2
#define TOOL_VERSION_SPEC "1.1.2"
#define TOOL_VERSION_BRANCH "c++11"

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
// NOTE: More features available at https://github.com/xamidi/pmGenerator/blob/dd29163745c38c3e8d6dd871be6e3929f4dcaa45/helper/Version.h?ts=4#L79-L252
//       The following approach is rather sophisticated (and a proof of concept) for being able to assign concatenated strings to 'constexpr const char*' variables in C++11.
//       To only assign concatenated strings to, for example, variables of type 'constexpr std::array<char, [...]>', would be much simpler (example: https://stackoverflow.com/q/28708497),
//       but std::array<[...]>::data() is not constexpr in C++11.

// Parameter pack helpers (similar to C++14)
template<std::size_t ...> struct _index_sequence { using type = _index_sequence; };
template<std::size_t N, std::size_t ... S> struct gen_pack_sequence: gen_pack_sequence<N - 1, N - 1, S...> {};
template<std::size_t ... S> struct gen_pack_sequence<0, S...> : _index_sequence<S...> {};
template<std::size_t N> using _make_index_sequence = typename gen_pack_sequence<N>::type;

namespace typelist { // To be able to concatenate constexpr strings despite C++11 restrictions, define a list of types that may contain chars. ; Concept: https://stackoverflow.com/a/275295

template<typename T, T V> struct Value { typedef T type; enum { value = V }; };
template<char V> struct Char : Value<char, V> {};
template<typename ...> struct TypeList;
template<typename T, typename ... TT> struct TypeList<T, TT...> {
	typedef T type;
	typedef TypeList<TT...> tail;
};
template<> struct TypeList<> {};
template<typename List> struct GetSize;
template<typename ... Items> struct GetSize<TypeList<Items...>> { enum { value = sizeof...(Items) }; };
template<typename ... T> struct ConcatList;
template<typename ... First, typename ... Second, typename ... Tail> struct ConcatList<TypeList<First...>, TypeList<Second...>, Tail...> {
	typedef typename ConcatList<TypeList<First..., Second...>, Tail...>::type type;
};
template<typename T> struct ConcatList<T> { typedef T type; };
template<typename NewItem, typename List> struct PrependItem;
template<typename NewItem, typename ... Items> struct PrependItem<NewItem, TypeList<Items...>> { typedef TypeList<NewItem, Items...> type; };
template<typename List> struct PopFront;
template<typename OldItem, typename ... Items> struct PopFront<TypeList<OldItem, Items...>> { typedef TypeList<Items...> type; };
template<typename List, std::size_t N, typename = void> struct GetItem {
	static_assert(GetSize<List>::value > 0, "index out of bounds");
	typedef typename GetItem<typename List::tail, N - 1>::type type;
};
template<typename List> struct GetItem<List, 0> { static_assert(GetSize<List>::value > 0, "index out of bounds"); typedef typename List::type type; };
template<typename List, std::size_t I, typename NewItem> struct ReplaceItem {
	static_assert(GetSize<List>::value > 0, "index out of bounds");
	typedef typename PrependItem<typename List::type, typename ReplaceItem<typename List::tail, I - 1, NewItem>::type>::type type;
};
template<typename NewItem, typename Type, typename ... T> struct ReplaceItem<TypeList<Type, T...>, 0, NewItem> { typedef TypeList<NewItem, T...> type; };
template<typename ... T> struct ConcatStringList;
template<typename S, typename ... First, typename ... Second, typename ... Tail> struct ConcatStringList<TypeList<First...>, TypeList<S, Second...>, Tail...> {
	typedef typename ReplaceItem<TypeList<First...>, GetSize<TypeList<First...>>::value - 1, S>::type first;
	typedef typename PopFront<TypeList<S, Second...>>::type second;
	typedef typename ConcatList<first, second>::type concat;
	typedef typename ConcatStringList<concat, Tail...>::type type;
};
template<typename T> struct ConcatStringList<T> { typedef T type; };

} // END namespace typelist

// Functional programming with templates to obtain constexpr char arrays
template<char ... Chars> struct to_list { typedef typelist::TypeList<typelist::Char<Chars>...> type; };
template<char ... Chars> struct char_sequence {
	static constexpr char value[] = { Chars... };
	typedef typename to_list<Chars...>::type list;
	template<template<char...> class Template> using param_pack = Template<Chars...>;
};
template<char ... Chars> constexpr char char_sequence<Chars...>::value[];
template<char ... Chars> struct char_string: char_sequence<Chars..., '\0'> {};
template<std::uint8_t ... Digits> struct num_array_string {
	typedef char_string<('0' + Digits)...> type;
};

template<std::size_t Add, std::uint8_t ... Digits> struct add_leading_zeros {
	typedef typename add_leading_zeros<Add - 1, 0, Digits...>::type type;
};
template<std::uint8_t ... Digits> struct add_leading_zeros<0, Digits...> {
	typedef typename num_array_string<Digits...>::type type;
};
template<typename UInt, UInt Num, std::size_t Len = 1, typename TCheck = void, std::uint8_t ... Digits> struct num_to_string;
template<typename UInt, UInt Num, std::size_t Len, std::uint8_t ... Digits> struct num_to_string<UInt, Num, Len, typename std::enable_if<Num == 0>::type, Digits...> {
	typedef typename add_leading_zeros<sizeof...(Digits) < Len ? Len - sizeof...(Digits) : 0, Digits...>::type type;
};
template<typename UInt, UInt Num, std::size_t Len, std::uint8_t ... Digits> struct num_to_string<UInt, Num, Len, typename std::enable_if<Num != 0>::type, Digits...> {
	typedef typename num_to_string<UInt, Num / 10, Len, void, Num % 10, Digits...>::type type;
};

template<typename CharList, typename = _make_index_sequence<typelist::GetSize<CharList>::value>> struct list_to_string;
template<typename CharList, std::size_t ... Indices> struct list_to_string<CharList, _index_sequence<Indices...>> {
	static_assert(sizeof...(Indices) > 0 && typelist::GetItem<CharList, sizeof...(Indices) - 1>::type::value == 0, "missing null-termination");
	typedef char_sequence<typelist::GetItem<CharList, Indices>::type::value...> type;
};

constexpr std::size_t _strlen(char const* s, std::size_t count = 0) {
	return (*s == '\0') ? count : _strlen(s + 1, count + 1);
}

// Compile-time string literals ; Concept: https://ideone.com/QvXuYf
template<typename S, typename T> struct _struct_to_string;
template<typename S, std::size_t ... Indices> struct _struct_to_string<S, _index_sequence<Indices...>> { typedef char_string<S::get()[Indices] ...> type; };
template<typename S> struct struct_to_string { typedef _make_index_sequence<_strlen(S::get())> indices; typedef typename _struct_to_string<S, indices>::type type; };
#define CONSTEXPR_STRING(name, s) \
	struct name ## __struct { constexpr static const char* get() { return s; } }; \
	typedef struct_to_string<name ## __struct>::type name

template<typename ... Strings> struct concatenate {
	template<typename String> using list = typename String::list;
	typedef typename list_to_string<typename typelist::ConcatStringList<list<Strings>...>::type>::type type;
};

typedef num_to_string<std::uint32_t, BUILD_YEAR, 4>::type __buildYear;
typedef num_to_string<std::uint32_t, BUILD_MONTH, 2>::type __buildMonth;
typedef num_to_string<std::uint32_t, BUILD_DAY, 2>::type __buildDay;
typedef num_to_string<std::uint32_t, BUILD_HOUR, 2>::type __buildHour;
typedef num_to_string<std::uint32_t, BUILD_MINUTE, 2>::type __buildMinute;
typedef num_to_string<std::uint32_t, BUILD_SECOND, 2>::type __buildSecond;
CONSTEXPR_STRING(__dot, ".");
CONSTEXPR_STRING(__colon, ":");
CONSTEXPR_STRING(__space, " ");
CONSTEXPR_STRING(__openBranch, " ('");
CONSTEXPR_STRING(__closeBranch, "' branch)");
typedef concatenate<__buildYear, __dot, __buildMonth, __dot, __buildDay>::type __buildDate;
typedef concatenate<__buildHour, __colon, __buildMinute, __colon, __buildSecond>::type __buildTime;
typedef concatenate<__buildDate, __dot, __buildHour, __buildMinute>::type __buildIdentifier;
CONSTEXPR_STRING(__name, TOOL_NAME);
CONSTEXPR_STRING(__version_spec, TOOL_VERSION_SPEC);
CONSTEXPR_STRING(__version_branch, TOOL_VERSION_BRANCH);
typedef concatenate<__name, __space, __version_spec, __space, __buildIdentifier, __openBranch, __version_branch, __closeBranch>::type __version;
CONSTEXPR_STRING(__repository, TOOL_REPOSITORY);

} // END namespace helper

constexpr const char* buildYear = helper::__buildYear::value;
constexpr const char* buildMonth = helper::__buildMonth::value;
constexpr const char* buildDay = helper::__buildDay::value;
constexpr const char* buildDate = helper::__buildDate::value;
constexpr const char* buildTime = helper::__buildTime::value;
constexpr const char* buildIdentifier = helper::__buildIdentifier::value;
constexpr const char* version = helper::__version::value;
constexpr const char* repository = helper::__repository::value;

}

#endif // XAMIDI_HELPER_VERSION_H
