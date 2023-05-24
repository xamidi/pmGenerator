#ifndef XAMID_HELPER_HASHING_H
#define XAMID_HELPER_HASHING_H

// Idea: http://stackoverflow.com/q/7110301

#include <cstddef>
#include <functional>
#include <tuple>
#include <utility>
#include <vector>

namespace xamid {
namespace helper {

// Code from boost
// Reciprocal of the golden ratio helps spread entropy
//     and handles duplicates.
// See Mike Seymour in magic-numbers-in-boosthash-combine:
//     http://stackoverflow.com/q/4948780

// General function to combine sets of hashable values to one hash
template<class T>
inline void hash_combine(std::size_t& seed, const T& v) {
#if (SIZE_MAX == UINT64_MAX)
	seed ^= std::hash<T>()(v) + 0x9e3779b97f4a7c15uLL + (seed << 6) + (seed >> 2);
#else
	seed ^= std::hash<T>()(v) + 0x9e3779b9u + (seed << 6) + (seed >> 2);
#endif
}

// Generic iterator over tuple elements, to combine all values in the tuple to one hash
template<class Tuple, std::size_t Index = std::tuple_size<Tuple>::value - 1>
struct TupleHashValueImpl {
	static void apply(std::size_t& seed, const Tuple& tuple) {
		TupleHashValueImpl<Tuple, Index - 1>::apply(seed, tuple);
		hash_combine(seed, std::get<Index>(tuple));
	}
};
template<class Tuple>
struct TupleHashValueImpl<Tuple, 0> {
	static void apply(std::size_t& seed, const Tuple& tuple) {
		hash_combine(seed, std::get<0>(tuple));
	}
};

template<typename _Tp>
struct myhash: std::hash<_Tp> { // Supports everything that std::hash does, and more!
};

//###################################
//#     Tuple hashing function      #
//###################################
template<typename... TT>
struct myhash<std::tuple<TT...>> {
	std::size_t operator()(const std::tuple<TT...>& tt) const {
		std::size_t seed = 0;
		TupleHashValueImpl<std::tuple<TT...>>::apply(seed, tt);
		return seed;
	}
};

//###################################
//#     Vector hashing function     #
//###################################
template<typename T>
struct myhash<std::vector<T>> {
	std::size_t operator()(const std::vector<T>& vec) const {
		std::size_t seed = vec.size();
		for (const T& i : vec)
			hash_combine(seed, i);
		return seed;
	}
};

//###################################
//#     Pair hashing function       #
//###################################
template<typename T, typename U>
struct myhash<std::pair<T, U>> {
	std::size_t operator()(const std::pair<T, U>& t) const {
		std::size_t seed = 0;
		hash_combine(seed, t.first);
		hash_combine(seed, t.second);
		return seed;
	}
};

}
}

#endif // XAMID_HELPER_HASHING_H
