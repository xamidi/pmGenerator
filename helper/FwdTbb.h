#ifndef XAMIDI_HELPER_FWDTBB_H
#define XAMIDI_HELPER_FWDTBB_H

//#if __has_include(<tbb/version.h>) // NOTE: Change manually if required. There seems to be no alternative for __has_include in C++11.
#include <tbb/version.h>
//#else
//#include <tbb/tbb_stddef.h>
//#endif

#include <functional>
#include <utility>

namespace tbb {
#if TBB_INTERFACE_VERSION >= 12002 // since v2021.1-beta08
namespace detail { namespace d1 { template<typename T> class tbb_allocator; template<typename T> class cache_aligned_allocator; template<typename T, typename Allocator> class concurrent_vector; template<typename Key, typename T, typename Hash, typename KeyEqual, typename Allocator> class concurrent_unordered_map; template<typename Key, typename Hash, typename KeyEqual, typename Allocator> class concurrent_unordered_set; } }
using detail::d1::tbb_allocator;
using detail::d1::cache_aligned_allocator;
using detail::d1::concurrent_vector;
using detail::d1::concurrent_unordered_map;
using detail::d1::concurrent_unordered_set;
#if TBB_INTERFACE_VERSION >= 12040 // since v2021.4.0
namespace detail { namespace d2 { template<typename Key, typename Value, typename Compare, typename Allocator> class concurrent_map; } }
using detail::d2::concurrent_map;
#else
namespace detail { namespace d1 { template<typename Key, typename Value, typename Compare, typename Allocator> class concurrent_map; } }
using detail::d1::concurrent_map;
#endif
#else
template<typename T> class tbb_allocator;
template<typename T> class cache_aligned_allocator;
template<typename T, typename Allocator> class concurrent_vector;
template<typename Key> class tbb_hash;
namespace interface5 { template<typename Key, typename T, typename Hash, typename KeyEqual, typename Allocator> class concurrent_unordered_map; template<typename Key, typename Hash, typename KeyEqual, typename Allocator> class concurrent_unordered_set; }
using interface5::concurrent_unordered_map;
using interface5::concurrent_unordered_set;
namespace interface10 { template<typename Key, typename Value, typename Compare, typename Allocator> class concurrent_map; }
using interface10::concurrent_map;
#define TBB_PREVIEW_CONCURRENT_ORDERED_CONTAINERS 1
#endif
}

namespace xamidi {
template<typename T> using tbb_concurrent_vector = tbb::concurrent_vector<T, tbb::cache_aligned_allocator<T>>;
#if TBB_INTERFACE_VERSION >= 12002 // since v2021.1-beta08
template<typename Key, typename T> using tbb_concurrent_unordered_map = tbb::concurrent_unordered_map<Key, T, std::hash<Key>, std::equal_to<Key>, tbb::tbb_allocator<std::pair<const Key, T>>>;
template<typename Key> using tbb_concurrent_unordered_set = tbb::concurrent_unordered_set<Key, std::hash<Key>, std::equal_to<Key>, tbb::tbb_allocator<Key>>;
#else
template<typename Key, typename T> using tbb_concurrent_unordered_map = tbb::concurrent_unordered_map<Key, T, tbb::tbb_hash<Key>, std::equal_to<Key>, tbb::tbb_allocator<std::pair<const Key, T>>>;
template<typename Key> using tbb_concurrent_unordered_set = tbb::concurrent_unordered_set<Key, tbb::tbb_hash<Key>, std::equal_to<Key>, tbb::tbb_allocator<Key>>;
#endif
template<typename Key, typename Value> using tbb_concurrent_map = tbb::concurrent_map<Key, Value, std::less<Key>, tbb::tbb_allocator<std::pair<const Key, Value>>>;
}

#endif // XAMIDI_HELPER_FWDTBB_H
