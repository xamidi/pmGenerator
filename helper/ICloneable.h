#ifndef XAMID_HELPER_ICLONEABLE_H
#define XAMID_HELPER_ICLONEABLE_H

#include <memory>
#include <unordered_map>

namespace xamid {
namespace helper {

// T : type of class that becomes cloneable
// L : parameter which contains lookups of all nested cloneable types (if they are nested, otherwise do not use), freely manageable by the user
template<typename T, typename L = void>
struct ICloneable {
	typedef std::unordered_map<const T*, std::shared_ptr<T>> CloneMap;

	virtual ~ICloneable() { // A class type is considered fully defined in its member functions' bodies, so we use the destructor for an assert that uses ICloneable<T, L>.
		static_assert(std::is_base_of<ICloneable<T, L>, T>::value, "T must be cloneable by this template instance.");
	}

	// Abstract methods
	// NOTE: When this function is called, it is to be assumed that 'this' has not yet a known clone.
	//       The function should merely clone the current object (of type T) according to its structure,
	//       so that 'out' is modified to be the clone. Saving/testing known clones has to be done
	//       elsewhere. [It is already implemented for clone(), cloneUniquePtr() and cloneSharedPtr().
	//       Parameters exist solely to propagate them to these functions when called on subcomponents.]
	virtual void cloneTo(T& out, CloneMap* knownClones = nullptr, L* allClones = nullptr) const = 0;

	// Methods
	T clone(bool useLookups = true, CloneMap* knownClones = nullptr, L* allClones = nullptr) const {
		if (useLookups) {
			if (knownClones) {
				typename CloneMap::iterator searchResult = knownClones->find(static_cast<const T*>(this));
				if (searchResult != knownClones->end()) {
					const std::shared_ptr<T>& knownCloneEntry = searchResult->second;
					if (knownCloneEntry)
						return *knownCloneEntry; // return a copy of the known clone entry
				}
			}
			CloneMap _knownClones;
			if (!knownClones)
				knownClones = &_knownClones;
			// For future lookups, let's just create a shared_ptr, so we do not have to clone 'this' again, and return a copy of its object.
			std::shared_ptr<T> lookupClone(new T);
			cloneTo(*lookupClone, knownClones, allClones);
			(*knownClones)[static_cast<const T*>(this)] = lookupClone;
			return *lookupClone;
		} else {
			T clone;
			cloneTo(clone, knownClones, allClones);
			return clone;
		}
	}
	std::unique_ptr<T> cloneUniquePtr(bool useLookups = true, CloneMap* knownClones = nullptr, L* allClones = nullptr) const {
		if (useLookups) {
			std::unique_ptr<T> clone(new T); // Since the pointer is unique, we always have to allocate a new address.
			if (knownClones) {
				typename CloneMap::iterator searchResult = knownClones->find(static_cast<const T*>(this));
				if (searchResult != knownClones->end()) {
					const std::shared_ptr<T>& knownCloneEntry = searchResult->second;
					if (knownCloneEntry) {
						*clone = *knownCloneEntry; // Copying a clone is sufficient and the best we can do for unique_ptr.
						return clone;
					}
				}
			}
			CloneMap _knownClones;
			if (!knownClones)
				knownClones = &_knownClones;
			cloneTo(*clone, knownClones, allClones);
			// For future lookups, let's copy the object of the just created unique_ptr and store it in a shared_ptr, so we do not have to clone 'this' again.
			std::shared_ptr<T> lookupClone(new T);
			*lookupClone = *clone;
			(*knownClones)[static_cast<const T*>(this)] = lookupClone;
			return clone;
		} else {
			std::unique_ptr<T> copy(new T);
			cloneTo(*copy, knownClones, allClones);
			return copy;
		}
	}
	std::shared_ptr<T> cloneSharedPtr(bool useLookups = true, CloneMap* knownClones = nullptr, L* allClones = nullptr) const {
		if (useLookups) {
			if (knownClones) {
				typename CloneMap::iterator searchResult = knownClones->find(static_cast<const T*>(this));
				if (searchResult != knownClones->end()) {
					const std::shared_ptr<T>& knownCloneEntry = searchResult->second;
					if (knownCloneEntry)
						return knownCloneEntry; // We can return the known clone itself (by reference).
				}
			}
			CloneMap _knownClones;
			if (!knownClones)
				knownClones = &_knownClones;
			std::shared_ptr<T> clone(new T);
			cloneTo(*clone, knownClones, allClones);
			(*knownClones)[static_cast<const T*>(this)] = clone; // Remember the shared address of the clone (for referencing).
			return clone;
		} else {
			std::shared_ptr<T> copy(new T);
			cloneTo(*copy, knownClones, allClones);
			return copy;
		}
	}
};

template<typename T>
struct ICopyable {
	virtual ~ICopyable() { // A class type is considered fully defined in its member functions' bodies, so we use the destructor for an assert that uses ICopyable<T>.
		static_assert(std::is_base_of<ICopyable<T>, T>::value, "T must be copyable by this template instance.");
	}

	// Abstract methods
	virtual void copyTo(T& out) const = 0;

	// Methods
	T copy() const {
		T copy;
		copyTo(copy);
		return copy;
	}
	std::unique_ptr<T> copyUniquePtr() const {
		std::unique_ptr<T> copy(new T);
		copyTo(*copy);
		return copy;
	}
	std::shared_ptr<T> copySharedPtr() const {
		std::shared_ptr<T> copy(new T);
		copyTo(*copy);
		return copy;
	}
};

}
}

#endif // XAMID_HELPER_ICLONEABLE_H
