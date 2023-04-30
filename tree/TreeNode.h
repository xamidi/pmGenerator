#ifndef XAMID_TREE_TREENODE_H
#define XAMID_TREE_TREENODE_H

#include "../helper/ICloneable.h"
#include "../helper/IPrintable.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iomanip>
#include <sstream>
#include <unordered_set>
#include <vector>

namespace xamid {
namespace tree {

// Represents a tree structure. Nodes are associated with values of type IPrintable.
// Nodes are not containers for values, but only take a shared ownership of them.
// Copying objects inside a tree would create an unnecessary overhead of object instances.
// Attribute vector<uint32_t> _meaning can be used for information composition such as by PossibilitiesListTreeNode.
template<typename T>
class TreeNode: public helper::IPointToPrintableValue<T>, public helper::ICloneable<TreeNode<T>> {
	static_assert(std::is_base_of<helper::IPrintable, T>::value, "T must derive from xamid::helper::IPrintable.");
	typedef std::unordered_map<const TreeNode<T>*, std::shared_ptr<TreeNode<T>>> TreeNodeCloneMap;
	std::shared_ptr<T> _value;
	std::vector<std::shared_ptr<TreeNode<T>>> _children;
	std::vector<std::uint32_t> _meaning;
public:
	TreeNode() { } // need a public default constructor for ICloneable
	TreeNode(const std::vector<std::uint32_t>& meaning, const std::shared_ptr<T>& value, const std::vector<std::shared_ptr<TreeNode<T>>>& children) : _value(value), _children(children), _meaning(meaning) { }
	explicit TreeNode(const std::shared_ptr<T>& value) : TreeNode( { }, value, { }) { }
	TreeNode(const std::vector<std::uint32_t>& meaning, const std::shared_ptr<T>& value) : TreeNode(meaning, value, { }) { }
	TreeNode(const std::shared_ptr<T>& value, const std::vector<std::shared_ptr<TreeNode<T>>>& children) : TreeNode( { }, value, children) { }
	bool hasMeaning(const std::vector<std::string>& meaning, const std::function<std::string(std::uint32_t)>& idLookup) const {
		if (_meaning.size() != meaning.size())
			return false;
		for (std::size_t i = 0; i < _meaning.size(); i++)
			if (idLookup(_meaning[i]) != meaning[i])
				return false;
		return true;
	}
	bool hasMeaning(const std::vector<std::uint32_t>& meaning) const {
		if (_meaning.size() != meaning.size())
			return false;
		for (std::size_t i = 0; i < _meaning.size(); i++)
			if (_meaning[i] != meaning[i])
				return false;
		return true;
	}
	void addChild(const std::shared_ptr<TreeNode<T>>& child) {
		_children.push_back(child);
	}
	const std::shared_ptr<T>& getValue() const override { // override for IPointToPrintableValue<T>
		return _value;
	}
	std::shared_ptr<T>& value() { // to freely manipulate value
		return _value;
	}
	const std::vector<std::shared_ptr<TreeNode<T>>>& getChildren() const { // to receive unmodifiable children (except for the pointed-to TreeNodes)
		return _children;
	}
	std::vector<std::shared_ptr<TreeNode<T>>>& children() { // to freely manipulate children
		return _children;
	}
	const std::vector<std::uint32_t>& getMeaning() const { // to receive unmodifiable meaning
		return _meaning;
	}
	std::vector<std::uint32_t>& meaning() { // to freely manipulate meaning
		return _meaning;
	}
	std::size_t height() const {
		std::size_t height = 0;
		auto recurse = [&height](const TreeNode<T>* node, std::size_t depth, const auto& me) -> void {
			if (node->_children.empty()) {
				if (depth > height)
					height = depth;
			} else
				for (std::size_t i = 0; i < node->_children.size(); i++)
					me(node->_children[i].get(), depth + 1, me);
		};
		recurse(this, 0, recurse);
		return height;
	}
	void cloneTo(TreeNode<T>& out, TreeNodeCloneMap* knownClones = nullptr, void* allClones = nullptr) const override { // override for ICloneable<TreeNode<T>>
		auto func = [&]() -> void {
			out._value = std::shared_ptr<T>(_value);
			out._meaning = _meaning;
			for (const std::shared_ptr<TreeNode<T>>& child : _children)
				out.addChild(child ? child->cloneSharedPtr(true, knownClones) : nullptr); // NOTE: 'allClones' is never used.
		};
		if (!knownClones) {
			TreeNodeCloneMap _knownClones;
			knownClones = &_knownClones;
			func();
		} else
			func();
	}

	// Representations
	std::string toAddressString() {
		auto recurse = [](const TreeNode<T>* node, const auto& me, const std::uint32_t& indent = 0) -> std::string {
			auto toBase16 = [](std::size_t value) {
				std::stringstream ss;
				ss << std::setbase(16) << value;
				return ss.str();
			};
			std::string str;
			for (std::uint32_t i = 0; i < indent; i++)
				str += "\t";
			if (node->_children.empty())
				str += "0x" + toBase16((std::size_t) node) + "\n";
			else {
				str += "0x" + toBase16((std::size_t) node) + " -> [\n";
				for (std::size_t i = 0; i < node->_children.size(); i++)
					str += me(node->_children[i].get(), me, indent + 1);
				for (std::uint32_t i = 0; i < indent; i++)
					str += "\t";
				str += "]\n";
			}
			return str;
		};
		return recurse(this, recurse);
	}
	std::string toString(const auto& fTtoString) const {
		auto recurse = [](const TreeNode<T>* node, const auto& me, const auto& fTtoString, const std::uint32_t& indent = 0) -> std::string {
			std::string str;
			for (std::uint32_t i = 0; i < indent; i++)
				str += "\t";
			if (node->_children.empty())
				str += fTtoString(*node->_value) + std::string("\n");
			else {
				str += fTtoString(*node->_value) + std::string(" -> [\n");
				for (std::size_t i = 0; i < node->_children.size(); i++)
					str += me(node->_children[i].get(), me, fTtoString, indent + 1);
				for (std::uint32_t i = 0; i < indent; i++)
					str += "\t";
				str += "]\n";
			}
			return str;
		};
		return recurse(this, recurse, fTtoString);
	}
	std::string toString() const override { // override for IPrintable<T> from IPointToPrintableValue<T>
		auto recurse = [](const TreeNode<T>* node, const auto& me, const std::uint32_t& indent = 0) -> std::string {
			std::string str;
			for (std::uint32_t i = 0; i < indent; i++)
				str += "\t";
			if (node->_children.empty())
				str += node->_value->toString() + "\n";
			else {
				str += node->_value->toString() + " -> [\n";
				for (std::size_t i = 0; i < node->_children.size(); i++)
					str += me(node->_children[i].get(), me, indent + 1);
				for (std::uint32_t i = 0; i < indent; i++)
					str += "\t";
				str += "]\n";
			}
			return str;
		};
		return recurse(this, recurse);
	}

	// Operators
	TreeNode<T>& operator=(const TreeNode<T>& other) {
		_value = other._value;
		_children = other._children;
		_meaning = other._meaning;
		return *this;
	}
	friend bool operator==(const TreeNode<T>& lhs, const TreeNode<T>& rhs) {
		if (&lhs == &rhs)
			return true;
		if (*lhs._value != *rhs._value)
			return false;
		const std::vector<std::shared_ptr<TreeNode<T>>>& lhsChildren = lhs.getChildren();
		const std::vector<std::shared_ptr<TreeNode<T>>>& rhsChildren = rhs.getChildren();
		if (lhsChildren.size() != rhsChildren.size())
			return false;
		for (unsigned i = 0; i < lhsChildren.size(); i++)
			if (*lhsChildren[i] != *rhsChildren[i])
				return false;
		return true;
	}
	friend bool operator!=(const TreeNode<T>& lhs, const TreeNode<T>& rhs) {
		return !(lhs == rhs);
	}

	// Helper methods
	bool cycleDetect() const {
		auto recurse = [](const TreeNode<T>* node, const std::unordered_set<const TreeNode<T>*>& knownAncestors, const auto& me) -> bool {
			if (knownAncestors.count(node))
				return true;
			const std::vector<std::shared_ptr<TreeNode<T>>>& children = node->getChildren();
			std::unordered_set<const TreeNode<T>*> knownAncestorsAndNode = knownAncestors;
			knownAncestorsAndNode.emplace(node);
			return std::any_of(children.begin(), children.end(), [&](const std::shared_ptr<TreeNode<T>>& descendant) { return me(descendant.get(), knownAncestorsAndNode, me); });
		};
		return recurse(this, { }, recurse);
	}
	bool cycleDetect(const auto& cycleHandler) const { // Cycle detection one-liner: node->cycleDetect([](const shared_ptr<TreeNode<T>>& cycle) { cerr << "Self reference found: " << *cycle->getValue() << endl; exit(0); });
		auto recurse = [&](const std::shared_ptr<TreeNode<T>>& node, const std::unordered_set<std::shared_ptr<TreeNode<T>>>& knownAncestors, const auto& me) -> bool {
			if (node.get() == this || knownAncestors.count(node)) {
				// NOTE: We handle 'this' differently since we do not have a shared_ptr for it, but want to use one in case it has a cycle (in which case we found a shared_ptr for it).
				cycleHandler(node);
				return true;
			}
			const std::vector<std::shared_ptr<TreeNode<T>>>& children = node->getChildren();
			std::unordered_set<std::shared_ptr<TreeNode<T>>> knownAncestorsAndNode = knownAncestors;
			knownAncestorsAndNode.emplace(node);
			return std::any_of(children.begin(), children.end(), [&](const std::shared_ptr<TreeNode<T>>& descendant) { return me(descendant, knownAncestorsAndNode, me); });
		};
		const std::vector<std::shared_ptr<TreeNode<T>>>& children = getChildren();
		std::unordered_set<std::shared_ptr<TreeNode<T>>> knownAncestorsAndNode;
		return std::any_of(children.begin(), children.end(), [&](const std::shared_ptr<TreeNode<T>>& descendant) { return recurse(descendant, knownAncestorsAndNode, recurse); });
	}
};

}
}

#endif // XAMID_TREE_TREENODE_H
