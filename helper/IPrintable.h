#ifndef XAMIDI_HELPER_IPRINTABLE_H
#define XAMIDI_HELPER_IPRINTABLE_H

#include <memory>
#include <string>

namespace xamidi {
namespace helper {

//#######################
//# Printable Interface #
//#######################

struct IPrintable {
	virtual ~IPrintable();

	// Abstract methods
	virtual std::string toString() const = 0;

	// Methods
	std::wstring toWString() const;
	std::ostream& print(std::ostream& os) const;
	std::ostream& println(std::ostream& os) const;
	std::wostream& wprint(std::wostream& os) const;
	std::wostream& wprintln(std::wostream& os) const;

	// Operators
	friend std::ostream& operator<<(std::ostream& out, const IPrintable& obj);
	friend std::wostream& operator<<(std::wostream& out, const IPrintable& obj);
};

template<typename T>
class IPointToPrintableValue: public IPrintable {
	static_assert(std::is_base_of<IPrintable, T>::value, "T must derive from xamidi::helper::IPrintable.");

	// Abstract methods
	virtual const std::shared_ptr<T>& getValue() const = 0;

	virtual std::string toString() const override {
		return getValue()->toString();
	}
};

//##################
//# String Wrapper #
//##################

struct String: public IPrintable {
	std::string value;
	explicit String(const std::string& value);
	String();
	virtual ~String();
	virtual std::string toString() const override;

	// Operators
	String& operator=(const String& other);
	friend bool operator==(const String& lhs, const String& rhs);
	friend bool operator==(const String& lhs, const std::string& rhs);
	friend bool operator==(const std::string& lhs, const String& rhs);
	friend bool operator!=(const String& lhs, const String& rhs);
	friend bool operator!=(const String& lhs, const std::string& rhs);
	friend bool operator!=(const std::string& lhs, const String& rhs);
};

}
}

#endif // XAMIDI_HELPER_IPRINTABLE_H
