#include "IPrintable.h"

#include "FctHelper.h"

using namespace std;

namespace xamid {
namespace helper {

//#######################
//# Printable Interface #
//#######################

IPrintable::~IPrintable() {
}

// Methods
wstring IPrintable::toWString() const {
	return FctHelper::utf8toWide(toString());
}
ostream& IPrintable::print(ostream& os) const {
	return os << toString();
}
ostream& IPrintable::println(ostream& os) const {
	return os << toString() << endl;
}
wostream& IPrintable::wprint(wostream& os) const {
	return os << toWString();
}
wostream& IPrintable::wprintln(wostream& os) const {
	return os << toWString() << endl;
}

// Operators
ostream& operator<<(ostream& out, const IPrintable& obj) {
	return out << obj.toString();
}
wostream& operator<<(wostream& out, const IPrintable& obj) {
	return out << obj.toWString();
}

//##################
//# String Wrapper #
//##################

String::String(const string& value) :
		value(value) {
}
String::String() :
		value() {
}
String::~String() {
}
string String::toString() const {
	return value;
}

// Operators
String& String::operator=(const String& other) {
	value = other.value;
	return *this;
}
bool operator==(const String& lhs, const String& rhs) {
	if (&lhs == &rhs)
		return true;
	return lhs.value == rhs.value;
}
bool operator==(const String& lhs, const string& rhs) {
	return lhs.value == rhs;
}
bool operator==(const string& lhs, const String& rhs) {
	return lhs == rhs.value;
}
bool operator!=(const String& lhs, const String& rhs) {
	return lhs.value != rhs.value;
}
bool operator!=(const String& lhs, const string& rhs) {
	return lhs.value != rhs;
}
bool operator!=(const string& lhs, const String& rhs) {
	return lhs != rhs.value;
}

}
}
