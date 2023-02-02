#ifndef XAMID_METAMATH_DRULEREDUCER_H
#define XAMID_METAMATH_DRULEREDUCER_H

#include <string>

namespace xamid {
namespace metamath {

struct DRuleReducer {
	static void createReplacementsFile(const std::string& pmproofsFile = "data/pmproofs.txt", const std::string& outputFile = "data/pmproofs-reducer.txt", const std::string& inputFilePrefix = "data/dProofs-withConclusions/dProofs", bool memReduction = true, bool withConclusions = true, bool debug = false);
	static void applyReplacements(const std::string& initials, const std::string& replacementsFile = "data/pmproofs-reducer.txt", const std::string& pmproofsFile = "data/pmproofs.txt", const std::string& outputFile = "data/pmproofs-result.txt", bool styleAll = false, bool listAll = true, bool wrap = true, bool debug = false);
};

}
}

#endif // XAMID_METAMATH_DRULEREDUCER_H
