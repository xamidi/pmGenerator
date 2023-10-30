#include "ProgressData.h"

#include "FctHelper.h"

#include <cstring>
#include <iostream>
#include <iterator>

using namespace std;

namespace xamidi {
namespace helper {

ProgressData::ProgressData(unsigned percentageStepSize, uint64_t maximum, bool estimated) :
		percentageStepSize(percentageStepSize), maximum(maximum), maximumEstimated(estimated), progressSteps([&]() {
			if (!FctHelper::vectorContains(vector<unsigned> { 1, 2, 4, 5, 10, 20, 25, 50, 100 }, percentageStepSize))
				throw logic_error("ProgressData(): 100 / percentageStepSize = 100 / " + to_string(percentageStepSize) + " is not an integer.");
			if (maximum && maximum < 100 / percentageStepSize) { // there are too few steps to have such a resolution
				percentageStepSize = 100 / static_cast<unsigned>(maximum); // may not be the final value, since 100 / percentageStepSize may not be an integer
				if (!FctHelper::vectorContains(vector<unsigned> { 1, 2, 4, 5, 10, 20, 25, 50, 100 }, percentageStepSize)) {
					if (percentageStepSize == 3)
						percentageStepSize = 4;
					else if (5 < percentageStepSize && percentageStepSize < 10)
						percentageStepSize = 10;
					else if (10 < percentageStepSize && percentageStepSize < 20)
						percentageStepSize = 20;
					else if (20 < percentageStepSize && percentageStepSize < 25)
						percentageStepSize = 25;
					else if (25 < percentageStepSize && percentageStepSize < 50)
						percentageStepSize = 50;
					else if (50 < percentageStepSize && percentageStepSize < 100)
						percentageStepSize = 100;
				}
				this->percentageStepSize = percentageStepSize;
			}
			unsigned stepAmount = 100 / percentageStepSize;
			vector<uint64_t> steps(stepAmount);
			for (unsigned i = 0; i < stepAmount; i++)
				steps[i] = static_cast<uint64_t>(static_cast<double>(maximum) * (i + 1) * percentageStepSize / 100.0);
			steps.push_back(0); // to avoid bound checks and never trigger at final state
			return steps;
		}()) {
}

ProgressData& ProgressData::operator=(const ProgressData& other) {
	percentageStepSize = other.percentageStepSize;
	maximum = other.maximum;
	maximumEstimated = other.maximumEstimated;
	progressSteps = other.progressSteps;
	progress = static_cast<uint64_t>(other.progress);
	progressState = static_cast<uint64_t>(other.progressState);
	return *this;
}

void ProgressData::setStartTime() {
	startTime = chrono::system_clock::now();
}

bool ProgressData::nextStep() {
	return ++progress == progressSteps[progressState];
}

bool ProgressData::nextState(string& percentage, string& progress, string& estimateToComplete) {
	if (progressState + 1 < progressSteps.size()) {
		uint64_t progressInSteps = progressSteps[progressState++];
		uint64_t pcnt = progressState * percentageStepSize;
		percentage = string(maximumEstimated || pcnt < 100 ? "≈" : "") + (pcnt < 100 ? pcnt < 10 ? maximumEstimated ? "  " : " " : maximumEstimated ? " " : "" : "") + to_string(pcnt);
		unsigned numeratorLen = FctHelper::digitsNum_uint64(progressInSteps);
		unsigned numeratorMaxLen = FctHelper::digitsNum_uint64(*prev(progressSteps.end(), 2));
		stringstream ss_progress;
		ss_progress << string(numeratorMaxLen - numeratorLen, ' ') << progressInSteps << " of " << (maximumEstimated ? "approximately " : "") << maximum;
		progress = ss_progress.str();
		chrono::microseconds durRemaining = chrono::duration_cast<chrono::microseconds>(chrono::system_clock::now() - startTime);
		long double durUs = durRemaining.count() * (static_cast<long double>(maximum) / progressInSteps);
		if (durUs > UINT64_MAX)
			cerr << "Warning: Overflow in ProgressData::nextState() invalidated progress durations." << endl;
		chrono::microseconds durFull(static_cast<uint64_t>(durUs));
		durRemaining = durFull - durRemaining;
		time_t time = chrono::system_clock::to_time_t(startTime + durFull);
		stringstream ss_etc;
		ss_etc << "ETC: " << strtok(ctime(&time), "\n") << " ; " << FctHelper::durationYearsToMs(durRemaining) << " remaining ; " << FctHelper::durationYearsToMs(durFull) << " total";
		estimateToComplete = ss_etc.str();
		return true;
	} else
		return false;
}

}
}
