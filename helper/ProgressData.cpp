#include "ProgressData.h"

#include "FctHelper.h"

#include <cstring>
#include <iostream>

using namespace std;

namespace xamid {
namespace helper {

ProgressData::ProgressData(unsigned percentageStepSize, uint64_t maximum, bool estimated) :
		percentageStepSize(percentageStepSize), maximum(maximum), maximumEstimated(estimated), progressSteps([&]() {
			unsigned stepAmount = 100 / percentageStepSize;
			if (stepAmount * percentageStepSize == 100)
				stepAmount--; // do not show 100% progress
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

bool ProgressData::nextState(uint64_t& percentage, string& progress, string& estimateToComplete) {
	if (progressState + 1 < progressSteps.size()) {
		uint64_t progressInSteps = progressSteps[progressState++];
		percentage = progressState * percentageStepSize;
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
