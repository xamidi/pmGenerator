#ifndef XAMID_HELPER_PROGRESSDATA_H
#define XAMID_HELPER_PROGRESSDATA_H

#include <atomic>
#include <chrono>
#include <string>
#include <vector>

namespace xamid {
namespace helper {

struct ProgressData {
	unsigned percentageStepSize = 0;
	uint64_t maximum = 0;
	bool maximumEstimated = false;
	std::chrono::time_point<std::chrono::system_clock> startTime;
	std::vector<uint64_t> progressSteps;
	std::atomic<uint64_t> progress;
	std::atomic<uint64_t> progressState;
	ProgressData() = default;
	ProgressData(const ProgressData& other) : percentageStepSize(other.percentageStepSize), maximum(other.maximum), maximumEstimated(other.maximumEstimated), progressSteps(other.progressSteps), progress((uint64_t) other.progress), progressState((uint64_t) other.progressState) { }
	ProgressData(unsigned percentageStepSize, uint64_t maximum, bool estimated = false);
	ProgressData& operator=(const ProgressData& other);
	void setStartTime();
	bool nextStep();
	bool nextState(uint64_t& percentage, std::string& progress, std::string& estimateToComplete);
};

}
}

#endif // XAMID_HELPER_PROGRESSDATA_H
