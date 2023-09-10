#ifndef XAMIDI_HELPER_PROGRESSDATA_H
#define XAMIDI_HELPER_PROGRESSDATA_H

#include <atomic>
#include <chrono>
#include <cstdint>
#include <string>
#include <vector>

namespace xamidi {
namespace helper {

struct ProgressData {
	unsigned percentageStepSize = 0;
	std::uint64_t maximum = 0;
	bool maximumEstimated = false;
	std::chrono::time_point<std::chrono::system_clock> startTime;
	std::vector<std::uint64_t> progressSteps;
	std::atomic<std::uint64_t> progress = 0;
	std::atomic<std::uint64_t> progressState = 0;
	ProgressData() = default;
	ProgressData(const ProgressData& other) : percentageStepSize(other.percentageStepSize), maximum(other.maximum), maximumEstimated(other.maximumEstimated), progressSteps(other.progressSteps), progress((std::uint64_t) other.progress), progressState((std::uint64_t) other.progressState) { }
	ProgressData(unsigned percentageStepSize, std::uint64_t maximum, bool estimated = false);
	ProgressData& operator=(const ProgressData& other);
	void setStartTime();
	bool nextStep();
	bool nextState(std::uint64_t& percentage, std::string& progress, std::string& estimateToComplete);
};

}
}

#endif // XAMIDI_HELPER_PROGRESSDATA_H
