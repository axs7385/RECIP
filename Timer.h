/****************************************************************************** 
 * timer.h 
 * record the elapsed time in microseconds (10^{-6} second)
 *****************************************************************************/

#ifndef _TIMER_LJ_
#define _TIMER_LJ_

#include <cstdlib>

#ifdef _WIN32
#include <windows.h>
#else
#include <sys/time.h>
#endif

class Timer {
public:
    Timer() { m_start = timestamp(); }
    void restart() { m_start = timestamp(); }
    long long elapsed() { return timestamp() - m_start; }

private:
    long long m_start;

    // Returns a timestamp ('now') in microseconds
    long long timestamp() {
#ifdef _WIN32
        LARGE_INTEGER frequency;
        LARGE_INTEGER now;
        QueryPerformanceFrequency(&frequency);
        QueryPerformanceCounter(&now);
        return (now.QuadPart * 1000000) / frequency.QuadPart;
#else
        struct timeval tp;
        gettimeofday(&tp, nullptr);
        return static_cast<long long>(tp.tv_sec) * 1000000 + tp.tv_usec;
#endif
    }
};

#endif
