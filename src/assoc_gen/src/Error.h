#ifndef ERROR_H
#define ERROR_H

#include <iostream>

#define ASSERT(condition, message) \
    do { \
        if (! (condition)) { \
            std::cerr << "Assertion `" #condition "` failed in " << __FILE__ \
                      << " line " << __LINE__ << ": " << message << std::endl; \
            std::terminate(); \
        } \
    } while (false)

#ifdef DEBUG
#define DEBUG_PRINT std::cout
#else
#define DEBUG_PRINT 0 && std::cout
//#define DEBUG_PRINT std::cout
#endif

#define DEBUG_PRINT2 0 && std::cout
//#define DEBUG_PRINT2 std::cout

#define DEBUG_PRINT3 0 && std::cout
//#define DEBUG_PRINT3 std::cout

#endif
