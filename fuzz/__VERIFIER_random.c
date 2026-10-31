#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static int initialized = 0;
static unsigned int seed;

enum {
     __VERIFIER_TRACE_LENGTH = 0x10000
};

static unsigned int __VERIFIER_index = 0;

typedef struct {
    unsigned int sign;
    unsigned long long sample;
    const char *fn;
} Sample;

static Sample __VERIFIER_counterexample[__VERIFIER_TRACE_LENGTH] = { 0 };

void store(unsigned int sign, unsigned long long sample, const char *fn) {
    if(__VERIFIER_index >= __VERIFIER_TRACE_LENGTH)
        exit(0);

    Sample *entry = &__VERIFIER_counterexample[__VERIFIER_index++];
    entry->sign   = sign;
    entry->sample = sample;
    entry->fn     = fn;
}

void output(unsigned int sign, unsigned long long sample, const char *fn) {
    if(sign) {
        printf("%s(%lld)\n", fn, sample);
    } else {
        printf("%s(%llu)\n", fn, sample);
    }
    fflush(stdout);
}

void __assert_fail(const char * assertion, const char * file, unsigned int line, const char * function) {
    alarm(0);
    printf("unsat\n");
    /* print trace in reverse, like Eldarica */

    unsigned int i;

    for(i = __VERIFIER_index; i > 0; i--) {
        Sample *entry = &__VERIFIER_counterexample[i-1];
        output(entry->sign, entry->sample, entry->fn);
    }

    printf("srand(%u)\n", seed);

    exit(0);
}

static void initialize() {
    if(!initialized) {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);
        seed = now.tv_nsec;
        srand(seed);
        signal(SIGALRM, exit);
        alarm(1);
        initialized = 1;
    }
}

unsigned long long generate(unsigned int sign) {
    if(sign) {
        /* the ranges reach one further up than down, such that 1 is drawn as often as -1 by the narrowest range
           (skippedu needs exactly 1) */
        switch(rand()%6) {
            case 0: return (unsigned long long)  0;
            case 1: return (unsigned long long) (rand() %     2);
            case 2: return (unsigned long long) (rand() %     8 -     3);
            case 3: return (unsigned long long) (rand() %    32 -    15);
            case 4: return (unsigned long long) (rand() %  1024 -   511);
            case 5: return (unsigned long long) (rand() % 65536 - 32767);
        }
    } else {
        switch(rand()%6) {
            case 0: return (unsigned long long)  0;
            case 1: return (unsigned long long) (rand() %     2);
            case 2: return (unsigned long long) (rand() %     8);
            case 3: return (unsigned long long) (rand() %    32);
            case 4: return (unsigned long long) (rand() %  1024);
            case 5: return (unsigned long long) (rand() % 65536);
        }
    }

    return 0; /* shut up compiler warning */
}

/*
 * Construct non-uniformly distributed small values centering around 0
 */
unsigned long long __VERIFIER_next_nondet(unsigned int sign, unsigned int bits, const char *fn) {
    unsigned long long sample;

    initialize();
    sample = generate(sign);
    store(sign, sample, fn);
    return sample;
}
