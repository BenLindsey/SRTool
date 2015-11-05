// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int test() {
    return 0;
}
