// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int g;

int swagger() {

    assert (g == 0);

    return g;
}
