// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int max()
ensures \result == 0
{
    int x;
    x = 0;

    {
        int x;
        x = 100;
    }

    return x;
}