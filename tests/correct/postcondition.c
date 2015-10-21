// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() 
ensures \result == 1
{
    int i;

    i = 1;
    
    assert(i == 1);
    
    return 1;
}
