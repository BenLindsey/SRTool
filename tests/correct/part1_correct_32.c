// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {
  assert (3 - 2 + 4 - 5 - 6 + - 1) == -7;
  return 0;
}
