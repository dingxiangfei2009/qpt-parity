#include <cstdio>
#include <string>

using std::stoi;

int main(int argc, const char ** argv) {
  if (argc < 2)
    return -1;
  int n = stoi(argv[1]);
  printf("parity %d;\n", 2 * n);
  for (int i = 1; i < 2 * n; ++i) {
    printf("%d %d 1 %d", i, i, i + 1);
    if (i & 1)
      printf(";\n");
    else
      printf(",1;\n");
  }
  printf("%d %d 1 1;\n", 2 * n, 2 * n);
}
