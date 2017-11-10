#include <cstdio>

char neighbours[32768];

int main() {
  int n;
  scanf("parity %d;", &n);
  printf("parity %d;\n", n);
  for (int i = 0, node, colour, owner; i < n; ++i) {
    scanf("%d %d %d %[0-9,]", &node, &colour, &owner, neighbours);
    scanf("%*[^;]");
    scanf(" ;");
    printf("%d %d %d %s;\n", node, colour + 1, owner ^ 1, neighbours);
  }
  return 0;
}
