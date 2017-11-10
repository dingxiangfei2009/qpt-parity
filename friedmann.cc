#include <cstdlib>
#include <cstdio>

int main(int argc, char **argv) {
  if (argc <= 1) return -1;
  int n = atoi(argv[1]);
  printf("parity %d;\n", 10 * n + 4);
  auto x = [](){return 0;};
  auto s = [](){return 1;};
  auto c = [](){return 2;};
  auto r = [](){return 3;};
  auto t = [=](int i){return i + 4 - 1;};
  auto a = [=](int i){return i + 2 * n + 4 - 1;};
  auto d = [=](int i){return i + 4 * n + 4 - 1;};
  auto e = [=](int i){return i + 5 * n + 4 - 1;};
  auto g = [=](int i){return i + 6 * n + 4 - 1;};
  auto k = [=](int i){return i + 7 * n + 4 - 1;};
  auto f = [=](int i){return i + 8 * n + 4 - 1;};
  auto h = [=](int i){return i + 9 * n + 4 - 1;};
  // x
  printf("%d 1 1 %d;\n", x(), x());
  // s
  printf("%d %d 0 %d", s(), 8 * n + 6, x());
  for (int j = 1; j <= n; ++j)
    printf(",%d", f(j));
  printf(";\n");
  // r
  printf("%d %d 0 %d", r(), 8 * n + 8, x());
  for (int j = 1; j <= n; ++j)
    printf(",%d", g(j));
  printf(";\n");
  // c
  printf("%d %d 0 %d,%d;\n", c(), 8 * n + 4, s(), r());
  // t
  printf("%d %d 0 %d,%d,%d;\n", t(1), 4 * n + 3, s(), r(), c());
  for (int i = 2; i <= 2 * n; ++i)
    printf("%d %d 0 %d,%d,%d;\n", t(i), 4 * n + 2 * i + 1, s(), r(), t(i - 1));
  // a
  for (int i = 1; i <= 2 * n; ++i)
    printf("%d %d 1 %d;\n", a(i), 4 * n + 2 * i + 2, t(i));
  // d
  for (int i = 1; i <= n; ++i) {
    printf("%d %d 0 %d,%d,%d", d(i), 4 * i + 1, s(), e(i), r());
    for (int j = 1; j < 2 * i + 1; ++j)
      printf(",%d", a(j));
    printf(";\n");
  }
  // e
  for (int i = 1; i <= n; ++i)
    printf("%d %d 1 %d,%d;\n", e(i), 4 * i + 2, d(i), h(i));
  // g
  for (int i = 1; i <= n; ++i)
    printf("%d %d 0 %d,%d;\n", g(i), 4 * i + 4, f(i), k(i));
  // k
  for (int i = 1; i <= n; ++i) {
    printf("%d %d 0 %d", k(i), 8 * n + 4 * i + 7, x());
    for (int j = i + 1; j <= n; ++j)
      printf(",%d", g(j));
    printf(";\n");
  }
  // f
  for (int i = 1; i <= n; ++i)
    printf("%d %d 1 %d;\n", f(i), 8 * n + 4 * i + 9, e(i));
  // h
  for (int i = 1; i <= n; ++i)
    printf("%d %d 1 %d;\n", h(i), 8 * n + 4 * i + 10, k(i));
  return 0;
}
