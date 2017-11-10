#include <iostream>
#include <iomanip>

using std::cout;
using std::stoi;

int main(int argc, const char ** argv) {
  if (argc < 2)
    return -1;
  int n = stoi(argv[1]);
  cout << "parity " << 2 * n + 2 << ";\n"
       << "0 0 0 0 \"u0\";\n"
       << "1 1 1 1 \"u1\";\n"
       << "2 2 0 0," << n + 2 << " \"v1\";\n"
       << n + 2 << " 2 1 2,1 \"v" << n + 1 << "\";\n";
  for (int i = 2; i <= n; ++i) {
    cout << i + 1 << ' ' << i + 1 << " 0 " << i << ',' << n + i + 1 << " \"v"
         << i << "\";\n";
    cout << n + i + 1 << ' ' << i + 1 << " 1 " << i + 1 << ',' << n + i
         << " \"v" << n + i << "\";\n";
  }
  return 0;
}
