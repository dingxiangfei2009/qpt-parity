#include <limits.h>
#include <cstdio>
#include <iterator>
#include <iostream>
#include <iomanip>
#include <queue>
#include <vector>
#include <stack>
#include <map>
#include <set>
#include <tuple>
#include <variant>
#include <algorithm>
#include <sstream>
#include <string>

using std::variant;
using std::holds_alternative;
using std::get;

using std::vector;
using std::stack;
using std::queue;
using std::tuple;
using std::map;
using std::set;
using std::multiset;
using std::ignore;
using std::tie;

using std::string;
using std::stringstream;

using std::copy;
using std::fill;
using std::find;
using std::transform;
using std::min;
using std::max;
using std::min_element;
using std::max_element;
using std::move;

using std::back_inserter;

using std::ostream_iterator;
using std::endl;
using std::cout;

int integerLog2(int n) {
  int r = 0;
  for (; n > 1; n >>= 1)
    ++r;
  return r;
}

char neighbours[32768];

template<typename Out>
void split(const char * str, char delim, Out o) {
  stringstream ss(str);
  string s;
  while (std::getline(ss, s, delim)) {
    *(o++) = atoi(s.c_str());
  }
}

constexpr inline int encodeColour(int raw) {
  return raw & 1 ? -raw-1 : raw+1;
}

constexpr inline int decodeColour(int en) {
  if (en < 0)
    return -en-1;
  else if (en > 0)
    return en-1;
  else
    return -1;
}

typedef vector<int> Witness;

/* both d and b are encoded colours */
int findUpdateByConcatenation(const Witness &b, int d) {
  for (int i = 0, e = b.size(); i < e; ++i)
    if (b[i] <= 0) { // empty or odd
      for (int j = i + 1; j < e; ++j)
        if (b[j]) { // non-empty
          if (abs(b[j]) < abs(d))
            return -1;
          else
            return i;
        }
      // all empty
      return i;
    }
  return b.size() - 1; // update at the last element
}

/* both d and b are encoded colours */
int findUpdateBySubstitution(const Witness &b, int d) {
  int last = 0;
  for (int i = b.size() - 1; i >= 0; --i)
    if (b[i]) {
      if (abs(b[i]) < abs(d))
        if (!last || abs(d) <= abs(last))
          return i;
      last = b[i];
    }
  return -1;
}

Witness setAndClearLower(const Witness &b, int pos, int d) {
  Witness b_ = b;
  fill(b_.begin(), b_.begin() + pos, 0);
  b_[pos] = d;
  return b_;
}

/* both d and b are encoded colours */
Witness basicUpdate(const Witness &b, int d) {
  int sub = findUpdateBySubstitution(b, d);
  int cat = findUpdateByConcatenation(b, d);
  int best = max(sub, cat);
  return best < 0 ? b : setAndClearLower(b, best, d);
}

typedef multiset<int> ColourSet;

/*
  bs are encoded colours
  Suppose cset is not empty.
*/
#ifndef BAD_UPDATE
Witness
immediateSuccessor(const ColourSet &cset, const Witness &b) {
  for (int i = 1, e = b.size(), limit, next; i < e; ++i) {
    limit = 0;
    for (int j = i + 1; j < e; ++j)
      if (b[j]) {
        limit = abs(b[j]);
        break;
      }
    if (!b[i]) {
      if (limit) {
        auto next_itr = cset.lower_bound(-limit);
        if (next_itr == cset.end()) {
          while (++i < e && !b[i]) ;
          --i;
          continue;
        }
        return setAndClearLower(b, i, *next_itr);
      } else {
        return setAndClearLower(b, i, *cset.begin());
      }
    } else {
      auto next_itr = cset.lower_bound(b[i] + 1);
      if (next_itr == cset.end())
        continue;
      next = *next_itr;
      if (limit && limit < abs(next))
        continue;
      // next > 0
      return setAndClearLower(b, i, next);
    }
  }
  return b;
}

Witness
substituteSuccessor(const ColourSet &cset, const Witness &b, int d) {
  if (d > 0)
    return b;

  int i;
  for (i = b.size() - 1; i >= 0; --i)
    if (b[i] == d)
      break;
  if (i < 0)
    return b;

  auto next_odd = cset.lower_bound(d+1);
  if (next_odd == cset.end())
    return b;
  int o = *next_odd;
  if (o > 0)
    o = d;

  auto greatest = cset.lower_bound(-o-1);
  if (greatest == cset.end())
    return b;
  if (greatest != cset.begin() && abs(*greatest) > abs(o))
    --greatest;
  int e = *greatest;
  if (o == d && e < 0 || abs(e) > abs(o))
    return b;

  Witness b_ = b;
  for (int j = 0; j < i; ++j)
    b_[j] = e;
  b_[i] = o;
  return b_;
}
#else
// NOTE: This is a wrong update rule. For comparison only.
Witness
immediateSuccessor(const ColourSet &cset, const Witness &b) {
  for (int i = 1, e = b.size(); i < e; ++i)
    if (b[i]) {
      auto next_itr = cset.lower_bound(b[i] + 1);
      if (next_itr == cset.end())
        return b;
      int next = *next_itr;
      if (next < 0)
        return setAndClearLower(b, i, next);
      // next > 0
      if (i + 1 < e && abs(b[i + 1]) >= next)
        return setAndClearLower(b, i, next);
    }
  return b;
}
#endif

/*
  Suppose |a| ≣ |b| and i ∈ ℕ.
  compareWitness(a,b) ≣ -(i+1) iff a ⊑ b and a[i] ≺ b[i] for largest i
  compareWitness(a,b) ≣ 0 iff a = b
  compareWitness(a,b) ≣ i+1 iff a ⊒ b and a[i] ≻ b[i] for largest i
*/
int compareWitness(const Witness &a, const Witness &b) {
  for (int i = a.size() - 1; i >= 0; --i)
    if (a[i] != b[i]) {
      if (!a[i])
        return -i - 1;
      else if (!b[i])
        return i + 1;
      else if (a[i] > b[i])
        return i + 1;
      else
        return -i - 1;
    }
  return 0;
}

bool compareWitnessLT(const Witness &a, const Witness &b) {
  return compareWitness(a, b) < 0;
}

/* both d and b are encoded colours */
#ifndef BAD_UPDATE
Witness
antagonistUpdate(const ColourSet &cset, const Witness &b, int d) {
  auto Scat = immediateSuccessor(cset, b);
  return
    min({
          basicUpdate(b, d),
          basicUpdate(Scat, d),
          basicUpdate(substituteSuccessor(cset, b, d), d),
          basicUpdate(substituteSuccessor(cset, Scat, d), d)},
      compareWitnessLT);
}
#else
Witness
antagonistUpdate(const ColourSet &cset, const Witness &b, int d) {
  return min(
             basicUpdate(b, d),
             basicUpdate(immediateSuccessor(cset, b), d),
             compareWitnessLT);
}
#endif

enum Fate {
  Won, Lost
};

typedef variant<Fate, Witness> Status;

bool isDecided(const Status &a) {
  return holds_alternative<Fate>(a);
}

int compareStatus(const Status &a_, const Status &b_) {
  int winA, winB;
  winA = isDecided(a_) ? (get<Fate>(a_) == Won) - (get<Fate>(a_) == Lost) : 0;
  winB = isDecided(b_) ? (get<Fate>(b_) == Won) - (get<Fate>(b_) == Lost) : 0;
  if (winA || winB)
    return winA - winB;
  else
    return compareWitness(get<vector<int>>(a_), get<vector<int>>(b_));
}

bool compareStatusLT(const Status &a, const Status &b) {
  return compareStatus(a, b) < 0;
}

struct Vertex {
  int colour, owner;
  vector<int> successors, predecessors;
};

string printStatus(const Status &a_) {
  if (isDecided(a_))
    if (get<Fate>(a_) == Won)
      return "Won";
    else
      return "Lost";
  const vector<int> &a = get<vector<int>>(a_);
  stringstream ss;
  for (auto itr = a.begin(), end = a.end(); itr != end; ++itr) {
    ss << ' ';
    if (*itr)
      ss << decodeColour(*itr);
    else
      ss << '_';
  }
  return ss.str();
}

string printGraphStatus(const map<int, Status> &a) {
  stringstream ss;
  for (auto &p : a) {
    ss << p.first << " :" << printStatus(p.second) << endl;
  }
  return ss.str();
}

inline int witnessValue(const vector<int> &a) {
  int c;
  for (int i = c = 0, j = 1, e = a.size(); i < e; ++i, j <<= 1)
    if (a[i] > 0)
      c += j;
  return c;
}

typedef map<int, Vertex> Graph;

vector<set<int>> scc(const Graph &G, int start, int &time, map<int, int> &low, map<int, int> &disc) {
  // explicit stack scc
  struct StackItem {
    int state;
    int v;
    decltype(G.at(start).successors.begin()) i;
  };
  stack<StackItem> stack_;
  stack<int> S;
  set<int> on_stack;
  vector<set<int>> sccs;
  stack_.push({0, start});
  while (!stack_.empty()) {
    auto& _STATE_ = stack_.top();
    switch (_STATE_.state) {
    case 0:
      low[_STATE_.v] = disc[_STATE_.v] = time++;
      S.push(_STATE_.v);
      on_stack.insert(_STATE_.v);

      _STATE_.i = G.at(_STATE_.v).successors.begin();
    LC1:
      if (_STATE_.i == G.at(_STATE_.v).successors.end())
        goto LC2;
      if (disc.find(*_STATE_.i) == disc.end()) {
        stack_.push({0, *_STATE_.i});
        _STATE_.state = 1;
        continue;
      STATE_1:
        low[_STATE_.v] = min(low[_STATE_.v], low[*_STATE_.i]);
      } else if (on_stack.count(*_STATE_.i)) {
        low[_STATE_.v] = min(low[_STATE_.v], disc[*_STATE_.i]);
      }
      ++_STATE_.i;
      goto LC1;
    LC2:
      if (low[_STATE_.v] == disc[_STATE_.v]) {
        set<int> scc_;
        int u;
        do {
          u = S.top();
          S.pop();
          on_stack.erase(u);
          scc_.insert(u);
        } while (u != _STATE_.v);
        sccs.push_back(move(scc_));
      }
      stack_.pop();
      continue;
    case 1:
      goto STATE_1;
    }
  }
  return sccs;
}

/* list of scc by topological order */
vector<set<int>> decomposeScc(const Graph &G) {
  map<int, int> low, disc;
  set<int> solved;
  vector<set<int>> sccs;
  int time = 0;
  for (const auto& p : G) {
    int u = p.first;
    if (solved.find(u) == solved.end()) {
      auto result = scc(G, u, time, low, disc);
      for (const auto& s : result)
        solved.insert(s.begin(), s.end());
      copy(result.begin(), result.end(), back_inserter(sccs));
    }
  }
  return sccs;
}

Graph subGraph(const Graph &G, const set<int> &nodes) {
  Graph G_;
  for (auto u : nodes) {
    Vertex node_u = G.at(u);
    auto predecessors = node_u.predecessors;
    auto successors = node_u.successors;
    node_u.predecessors.clear();
    node_u.successors.clear();
    copy_if(
            predecessors.begin(),
            predecessors.end(),
            back_inserter(node_u.predecessors),
            [&](int u){return nodes.count(u);} );
    copy_if(
            successors.begin(),
            successors.end(),
            back_inserter(node_u.successors),
            [&](int u){return nodes.count(u);} );
    G_[u] = node_u;
  }
  return G_;
}

set<int>
vertices(const Graph &G) {
  set<int> nodes;
  for (const auto &p : G) {
    int node;
    tie(node, ignore) = p;
    nodes.insert(node);
  }
  return nodes;
}

set<int> attractorSet(const Graph &G, const set<int> &nodes, int owner) {
  map<int, int> succCount;
  for (auto &p : G) {
    succCount[p.first] = p.second.successors.size();
  }
  auto attr = nodes;
  queue<int> Q;
  for (int v : nodes) {
    succCount[v] = 0;
    Q.push(v);
  }
  while (!Q.empty()) {
    int v = Q.front();
    Q.pop();
    if (G.find(v) == G.end()) continue;
    for (int u : G.at(v).predecessors)
      if (succCount[u]) {
        if (G.at(u).owner == owner) {
          succCount[u] = 0;
          attr.insert(u);
          Q.push(u);
        } else if (!--succCount[u]) {
          attr.insert(u);
          Q.push(u);
        }
      }
  }
  return attr;
}

tuple<set<int>, set<int>, Graph>
winningCycles(Graph G, const ColourSet &cset) {
  set<int> even, odd;
  int c = INT_MIN;
  set<int> nodes = vertices(G);
  auto bottom = cset.begin(), top = --cset.end();
  while (*top >= *bottom) {
    const int colour = abs(*top) < abs(*bottom) ? *bottom : *top;
    cout << colour << endl;
    const int owner = colour < 0;
    set<int> nodes_;
    copy_if(
            nodes.begin(),
            nodes.end(),
            inserter(nodes_, nodes_.begin()),
            [&] (int v) {
              return
                abs(G.at(v).colour) <= abs(colour) &&
                (G.at(v).successors.size() == 1 || G.at(v).owner == owner);
            });
    auto subG = subGraph(G, nodes_);
    auto sccs = decomposeScc(subG);
    set<int> won;
    for (const auto &scc : sccs) {
      if (scc.size() == 1) {
        int v = *scc.begin();
        if (find(G.at(v).successors.begin(), G.at(v).successors.end(), v) == G.at(v).successors.end())
          continue;
      }
      for (const auto &v : scc)
        if (G.at(v).colour == colour) {
          won.insert(v);
          break;
        }
    }
    auto attr = attractorSet(subG, won, owner);
    bool changed = !attr.empty();
    if (changed) {
      if (owner) {
        odd.insert(attr.begin(), attr.end());
        attr = attractorSet(G, odd, owner);
        odd.insert(attr.begin(), attr.end());
      } else {
        even.insert(attr.begin(), attr.end());
        attr = attractorSet(G, even, owner);
        even.insert(attr.begin(), attr.end());
      }
      nodes_ = move(nodes);
      set_difference(nodes_.begin(), nodes_.end(), attr.begin(), attr.end(), inserter(nodes, nodes.begin()));
      G = subGraph(G, nodes);
    }
    if (colour == *top) {
      top = cset.lower_bound(*top);
      if (top != cset.begin())
        --top;
    } else {
      bottom = cset.upper_bound(*bottom);
      if (bottom == cset.end())
        break;
    }
  }
  Graph G_ = subGraph(G, nodes);
  return tuple(even, odd, G_);
}

void removeOneColour(ColourSet &cset, int colour) {
  auto itr = cset.find(colour);
  if (itr == cset.end())
    return;
  cset.erase(itr);
}

map<int, Status> solve(Graph G_, int iterations) {
  Graph G = G_;
  ColourSet cset;
  for (const auto &p : G) {
    const int colour = p.second.colour;
    cset.insert(colour);
  }
  // remove winner controlled cycles
  set<int> evenWinning, oddWinning;
  #ifdef REMOVE_CYCLES
  tie(evenWinning, oddWinning, G) = winningCycles(G_, cset);
  cout << "Winning cycle reduction report:" << endl << "Winning:" << endl;
  for (int u : evenWinning) cout << ' ' << u;
  cout << endl << "Losing:" << endl;
  for (int u : oddWinning) cout << ' ' << u;
  cout << endl;
  // colour reduction
  for (int u : evenWinning) removeOneColour(cset, G_.at(u).colour);
  for (int u : oddWinning) removeOneColour(cset, G_.at(u).colour);
  #endif

  int evenColourCount = 0;
  for (const int colour : cset)
    evenColourCount += colour > 0;

  set<int> updating;
  map<int, Status> status;
  int witnessLength = integerLog2(evenColourCount) + 2;
  for (const auto &p : G) {
    int v = p.first;
    if (evenWinning.count(v))
      status[v] = Won;
    else if (oddWinning.count(v))
      status[v] = Lost;
    else {
      updating.insert(v);
      status[v] = Witness(witnessLength);
    }
  }

  evenWinning.clear();
  for (int ITR = 0; iterations < 0 || ITR < iterations; ++ITR) {
    cout << "\rIteration " << ITR << ", Updates " << updating.size() << "          ";
    if (updating.empty())
      return status; // fix-point reached
    set<int> updating_;
    map<int, Status> status_;
    bool decided = false;
    for (auto v : updating) {
      vector<Status> witnesses;
      transform(
                G.at(v).successors.begin(),
                G.at(v).successors.end(),
                back_inserter(witnesses),
                [&](int s){
                  if (isDecided(status[s]))
                    return status[s];
                  vector<int> next =
                    antagonistUpdate(
                                     cset,
                                     get<vector<int>>(status[s]),
                                     G.at(v).colour);
                  if (witnessValue(next) > evenColourCount)
                    return Status(Won);
                  else
                    return Status(next);
                });
      auto bestItr =
        G.at(v).owner ?
        min_element(witnesses.begin(), witnesses.end(), compareStatusLT) : // v ∈ V_o
        max_element(witnesses.begin(), witnesses.end(), compareStatusLT); // v ∈ V_e
      int bestIdx = bestItr - witnesses.begin();
      int comp = compareStatus(*bestItr, status[v]);
      if (comp <= 0)
        continue;
      status_[v] = *bestItr;
      if (isDecided(status_[v])) {
        decided = true;
        if (get<Fate>(status_[v]) == Won)
          evenWinning.insert(v);
      }
      for (auto p : G.at(v).predecessors)
        updating_.insert(p);
    }
    if (decided) {
      auto nodes_ = vertices(G);
      set<int> nodes;
      auto attr = attractorSet(G, evenWinning, 0);
      evenWinning.clear();
      cout << endl << "We have winners ";
      copy(attr.begin(), attr.end(), ostream_iterator<int>(cout, " "));
      cout << endl;
      for (int v : attr) {
        status_[v] = Won;
        for (auto p : G.at(v).predecessors)
          updating_.insert(p);
        const int colour = G.at(v).colour;
        evenColourCount -= colour > 0;
        removeOneColour(cset, colour);
      }
      set_difference(
                     nodes_.begin(),
                     nodes_.end(),
                     attr.begin(),
                     attr.end(),
                     inserter(nodes, nodes.begin()));
      G_ = G;
      G = subGraph(G_, nodes);
      updating.clear();
      set_difference(
                     updating_.begin(),
                     updating_.end(),
                     attr.begin(),
                     attr.end(),
                     inserter(updating, updating.begin()));
    } else
      updating = move(updating_);
    for (auto& itr : status_)
      status[itr.first] = itr.second;
  }
  return status;
}

int main(int argc, char **argv) {
  int ITR = argc > 1 ? atoi(argv[1]) : -1;
  const char *FILE = argc > 2 ? argv[2] : nullptr;
  int n;
  if (FILE) {
    freopen(FILE, "r", stdin);
  }
  scanf("parity %d;", &n);
  Graph V;
  set<int> colours;
  for (int i = 0; i < n; ++i) {
    int node, colour, owner;
    scanf("%d %d %d %[0-9,]", &node, &colour, &owner, neighbours);
    // Suppose 0 ≤ node < n, owner ∈ {0, 1}.
    V[node].owner = owner;
    V[node].colour = encodeColour(colour);
    split(neighbours, ',', back_inserter(V[node].successors));
    for (auto v : V[node].successors)
      V[v].predecessors.push_back(node);
    scanf("%*[^;]");
    scanf(" ;");
  }
  cout << "Solving " << (FILE ? FILE : "(stdin)") << endl;
  auto result = solve(V, ITR);
  cout << endl << printGraphStatus(result).c_str();
  return 0;
}
