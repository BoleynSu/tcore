// Copyright 2016 Boleyn Su

#include <sys/types.h>
#include <algorithm>
#include <cassert>
#include <functional>
#include <iostream>
#include <iterator>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <utility>
#include <vector>

using namespace std;

typedef int64_t i64;

struct graph {
  struct ds_t {
    i64 val;
    vector<pair<i64, i64>> st;
    ds_t() : val(), st() {}
  };
  // input parameters
  i64 theta, k, tau;
  // input data
  i64 V, E;
  vector<vector<pair<pair<i64, i64>, pair<i64, i64>>>> neighbors;
  // output data
  vector<ds_t> ds;
  vector<vector<i64>> ans;
  graph(istream& cin) : theta(), k(), tau(), V(), E(), neighbors(), ans() {
    cin >> theta >> k >> tau;
    cin >> V >> E;
    neighbors.resize(V);
    for (i64 i = 0, last_t = numeric_limits<i64>::min(); i < E; ++i) {
      i64 u, v, t;
      cin >> u >> v >> t;
      assert(u != v);
      assert(last_t <= t);
      i64 bu = neighbors[u].size(), bv = neighbors[v].size();
      neighbors[u].emplace_back(make_pair(v, bv), make_pair(t, t + theta));
      neighbors[v].emplace_back(make_pair(u, bu), make_pair(t, t + theta));
      last_t = t;
    }
  }
  // NOTE: O(V+theta E)
  void theta_stable_k_degree_nodes_with_stability_no_less_than_tau() {
    // NOTE: some magic
    vector<i64> last(V);
    vector<vector<bool>> ignore(V);
    for (i64 u = 0; u < V; u++) {
      ignore[u].resize(neighbors[u].size());
      for (i64 i = 0; i < (i64)neighbors[u].size(); i++) {
        auto& n = neighbors[u][i];
        i64 j = last[n.first.first];
        if (j < i && neighbors[u][j].first.first == n.first.first) {
          if (neighbors[u][j].second.second > n.second.first) {
            neighbors[u][j].second.second = n.second.first;
            ignore[u][i] = true;
          }
        }
        last[n.first.first] = i;
      }
    }
    queue<i64> q;
    for (i64 u = 0; u < V; u++) {
      if (neighbors[u].size() == 0) {
        ds[u].val = 0;
      } else {
        // TODO: check with a threshold
        for (i64 i = 0, j = 0;
             i < (i64)neighbors[u].size() || j < (i64)neighbors[u].size();) {
          if (i < (i64)neighbors[u].size()) {
            if (j < (i64)neighbors[u].size()) {
              if (neighbors[u][i].second.first <
                  neighbors[u][j].second.second) {
                ds[u].st.emplace_back(neighbors[u][i].second.first, i);
                i++;
              } else {
                if (neighbors[u][j].second.second ==
                    neighbors[u][j].second.first + theta) {
                  ds[u].st.emplace_back(neighbors[u][j].second.second, -1);
                }
                j++;
              }
            } else {
              ds[u].st.emplace_back(neighbors[u][i].second.first, i);
              i++;
            }
          } else {
            if (neighbors[u][j].second.second ==
                neighbors[u][j].second.first + theta) {
              ds[u].st.emplace_back(neighbors[u][j].second.second, -1);
            }
            j++;
          }
        }
        i64 ns = 0;
        for (i64 i = 0, pre = 0; i < (i64)ds[u].st.size(); i++) {
          if (ns > 0 && ds[u].st[ns - 1].first == ds[u].st[i].first) {
            if (ds[u].st[i].second == -1) {
              pre--;
            } else {
              neighbors[u][ds[u].st[i].second].second.first = ns - 1;
              if (!ignore[u][ds[u].st[i].second]) {
                pre++;
              }
            }
            ds[u].st[ns - 1].second = pre;
          } else {
            ns++;
            if (ds[u].st[i].second == -1) {
              pre--;
            } else {
              neighbors[u][ds[u].st[i].second].second.first = ns - 1;
              if (!ignore[u][ds[u].st[i].second]) {
                pre++;
              }
            }
            ds[u].st[ns - 1].first = ds[u].st[i].first;
            ds[u].st[ns - 1].second = pre;
          }
        }
        ds[u].st.resize(ns);
        for (i64 i = 0; i < ns - 1; i++) {
          if (ds[u].st[i].second >= k) {
            ds[u].val += ds[u].st[i + 1].first - ds[u].st[i].first;
          }
        }
      }
      //            cout << u << ":" << ds[u].val << endl;
      //            for (i64 i = 0; i < (i64)ds[u].st.size(); i++) {
      //              cout << ds[u].st[i].first << "," << ds[u].st[i].second <<
      //              endl;
      //            }
      if (ds[u].val < tau) {
        q.emplace(u);
        //        cout << "push " << u << endl;
      }
    }
    while (!q.empty()) {
      i64 u = q.front();
      //                  cout << "pop " << u << endl;
      for (auto& n : neighbors[u]) {
        i64 v = n.first.first;
        i64 it = neighbors[v][n.first.second].second.first;
        // NOTE: O(theta)
        while (ds[v].st[it].first < n.second.second) {
          ds[v].st[it].second--;
          if (ds[v].st[it].second + 1 >= k && ds[v].st[it].second < k) {
            i64 delta = ds[v].st[it + 1].first - ds[v].st[it].first;
            ds[v].val -= delta;
            if (ds[v].val + delta >= tau && ds[v].val < tau) {
              q.emplace(v);
            }
          }
          it++;
        }
      }
      q.pop();
    }
  }
  i64 stability(const vector<i64>& comp, vector<ds_t>& ds, vector<bool>& in) {
    vector<map<i64, set<i64>>> st(V);
    for (i64 i = 0; i < comp.size(); i++) {
      i64 u = comp[i];
      for (auto& n : neighbors[u]) {
        i64 v = n.first.first;
        if (in[v]) {
          i64 it = neighbors[v][n.first.second].second.first;
          i64 b = ds[v].st[it].first;
          for (i64 i = 0; i < theta; i++) {
            st[u][b + i].insert(v);
          }
        }
      }
    }
    i64 cnt = 0;
    for (i64 t = 1921; t <= 2020; t++) {
      i64 delta = 1;
      for (i64 u : comp) {
        if (st[u][t].size() < k) {
          delta = 0;
        }
      }
      cnt += delta;
    }
    return cnt;
  }
  void branch_and_bound(const vector<i64>& comp, vector<ds_t>& ds,
                        vector<bool>& in, vector<bool>& selected) {
    if (ans.back().size() > comp.size()) {
      return;
    }
    if (stability(comp, ds, in) >= tau) {
      ans.emplace_back(comp);
    } else {
      vector<i64> comp1, comp2;
    }
  }
  void solve() {
    ds.resize(V);
    ans.emplace_back();
    theta_stable_k_degree_nodes_with_stability_no_less_than_tau();
    vector<bool> visited(V), selected(V);
    for (i64 u = 0; u < V; u++) {
      if (ds[u].val >= tau && !visited[u]) {
        vector<i64> comp;
        i64 qh = 0;
        comp.emplace_back(u);
        visited[u] = true;
        while (qh < (i64)comp.size()) {
          i64 u = comp[qh];
          qh++;
          for (auto& n : neighbors[u]) {
            i64 v = n.first.first;
            // NOTE: important
            if (!visited[v] && ds[v].val >= tau &&
                ds[u].st[n.second.first].second >= k) {
              comp.emplace_back(v);
              visited[v] = true;
            }
          }
        }
        cout << comp.size() << endl;
        for (i64 u : comp) {
          cout << u << endl;
        }
        branch_and_bound(comp, ds, visited, selected);
        comp.clear();
      }
      //      cout << u << " " << ds_t[u].val << endl;
    }
  }
};

int main() {
  graph G(cin);
  G.solve();
  return 0;
}
