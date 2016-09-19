// Copyright 2016 Boleyn Su

#include <sys/types.h>
#include <algorithm>
#include <iostream>
#include <iterator>
#include <queue>
#include <utility>
#include <vector>

using namespace std;

typedef int64_t i64;

struct graph {
  // input data
  i64 V, E;
  vector<vector<pair<i64, i64>>> neighbors;
  // input parameters
  i64 theta, k, tau;
  // shared output data
  vector<i64> filtered;
  void read(istream& cin) {
    cin >> V >> E;
    neighbors.resize(V);
    for (i64 i = 0; i < E; ++i) {
      i64 u, v, t;
      cin >> u >> v >> t;
      neighbors[u].emplace_back(v, t);
      neighbors[v].emplace_back(u, t);
    }
    cin >> theta >> k >> tau;
    filtered.resize(V);
  }
  // NOTE: O(V+ElogE+theta E)
  // TODO: improve it to O(V+theta E) if the input is ordered
  void theta_stable_k_degree_with_stability_no_less_than_tau() {
    struct ds {
      i64 val;
      vector<pair<i64, i64>> st;
      ds() : val(), st() {}
    };
    vector<ds> ds(V);
    queue<i64> q;
    for (i64 u = 0; u < V; u++) {
      for (auto& n : neighbors[u]) {
        ds[u].st.emplace_back(n.second, 1);
        // TODO: check with a threshold
        ds[u].st.emplace_back(n.second + theta, -1);
      }
      // NOTE: O(ElogE)
      sort(ds[u].st.begin(), ds[u].st.end());
      i64 ns = 1;
      for (i64 i = 1; i < (i64)ds[u].st.size(); i++) {
        if (ds[u].st[ns - 1].first == ds[u].st[i].first) {
          ds[u].st[ns - 1].second += ds[u].st[i].second;
        } else {
          ds[u].st[ns] = ds[u].st[i];
          ds[u].st[ns].second += ds[u].st[ns - 1].second;
          ns++;
        }
      }
      ds[u].st.resize(ns);
      for (i64 i = 0; i < ns - 1; i++) {
        if (ds[u].st[i].second >= k) {
          ds[u].val += ds[u].st[i + 1].first - ds[u].st[i].first;
        }
      }
      //      cout << u << ":" << ds[u].val << endl;
      //      for (i64 i = 0; i < ns; i++) {
      //        cout << ds[u].st[i].first << "," << ds[u].st[i].second << endl;
      //      }
      if (ds[u].val < tau) {
        q.emplace(u);
        //        cout << "push " << u << endl;
      }
    }
    while (!q.empty()) {
      i64 u = q.front();
      //      cout << "pop " << u << endl;
      for (auto& n : neighbors[u]) {
        i64 v = n.first;
        i64 t = n.second;
        // NOTE: O(logE)
        auto it =
            lower_bound(ds[v].st.begin(), ds[v].st.end(), make_pair(t, (i64)0));
        // NOTE: O(theta)
        while (it->first < t + theta) {
          it->second--;
          if (it->second + 1 >= k && it->second < k) {
            i64 delta = 0;
            delta -= it->first;
            it++;
            delta += it->first;
            ds[v].val -= delta;
            if (ds[v].val + delta >= tau && ds[v].val < tau) {
              q.emplace(v);
            }
          } else {
            it++;
          }
        }
      }
      q.pop();
    }
    for (i64 u = 0; u < V; u++) {
      if (ds[u].val < tau) {
        filtered[u] = true;
      }
      //      cout << ds[u].val << endl;
    }
  }
  void k_core() {
    vector<vector<i64>> nn(V);
    vector<i64> deg(V), cnt(V), pos(V);
    for (i64 u = 0; u < V; u++) {
      for (auto& n : neighbors[u]) {
        nn[u].emplace_back(n.first);
      }
      sort(nn[u].begin(), nn[u].end());
      nn[u].erase(unique(nn[u].begin(), nn[u].end()), nn[u].end());
      deg[u] = nn[u].size();
      cnt[deg[u]]++;
    }
    vector<i64> q(V);
    for (i64 i = 1; i < V; i++) {
      cnt[i] += cnt[i - 1];
    }
    for (i64 u = 0; u < V; u++) {
      cnt[deg[u]]--;
      q[cnt[deg[u]]] = u;
      pos[u] = cnt[deg[u]];
    }
    // deg[u] = nn[u].size()
    // cnt[x] = | { u | deg[u] < x } |
    // q[pos[u]] = u
    for (i64 qh = 0; qh < (i64)q.size(); qh++) {
      i64 u = q[qh];
      cnt[deg[u]]++;
      for (i64 v : nn[u]) {
        if (deg[v] > deg[u]) {
          i64 a = cnt[deg[v]], b = pos[v];
          swap(q[a], q[b]);
          pos[q[a]] = a;
          pos[q[b]] = b;
          cnt[deg[v]]++;
          deg[v]--;
        }
      }
      if (deg[u] < k) {
        filtered[u] = true;
      }
      //      cout << u << " " << deg[u] << endl;
    }
  }
} G;

int main() {
  G.read(cin);
  G.theta_stable_k_degree_with_stability_no_less_than_tau();
  G.k_core();
  // TODO: theta_stable_k_degree_with_stability_no_less_than_tau and k_core can
  // help each other
  for (i64 u = 0; u < G.V; u++) {
    if (!G.filtered[u]) {
      cout << u << endl;
    }
  }
  return 0;
}
