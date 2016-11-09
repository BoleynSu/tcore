// Copyright 2016 Boleyn Su

#include <sys/time.h>
#include <sys/types.h>
#include <algorithm>
#include <cassert>
#include <fstream>
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
  // helper data
  vector<bool> visited, is_selected, &in_comp;
  // testing data
  timeval start_at, end_at;
  graph(istream& in, i64 theta, i64 k, i64 tau)
      : theta(theta),
        k(k),
        tau(tau),
        V(),
        E(),
        neighbors(),
        ans(),
        visited(),
        is_selected(),
        in_comp(visited),
        start_at(),
        end_at() {
    gettimeofday(&start_at, 0);
    in >> V >> E;
    neighbors.resize(V);
    for (i64 i = 0, last_t = 0; i < E; ++i) {
      i64 u, v, t;
      in >> u >> v >> t;
      assert(u != v);
      assert(last_t <= t);
      i64 bu = neighbors[u].size(), bv = neighbors[v].size();
      neighbors[u].emplace_back(make_pair(v, bv), make_pair(t, t + theta));
      neighbors[v].emplace_back(make_pair(u, bu), make_pair(t, t + theta));
      last_t = t;
    }
    gettimeofday(&end_at, 0);
    cout << "reading time: "
         << (end_at.tv_sec - start_at.tv_sec) * 1000 +
                (end_at.tv_usec - start_at.tv_usec) / 1000
         << "ms" << endl;
  }
  // NOTE: O(V+theta E)
  void theta_stable_k_degree_nodes_with_stability_no_less_than_tau() {
    gettimeofday(&start_at, 0);
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
      if (ds[u].val < tau - theta) {
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
            if (ds[v].val + delta >= tau - theta && ds[v].val < tau - theta) {
              q.emplace(v);
            }
          }
          it++;
        }
      }
      q.pop();
    }
    gettimeofday(&end_at, 0);
    cout << "preprocessing time: "
         << (end_at.tv_sec - start_at.tv_sec) * 1000 +
                (end_at.tv_usec - start_at.tv_usec) / 1000
         << "ms" << endl;
  }
  pair<i64, i64> stability(const vector<i64>& comp, i64 selected) {
    vector<pair<i64, i64>> st;
    st.push_back(make_pair(0, numeric_limits<i64>::max()));
    i64 len = numeric_limits<i64>::max(),
        selected_len = numeric_limits<i64>::max();
    for (i64 i = 0; i < (i64)comp.size(); i++) {
      i64 u = comp[i];
      vector<pair<i64, i64>> nst;
      i64 nlen = 0;
      auto it = st.begin();
      for (i64 j = 0; j < (i64)ds[u].st.size(); j++) {
        if (ds[u].st[j].second >= k) {
          // [ds[u].st[j].first, ds[u].st[j + 1].first);
          while (it != st.end() && it->second <= ds[u].st[j].first) {
            it++;
          }
          while (it != st.end() && it->second <= ds[u].st[j + 1].first) {
            pair<i64, i64> range(max(it->first, ds[u].st[j].first), it->second);
            if (range.first < range.second) {
              nst.push_back(range);
              nlen += range.second - range.first;
            }
            it++;
          }
          if (it != st.end() && it->first < ds[u].st[j + 1].first) {
            pair<i64, i64> range(max(it->first, ds[u].st[j].first),
                                 ds[u].st[j + 1].first);
            if (range.first < range.second) {
              nst.push_back(range);
              nlen += range.second - range.first;
            }
          }
        }
      }
      st.swap(nst);
      len = nlen;
      if (i < selected) {
        selected_len = len;
      }
      if (len < tau - theta) {
        break;
      }
    }
    return make_pair(len, selected_len);
  }
  bool remove_node(i64 u, queue<i64>& q) {
    bool removable = true;
    for (auto& n : neighbors[u]) {
      i64 v = n.first.first;
      if (in_comp[v]) {
        i64 it = neighbors[v][n.first.second].second.first;
        while (ds[v].st[it].first < n.second.second) {
          ds[v].st[it].second--;
          if (ds[v].st[it].second + 1 >= k && ds[v].st[it].second < k) {
            i64 delta = ds[v].st[it + 1].first - ds[v].st[it].first;
            ds[v].val -= delta;
            if (ds[v].val + delta >= tau - theta && ds[v].val < tau - theta) {
              q.emplace(v);
              if (is_selected[v]) {
                removable = false;
              }
            }
          }
          it++;
        }
      }
    }
    return removable;
  }
  void add_node(i64 u) {
    for (auto& n : neighbors[u]) {
      i64 v = n.first.first;
      if (in_comp[v]) {
        i64 it = neighbors[v][n.first.second].second.first;
        while (ds[v].st[it].first < n.second.second) {
          ds[v].st[it].second++;
          if (ds[v].st[it].second >= k && ds[v].st[it].second - 1 < k) {
            i64 delta = ds[v].st[it + 1].first - ds[v].st[it].first;
            ds[v].val += delta;
          }
          it++;
        }
      }
    }
  }
  void branch_and_bound(const vector<i64>& comp, i64 selected) {
    if (ans.back().size() >= comp.size()) {
      return;
    }
    auto len = stability(comp, selected);
    if (len.first >= tau - theta) {
      ans.emplace_back(comp);
    } else if (len.second >= tau - theta && selected < (i64)comp.size()) {
      vector<i64> compd, comps;
      i64 u = comp[selected];
      // remove u
      {
        bool removable = true;
        vector<i64> removed;
        queue<i64> q;
        q.push(u);
        while (!q.empty()) {
          i64 u = q.front();
          removed.push_back(u);
          if (!remove_node(u, q)) {
            removable = false;
            break;
          }
          q.pop();
        }
        if (removable) {
          for (i64 u : removed) {
            assert(in_comp[u] && !is_selected[u]);
            in_comp[u] = false;
          }
          for (i64 u : comp) {
            if (in_comp[u]) {
              compd.push_back(u);
            }
          }
          branch_and_bound(compd, selected);
          for (i64 u : removed) {
            in_comp[u] = true;
          }
        }
        for (i64 u : removed) {
          add_node(u);
        }
      }
      // select u
      {
        is_selected[u] = true;
        selected++;

        bool selectable = true;
        vector<pair<i64, i64>> st;
        st.push_back(make_pair(0, numeric_limits<i64>::max()));
        i64 len = numeric_limits<i64>::max();
        for (i64 i = 0; i < selected; i++) {
          i64 u = comp[i];
          vector<pair<i64, i64>> nst;
          i64 nlen = 0;
          auto it = st.begin();
          for (i64 j = 0; j < (i64)ds[u].st.size(); j++) {
            if (ds[u].st[j].second >= k) {
              // [ds[u].st[j].first, ds[u].st[j + 1].first);
              while (it != st.end() && it->second <= ds[u].st[j].first) {
                it++;
              }
              while (it != st.end() && it->second <= ds[u].st[j + 1].first) {
                pair<i64, i64> range(max(it->first, ds[u].st[j].first),
                                     it->second);
                if (range.first < range.second) {
                  nst.push_back(range);
                  nlen += range.second - range.first;
                }
                it++;
              }
              if (it != st.end() && it->first < ds[u].st[j + 1].first) {
                pair<i64, i64> range(max(it->first, ds[u].st[j].first),
                                     ds[u].st[j + 1].first);
                if (range.first < range.second) {
                  nst.push_back(range);
                  nlen += range.second - range.first;
                }
              }
            }
          }
          st.swap(nst);
          len = nlen;
          if (len < tau - theta) {
            selectable = false;
            break;
          }
        }
        if (selectable) {
          bool removable = true;
          vector<i64> removed;
          queue<i64> q;
          for (i64 i = selected; i < (i64)comp.size(); i++) {
            i64 u = comp[i];
            vector<pair<i64, i64>> nst;
            i64 nlen = 0;
            auto it = st.begin();
            for (i64 j = 0; j < (i64)ds[u].st.size(); j++) {
              if (ds[u].st[j].second >= k) {
                // [ds[u].st[j].first, ds[u].st[j + 1].first);
                while (it != st.end() && it->second <= ds[u].st[j].first) {
                  it++;
                }
                while (it != st.end() && it->second <= ds[u].st[j + 1].first) {
                  pair<i64, i64> range(max(it->first, ds[u].st[j].first),
                                       it->second);
                  if (range.first < range.second) {
                    nst.push_back(range);
                    nlen += range.second - range.first;
                  }
                  it++;
                }
                if (it != st.end() && it->first < ds[u].st[j + 1].first) {
                  pair<i64, i64> range(max(it->first, ds[u].st[j].first),
                                       ds[u].st[j + 1].first);
                  if (range.first < range.second) {
                    nst.push_back(range);
                    nlen += range.second - range.first;
                  }
                }
              }
            }
            if (nlen < tau - theta) {
              q.push(u);
            }
          }
          while (!q.empty()) {
            i64 u = q.front();
            removed.push_back(u);
            if (!remove_node(u, q)) {
              removable = false;
              break;
            }
            q.pop();
          }
          if (removable) {
            for (i64 u : removed) {
              assert(in_comp[u] && !is_selected[u]);
              in_comp[u] = false;
            }
            for (i64 u : comp) {
              if (in_comp[u]) {
                comps.push_back(u);
              }
            }
            branch_and_bound(comps, selected);
            for (i64 u : removed) {
              in_comp[u] = true;
            }
          }
          for (i64 u : removed) {
            add_node(u);
          }
        }
        selected--;
        is_selected[u] = false;
      }
    }
  }
  void solve() {
    ds.resize(V);
    theta_stable_k_degree_nodes_with_stability_no_less_than_tau();
    visited.resize(V);
    is_selected.resize(V);
    ans.emplace_back();
    gettimeofday(&start_at, 0);
    for (i64 u = 0; u < V; u++) {
      if (ds[u].val >= tau - theta && !visited[u]) {
        vector<i64> comp;
        i64 qh = 0;
        comp.emplace_back(u);
        visited[u] = true;
        while (qh < (i64)comp.size()) {
          i64 u = comp[qh];
          qh++;
          for (auto& n : neighbors[u]) {
            i64 v = n.first.first;
            if (!visited[v] && ds[v].val >= tau - theta) {
              comp.emplace_back(v);
              visited[v] = true;
            }
          }
        }
        branch_and_bound(comp, 0);
        comp.clear();
      }
    }
    cout << ans.back().size() << endl;
    for (i64 u : ans.back()) {
      cout << u << endl;
    }
    gettimeofday(&end_at, 0);
    cout << "searching time: "
         << (end_at.tv_sec - start_at.tv_sec) * 1000 +
                (end_at.tv_usec - start_at.tv_usec) / 1000
         << "ms" << endl;
  }
};

int main(int argc, char* argv[]) {
  ifstream in(argv[1]);
  i64 theta = atoi(argv[2]);
  i64 k = atoi(argv[3]);
  i64 tau = atoi(argv[4]);
  graph G(in, theta, k, tau);
  G.solve();
  return 0;
}
