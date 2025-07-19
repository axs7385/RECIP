#include "Utility.h"
#include "LinearHeap.h"
#include "Timer.h"
#include "Graph.h"
// #include "ilp.h"
#include <map>
#include <ilcplex/ilocplex.h>
// #define NDEBUG
ILOSTLBEGIN
using namespace std;
ui n;  // number of nodes of the graph
ept m; // number of edges of the graph
ui K;  // the value of k in maximal k interdiction clique

ept *pstart; // offset of neighbors of nodes
ept *pend;
ui *edges; // adjacent ids of edges
clock_t bgt;
ept *pend_buf;
ui *tri_cnt;
ui *edges_pointer;
ui *Qe;
ui *degree;
int *dict;
int *deleted;
int LB = 0;
int ans;
int *ban;
inline void read(int &x)
{
    char c = getchar();
    while (c > '9' | c < '0')
    {
        if (c == 'c')
        {
            while (c != '\n')
                c = getchar();
        }
        c = getchar();
    }
    x = 0;
    while (c >= '0' && c <= '9')
    {
        x = x * 10 + c - '0';
        c = getchar();
    }
}
inline void read(unsigned &x)
{
    char c = getchar();
    while (c > '9' | c < '0')
    {
        if (c == 'c')
        {
            while (c != '\n')
                c = getchar();
        }
        c = getchar();
    }
    x = 0;
    while (c >= '0' && c <= '9')
    {
        x = x * 10 + c - '0';
        c = getchar();
    }
}
inline void read(ept &x)
{
    char c = getchar();
    while (c > '9' | c < '0')
    {
        if (c == 'c')
        {
            while (c != '\n')
                c = getchar();
        }
        c = getchar();
    }
    x = 0;
    while (c >= '0' && c <= '9')
    {
        x = x * 10 + c - '0';
        c = getchar();
    }
}
int *dedges;
int inn,inm;
void read_graph_std()
{
    read(n);
    read(m);
    inn=n,inm=m;
    m *= 2;
    printf("*\tn = %s; m = %s (undirected)\n", Utility::integer_to_string(n).c_str(), Utility::integer_to_string(m / 2).c_str());

    vector<pair<ui, ui>> vp;
    for (ui i = 0; i < m / 2; i++)
    {
        ui a, b;
        read(a);
        read(b);
        --a;
        --b;
        if (a >= n || b >= n)
        {
            printf("!!! Vertex IDs must be between 0 and n-1. Exit !!!\n");
            exit(0);
        }
        if (a==b)
            continue;
        vp.pb(mp(a, b));
        vp.pb(mp(b, a));
    }
    sort(vp.begin(), vp.end());
    // int oldsize=vp.size();
    vp.erase(unique(vp.begin(),vp.end()),vp.end());
    // cerr<<"!!!"<<oldsize<<' '<<vp.size()<<endl;
    if (pstart != nullptr)
        delete[] pstart;
    pstart = new ept[n + 1];
    if (pend != nullptr)
        delete[] pend;
    pend = new ept[n];
    if (degree != nullptr)
        delete[] degree;
    degree = new ui[n];
    if (edges != nullptr)
        delete[] edges;
    edges = new ui[m];
    if (dedges != nullptr)
        delete[] dedges;
    dedges = new int[m];
    pstart[0] = 0;
    ui idx = 0;
    for (ui i = 0; i < n; i++)
    {
        pstart[i + 1] = pstart[i];
        while (idx < vp.size() && vp[idx].first == i)
            edges[pstart[i + 1]++] = vp[idx++].second;
        pend[i] = pstart[i + 1];
        degree[i] = pend[i] - pstart[i];
    }
#ifndef NDEBUG
    printf("Finished reading graph\n");
#endif
}
void print_usage()
{
    printf("Usage: [1]exe [2]k [3]graph-dir [4 output]\n");
}
int *rk;
bool degcmp(int x, int y)
{
    // return pend[x] - pstart[x] > pend[y] - pstart[y];
    return degree[x] > degree[y];
}
bool iscon(ui u, ui w)
{
    int l = pstart[u], r = pstart[u + 1];
    if (l >= r)
        return 0;
    while (l + 1 < r)
    {
        int mid = l + (r - l) / 2;
        if (edges[mid] > w)
            r = mid;
        else
            l = mid;
    }
    return edges[l] == w;
}
int *used;
int *covered;
ui *out_mapping;
int fast_color()
{
    // if (rk != nullptr)
    //     delete[] rk;
    // rk = new int[n];
    if (rk == nullptr)
        rk = new int[n];
    for (int i = 0; i < n; ++i)
        rk[i] = i;
    sort(rk, rk + n, degcmp);
    /*
    O(n^2logn), useless
    vector<vector<int>> v;
    for (int i = 0; i < n; ++i)
    {
        int u = rk[i];
        bool b = false;
        for (int j = 0; j < v.size(); ++j)
        {
            bool bb = true;
            for (int w : v[j])
                bb &= iscon(u, w);
            if (bb)
            {
                v[j].push_back(u);
                b=true;
                break;
            }
        }
        if (!b)
        {
            vector<int> vv;
            vv.push_back(u);
            v.push_back(vv);
        }
    }
    */
    used = new int[n];
    for (int i = 0; i < n; ++i)
        used[i] = 0;
    covered = new int[n];
    for (int i = 0; i < n; ++i)
        covered[i] = 0;
    int tot = 0, cnt = 0, mxclq = 0;
    vector<int> clqs;
    for (int i = 0; i < n; ++i)
    {
        int u = rk[i];
        if (used[u])
            continue;
        // cerr<<"..."<<i<<' '<<n<<' '<<LB<<endl;
        ++tot;
        vector<int> v;
        v.clear();
        vector<int> theclique;
        theclique.push_back(u);
        ++cnt;
        int clq = 1;
        used[u] = 1;
        for (int j = pstart[u]; j < pend[u]; ++j)
        {
            int to = edges[j];
            if (used[to])
                continue;
            covered[to] = cnt;
            v.push_back(to);
        }
        while (!v.empty())
        {
            if (clq + (int)v.size() <= LB)
                break;
            int noww = -1, nowd = -1;
            for (int w : v)
            {
                int d = 0;
                for (int j = pstart[w]; j < pend[w]; ++j)
                {
                    int to = edges[j];
                    if (!used[to] && covered[to] == cnt)
                        ++d;
                }
                if (d >= nowd)
                {
                    noww = w;
                    nowd = d;
                }
            }
            ++clq;
            ++cnt;
            used[noww] = 1;
            theclique.push_back(noww);
            v.clear();
            for (int j = pstart[noww]; j < pend[noww]; ++j)
            {
                int to = edges[j];
                if (!used[to] && covered[to] == cnt - 1)
                {
                    covered[to] = cnt;
                    v.push_back(to);
                }
            }
        }
        if (clq > LB)
        {
            clqs.push_back(clq);
            // cerr<<"!"<<clq<<endl;
            mxclq = max(clq, mxclq);
            // if (LB != 0)
            // {
            //     printf("Clique sized %d:", clq);
            //     for (int x : theclique)
            //         printf("%d ", out_mapping[x]);
            //     puts("");
            // }
        }
        else
        {
            for (int x : theclique)
                used[x] = 0;
        }
    }
    sort(clqs.begin(), clqs.end(), greater<int>());
    for (int i = 0; i < min(10, (int)clqs.size()); ++i)
        cerr << clqs[i] << ' ';
    // cerr << endl;
    int l = LB, r = mxclq;
    // cerr<<"?"<<mxclq<<endl;
    while (l <= r)
    {
        int mid = (l + r) / 2;
        int sum = 0;
        for (int x : clqs)
            if (x > mid)
                sum += x - mid;
        if (sum > K)
            l = mid + 1;
        else
            r = mid - 1;
    }
    cerr << "LB:" << l << endl;
    printf("Time: %.3lfs .Initial lower bound: %d.\n", ((double)clock() - bgt) / (double)CLOCKS_PER_SEC, l);
    return l;
}
int *idtonode;

int exact_color()
{
    if (LB == 0)
        return fast_color();
    if (n <= LB || m < (long long)LB * (LB + 1) / 2)
        return LB;
    if (dict == nullptr)
        dict = new int[n];
    if (idtonode == nullptr)
        idtonode = new int[m];
    if (used == nullptr)
        used = new int[n];
    memset(used, 0, sizeof(int) * n);
    int delnode = 0;
    int ans = LB;
    vector<int> clqs;
    // cerr<<"?"<<LB<<endl;
    while (true)
    {
        int cnt = 0;
        for (int i = 0; i < n; ++i)
            if (!used[i])
            {
                idtonode[cnt] = i;
                dict[i] = cnt++;
            }

        Graph subg(".");
        vector<pair<int, int>> subedges;
        subedges.clear();
        for (int i = 0; i < n; ++i)
            if (!used[i])
                for (int j = pstart[i]; j < pend[i]; ++j)
                {
                    int k = edges[j];
                    if (!used[k] && k > i)
                        subedges.push_back(mp(dict[i], dict[k]));
                }
        for (int i = 0; i < n; ++i)
                dict[i] = -1;
        subg.myinit(subedges);
        vector<ui> clq = subg.max_clique_nodes();
        // cerr<<"???"<<clq.size()<<':';
        for (ui u : clq)
        {
            // cerr<<idtonode[u]<<' ';
            used[idtonode[u]] = 1;
        }
        // cerr<<endl;
        if (clq.size() <= LB)
            break;
        else
        {
            clqs.push_back(clq.size());
        }
    }
    while (true)
    {
        int delnode = 0;
        for (int x : clqs)
            if (x > ans)
                delnode += x - ans;
        if (delnode > K)
            ++ans;
        else
            break;
    }
    for (int i = 0; i < n; ++i)
        dict[i] = -1;
    cerr << "LBex:" << ans << endl;
    cerr << "time: " << ((double)clock() - bgt) / (double)CLOCKS_PER_SEC << endl;
    printf("Time: %.3lfs .Exact greedt lower bound: %d.\n", ((double)clock() - bgt) / (double)CLOCKS_PER_SEC, ans);
    return ans;
}
int extra_color()
{
    if (LB == 0)
        return fast_color();
    if (n <= LB || m < (long long)LB * (LB + 1) / 2)
        return LB;
    if (dict == nullptr)
        dict = new int[n];
    if (idtonode == nullptr)
        idtonode = new int[m];
    if (used == nullptr)
        used = new int[n];
    memset(used, 0, sizeof(int) * n);
    int delnode = 0;
    int ans = LB;
    // vector<int> clqs;
    vector<vector<pair<int, int>>> chords;
    while (true)
    {
        int cnt = 0;
        for (int i = 0; i < n; ++i)
            if (!used[i])
            {
                idtonode[cnt] = i;
                dict[i] = cnt++;
            }

        Graph subg(".");
        vector<pair<int, int>> subedges;
        subedges.clear();
        for (int i = 0; i < n; ++i)
            if (!used[i])
                for (int j = pstart[i]; j < pend[i]; ++j)
                {
                    int k = edges[j];
                    if (!used[k] && k > i)
                        subedges.push_back(mp(dict[i], dict[k]));
                }
        for (int i = 0; i < n; ++i)
            if (!used[i])
            {
                dict[i] = -1;
            }
        subg.myinit(subedges);
        vector<ui> clq = subg.max_clique_nodes();
        for (ui &x : clq)
            x = idtonode[x];
        for (ui u : clq)
            used[u] = 1;
        if (clq.size() <= LB)
            break;
        else
        {
            // clqs.push_back(clq.size());
            vector<pair<int, int>> chord;
            chord.push_back({0, clq.size()});
            vector<ui> oldclq = clq;
            int l = 0, r = clq.size();
            while (clq.size() > LB)
            {
                map<int, int> mp;
                for (ui x : clq)
                    for (int i = pstart[x]; i < pend[x]; ++i)
                        if (!used[edges[i]])
                            ++mp[edges[i]];
                int x = -1, mx = -1;
                for (auto [o, v] : mp)
                    if (v > mx)
                    {
                        x = o;
                        mx = v;
                    }
                if (x == -1 || used[x])
                    break;
                vector<ui> newclq;
                used[x] = 1;
                newclq.push_back(x);
                for (ui y : clq)
                    if (iscon(x, y))
                        newclq.push_back(y);
                    else
                        ++l;
                for (auto [o, v] : mp)
                    if (o != x && v == mx)
                    {
                        bool b = true;
                        for (ui y : newclq)
                            if (!iscon(o, y))
                            {
                                b = false;
                                break;
                            }
                        if (b)
                        {
                            newclq.push_back(o);
                            used[o] = 1;
                            ++r;
                            // chord.push_back(0);
                        }
                    }
                if (newclq.size() > LB)
                {
                    chord.push_back({l, r});
                    swap(newclq, clq);
                    clq.clear();
                }
                else
                    break;
            }
            swap(clq, oldclq);
            oldclq.clear();
            l = 0, r = clq.size();
            while (clq.size() > LB)
            {
                map<int, int> mp;
                for (ui x : clq)
                    for (int i = pstart[x]; i < pend[x]; ++i)
                        if (!used[edges[i]])
                            ++mp[edges[i]];
                int x = -1, mx = -1;
                for (auto [o, v] : mp)
                    if (v > mx)
                    {
                        x = o;
                        mx = v;
                    }
                if (x == -1 || used[x])
                    break;
                vector<ui> newclq;
                used[x] = 1;
                newclq.push_back(x);
                for (ui y : clq)
                    if (iscon(x, y))
                        newclq.push_back(y);
                    else
                        --r;
                for (auto [o, v] : mp)
                    if (o != x && v == mx)
                    {
                        bool b = true;
                        for (ui y : newclq)
                            if (!iscon(o, y))
                            {
                                b = false;
                                break;
                            }
                        if (b)
                        {
                            newclq.push_back(o);
                            used[o] = 1;
                            --l;
                            // chord.push_back(0);
                        }
                    }
                if (newclq.size() > LB)
                {
                    chord.push_back({l, r});
                    swap(newclq, clq);
                    clq.clear();
                }
                else
                    break;
            }
            sort(chord.begin(), chord.end());
            int mn = chord[0].first, add = -mn;
            for (int i = 0; i < chord.size(); ++i)
            {
                chord[i].first += add;
                chord[i].second += add;
            }
            chords.push_back(chord);
        }
    }
    while (true)
    {
        int delnode = 0;
        for (auto chord : chords)
        {
            vector<int> a(chord.back().second, 0);
            for (auto [l, r] : chord)
            {
                if (r - l <= ans)
                    continue;
                int sum = 0;
                for (int i = l; i < r; ++i)
                    ++sum;
                if (r - l - sum <= ans)
                    continue;
                int tmp = r - l - sum - ans;
                delnode += tmp;
                for (int i = r - 1; i >= l; --i)
                    if (!a[i])
                    {
                        a[i] = 1;
                        --tmp;
                        if (tmp == 0)
                            break;
                    }
            }
        }
        if (delnode > K)
            ++ans;
        else
            break;
    }
    for (int i = 0; i < n; ++i)
        dict[i] = -1;
    cerr << "LBextra:" << ans << endl;
    cerr << "time: " << ((double)clock() - bgt) / (double)CLOCKS_PER_SEC << endl;
    printf("Time: %.3lfs .Ex greedy lower bound: %d.\n", ((double)clock() - bgt) / (double)CLOCKS_PER_SEC, ans);
    return ans;
}
int newLB()
{
    if (LB == 0)
        return fast_color();
    if (n <= LB || m < (long long)LB * (LB + 1) / 2)
        return LB;
    if (dict == nullptr)
        dict = new int[n];
    if (idtonode == nullptr)
        idtonode = new int[m];
    if (used == nullptr)
        used = new int[n];
    memset(used, 0, sizeof(int) * n);
    int delnode = 0;
    int ans = LB;
    vector<int> clqs;
    while (true)
    {
        int cnt = 0;
        for (int i = 0; i < n; ++i)
            if (!used[i])
            {
                idtonode[cnt] = i;
                dict[i] = cnt++;
            }

        Graph subg(".");
        vector<pair<int, int>> subedges;
        subedges.clear();
        for (int i = 0; i < n; ++i)
            if (!used[i])
                for (int j = pstart[i]; j < pend[i]; ++j)
                {
                    int k = edges[j];
                    if (!used[k] && k > i)
                        subedges.push_back(mp(dict[i], dict[k]));
                }
        for (int i = 0; i < n; ++i)
            if (!used[i])
            {
                dict[i] = -1;
            }
        subg.myinit(subedges);
        vector<ui> clq = subg.max_clique_nodes();
        for (ui u : clq)
            used[idtonode[u]] = 1;
        if (clq.size() <= LB)
            break;
        else
        {
            clqs.push_back(clq.size());
        }
    }
    while (true)
    {
        int delnode = 0;
        for (int x : clqs)
            if (x > ans)
                delnode += x - ans;
        if (delnode > K)
            ++ans;
        else
            break;
    }
    for (int i = 0; i < n; ++i)
        dict[i] = -1;
    cerr << "LBnew:" << ans << endl;
    cerr << "time: " << ((double)clock() - bgt) / (double)CLOCKS_PER_SEC << endl;
    printf("Time: %.3lfs .New lower bound: %d.\n", ((double)clock() - bgt) / (double)CLOCKS_PER_SEC, ans);
    return ans;
}
ui *peel_sequence;
ui *core;
char *vis;
ListLinearHeap *heap;
// degeneracy-based k-defective clique
// return an upper bound of the maximum k-defective clique size
void degen()
{
    Timer t;

    ui threshold = LB;

    ui queue_n = 0, new_size = 0;
    for (ui i = 0; i < n; i++)
        if (degree[i] < threshold)
            peel_sequence[queue_n++] = i;
    for (ui i = 0; i < queue_n; i++)
    {
        ui u = peel_sequence[i];
        degree[u] = 0;
        for (ept j = pstart[u]; j < pend[u]; j++)
            if (degree[edges[j]] > 0)
            {
                if ((degree[edges[j]]--) == threshold)
                    peel_sequence[queue_n++] = edges[j];
            }
    }
    ept total_edges = 0;
    memset(vis, 0, sizeof(char) * n);
    for (ui i = 0; i < n; i++)
    {
        if (degree[i] >= threshold)
        {
            peel_sequence[queue_n + (new_size++)] = i;
            total_edges += degree[i];
        }
        else
        {
            vis[i] = 1;
            core[i] = 0;
        }
    }
    assert(queue_n + new_size == n);

    if (new_size != 0)
    {
        heap->init(new_size, new_size - 1, peel_sequence + queue_n, degree);
        ui max_core = 0;
        ui idx = n;
        for (ui i = 0; i < new_size; i++)
        {
            ui u, key;
            heap->pop_min(u, key);
            if (key > max_core)
                max_core = key;
            core[u] = max_core;
            peel_sequence[queue_n + i] = u;
            for (ept j = pstart[u]; j < pend[u]; j++)
                if (vis[edges[j]] == 0)
                {

                    total_edges -= 2;
                    heap->decrement(edges[j], 1);
                }
        }
#ifndef NDEBUG
        printf("*** Degeneracy Time: %s (microseconds)\n", Utility::integer_to_string(t.elapsed()).c_str());
#endif
    }
}
void degen_order()
{
    int total_edges = 0;
    for (ui i = 0; i < n; i++)
    {
        peel_sequence[i] = i;
        total_edges += degree[i];
    }
    heap->init(n, n - 1, peel_sequence, degree);
    ui max_core = 0;
    ui idx = n;
    for (ui i = 0; i < n; i++)
    {
        ui u, key;
        heap->pop_min(u, key);
        if (key > max_core)
            max_core = key;
        core[u] = max_core;
        peel_sequence[i] = u;
        for (ept j = pstart[u]; j < pend[u]; j++)
            if (vis[edges[j]] == 0)
            {
                total_edges -= 2;
                heap->decrement(edges[j], 1);
            }
    }
}
int *col;
int mxcol;
int aftercoln;
void color()
{
    degen_order();
    if (col == nullptr)
        col = new int[n];
    mxcol = 0;
    for (int i = 0; i < n; ++i)
        col[i] = n;
    for (int i = 0; i < n; ++i)
    {
        int u = peel_sequence[n - i - 1];
        for (int j = pstart[u]; j < pend[u]; j++)
        {
            int c = col[edges[j]];
            if (c != n)
                vis[c] = 1;
        }
        int tmp = mxcol;
        for (int j = 0; j < mxcol; j++)
            if (!vis[j])
            {
                tmp = j;
                break;
            }
        col[u] = tmp;
        if (tmp == mxcol)
            vis[mxcol++] = 0;
        for (int j = pstart[u]; j < pend[u]; j++)
        {
            int c = col[edges[j]];
            if (c != n)
                vis[c] = 0;
        }
    }
    int resn = n;
    for (int i=0;i<n;++i)
        ban[i]=0;
    for (int i=0;i<n;++i)
    {
        set<int> cols;
        for (int j = pstart[i]; j < pend[i]; j++)
            if (!ban[edges[j]])
                cols.insert(col[edges[j]]);
        if (cols.size()<LB)
        {
            --resn;
            ban[i]=1;
            // cerr<<"!!!"<<endl;
        }
        else
        {
            // if (i%100==0)
            //     cerr<<i<<' '<<cols.size()<<' '<<LB<<endl;
        }
    }
    aftercoln = resn;
    // cout<<"color:";
    // for (int i=0;i<n;++i)
    //     cout<<col[i]<<' ';
    // cout<<endl;
    // cout<<"mxcol:"<<mxcol<<endl;
}
void recolor()
{
    mxcol = 0;
    for (int i = 0; i < n; ++i)
        col[i] = n;
    for (int i = 0; i < n; ++i)
    {
        int u = peel_sequence[n - i - 1];
        if (ban[u])
            continue;
        for (int j = pstart[u]; j < pend[u]; j++)
        {
            int c = col[edges[j]];
            if (c != n)
                vis[c] = 1;
        }
        int tmp = mxcol;
        for (int j = 0; j < mxcol; j++)
            if (!vis[j])
            {
                tmp = j;
                break;
            }
        col[u] = tmp;
        if (tmp == mxcol)
            vis[mxcol++] = 0;
        for (int j = pstart[u]; j < pend[u]; j++)
        {
            int c = col[edges[j]];
            if (c != n)
                vis[c] = 0;
        }
    }
}
int clq_col_ub(int x)
{
    int sum = 0;
    for (int i = pstart[x]; i < pend[x]; ++i)
        if (!ban[edges[i]] && !vis[col[edges[i]]])
        {
            ++sum;
            vis[col[edges[i]]] = 1;
        }
    for (int i = pstart[x]; i < pend[x]; ++i)
        if (!ban[edges[i]])
        {
            vis[col[edges[i]]] = 0;
        }
    return sum + 1;
}
ui *rid;
void core_shrink_graph()
{
    ui cnt = 0;
    for (ui i = 0; i < n; i++)
        if (degree[i] >= LB)
        {
            rid[i] = cnt;
            out_mapping[cnt] = out_mapping[i];
            ++cnt;
        }

    if (cnt != n)
    {
        cnt = 0;
        ept pos = 0;
        for (ui i = 0; i < n; i++)
            if (degree[i] >= LB)
            {
                ept t_start = pstart[i];
                pstart[cnt] = pos;
                for (ept j = t_start; j < pstart[i + 1]; j++)
                    if (degree[edges[j]] >= LB)
                    {
                        edges[pos++] = rid[edges[j]];
                    }
                pend[cnt] = pos;
                // degree[cnt]=pend[cnt]-pstart[cnt];
                ++cnt;
            }
        for (int i = 0; i < cnt; ++i)
            degree[i] = pend[i] - pstart[i];
        pstart[cnt] = pos;
        for (ui i = 0; i < cnt; i++)
        {
            peel_sequence[i] = rid[peel_sequence[n - cnt + i]];
        }

        // if (pos > 0 && pos < m / 2)
        // {
        //     ept *pstart_new = new ept[cnt + 1];
        //     ui *edges_new = new ui[pos];
        //     memcpy(pstart_new, pstart, sizeof(ept) * (cnt + 1));
        //     memcpy(edges_new, edges, sizeof(ui) * pos);
        //     delete[] pstart;
        //     pstart = pstart_new;
        //     delete[] edges;
        //     edges = edges_new;
        // }

        n = cnt;
        m = pos;
    }
    // #ifndef NDEBUG
    printf("*** After core shrink: n = %s, m = %s (undirected)\n", Utility::integer_to_string(n).c_str(), Utility::integer_to_string(m / 2).c_str());
    // #endif
}
int *dend;
int *dstart;
void my_orient_graph()
{
    if (dedges == nullptr)
        dedges = new int[m];
    if (dend == nullptr)
        dend = new int[n];
    if (dstart == nullptr)
        dstart = new int[n];
    for (ui i = 0; i < n; i++)
        rid[peel_sequence[i]] = i;
    for (ui i = 0; i < n; i++)
    {
        dend[i] = dstart[i] = pstart[i];
        int &end = dend[i];
        for (ept j = pstart[i]; j < pstart[i + 1]; j++)
            if (rid[edges[j]] > rid[i])
                dedges[end++] = edges[j];
        // dend[i]=end;
    }

#ifndef NDEBUG
    cerr << "orient down" << endl;
#endif
}
int *adj;
void oriented_triangle_counting()
{
    memset(adj, 0, sizeof(ui) * n);
    long long cnt = 0;
    memset(tri_cnt, 0, sizeof(ui) * m);
    for (ui u = 0; u < n; u++)
    {
        for (ept j = pstart[u]; j < pend[u]; j++)
            adj[edges[j]] = j + 1;

        for (ept j = pstart[u]; j < pend[u]; j++)
        {
            ui v = edges[j];
            for (ept k = pstart[v]; k < pend[v]; k++)
                if (adj[edges[k]])
                {
                    ++tri_cnt[j];
                    ++tri_cnt[k];
                    ++tri_cnt[adj[edges[k]] - 1];
                    ++cnt;
                }
        }

        for (ept j = pstart[u]; j < pend[u]; j++)
            adj[edges[j]] = 0;
    }

#ifndef NDEBUG
    // printf("*** Total number of triangles: %s\n", Utility::integer_to_string(cnt).c_str());
#endif
}
int *edgeid;

[[maybe_unused]] int neg_clq_size(int u)
{
    Graph subg(".");
    vector<pair<int, int>> subedges;
    subedges.clear();
    int cnt = 0;
    for (int i = pstart[u]; i < pend[u]; ++i)
        if (!ban[edges[i]])
            dict[edges[i]] = cnt++;
    if (cnt < LB)
    {
        for (int i = pstart[u]; i < pend[u]; ++i)
            if (!ban[edges[i]])
                dict[edges[i]] = -1;
        return cnt + 1;
    }
    for (int i = pstart[u]; i < pend[u]; ++i)
    {
        int w = edges[i];
        if (!ban[w])
        {
            int mpw = dict[w];
            for (int j = pstart[w]; j < pend[w]; ++j)
                if (dict[edges[j]] != -1 && mpw < dict[edges[j]])
                    subedges.push_back(mp(mpw, dict[edges[j]]));
        }
    }
    for (int i = pstart[u]; i < pend[u]; ++i)
        if (!ban[edges[i]])
            dict[edges[i]] = -1;
    subg.myinit(subedges);
    // cerr<<"!"<<u<<' '<<subg.max_clique_size() + 1<<endl;
    return subg.max_clique_size() + 1;
}
vector<int> neg_clq_nodes(int u)
{
    Graph subg(".");
    vector<pair<int, int>> subedges;
    subedges.clear();
    int cnt = 0;
    vector<int> idtonodev;
    for (int i = pstart[u]; i < pend[u]; ++i)
        // if (!ban[edges[i]] && !deleted[edgeid[i]])
        if (!ban[edges[i]])
        {
            idtonodev.push_back(edges[i]);
            dict[edges[i]] = cnt++;
        }
    if (cnt < LB)
    {
        for (int i = pstart[u]; i < pend[u]; ++i)
            if (!ban[edges[i]])
                dict[edges[i]] = -1;
        return vector<int>();
    }
    for (int i = pstart[u]; i < pend[u]; ++i)
    {
        int w = edges[i];
        if (dict[w] != -1)
        {
            int mpw = dict[w];
            for (int j = pstart[w]; j < pend[w]; ++j)
                if (dict[edges[j]] != -1 && mpw < dict[edges[j]])
                    subedges.push_back(mp(mpw, dict[edges[j]]));
        }
    }
    for (int i = pstart[u]; i < pend[u]; ++i)
        if (!ban[edges[i]])
            dict[edges[i]] = -1;
    subg.myinit(subedges);
    vector<ui> subgv = subg.max_clique_nodes();
    vector<int> gv;
    for (ui x : subgv)
        gv.push_back(idtonodev[x]);
    return gv;
}
map<pair<int, int>, int> mpedgeid;
int ask_edge_id(int u, int v)
{
    if (u > v)
        swap(u, v);
    pair<int, int> ed = {u, v};
    return (mpedgeid.find(ed) == mpedgeid.end()) ? -1 : mpedgeid[ed];
    // return mpedgeid[ed];
}
int idcnt = 0;
pair<int, int> *idtoedge;
void triangle_counting()
{
    if (edgeid == nullptr)
        edgeid = new int[m];
    mpedgeid.clear();
    if (adj == nullptr)
        adj = new int[n];
    if (tri_cnt == nullptr)
        tri_cnt = new ui[m];
    if (idtoedge == nullptr)
        idtoedge = new pair<int, int>[m];
    memset(adj, 0, sizeof(int) * n);
    memset(tri_cnt, 0, sizeof(ui) * m);
    int cnt = 0;
    for (int i = 0; i < n; ++i)
        for (int j = pstart[i]; j < pend[i]; ++j)
            if (edges[j] > i)
            {
                idtoedge[cnt] = mp(i, edges[j]);
                mpedgeid[mp(i, edges[j])] = edgeid[j] = cnt++;
            }
            else
                edgeid[j] = mpedgeid[mp(edges[j], i)];
    idcnt = cnt;
    for (int u = 0; u < n; ++u)
    {
        for (int j = pstart[u]; j < pend[u]; ++j)
            adj[edges[j]] = edgeid[j] + 1;
        for (int j = pstart[u]; j < pend[u]; j++)
        {
            ui v = edges[j];
            if (v < u)
                continue;
            for (ept k = pstart[v]; k < pend[v]; k++)
                if (edges[k] > v && adj[edges[k]])
                {
                    ++tri_cnt[edgeid[j]];
                    ++tri_cnt[edgeid[k]];
                    ++tri_cnt[adj[edges[k]] - 1];
                }
        }
    }
}
void lazy_delete()
{
    triangle_counting();
    memset(ban, 0, sizeof(int) * n);
    memset(deleted, 0, sizeof(int) * m);
    deque<int> q;
    for (int i = 0; i < idcnt; ++i)
        if (tri_cnt[i] <= LB - 2)
            q.push_back(i+1);
    while (!q.empty())
    {
        int x = q.front();
        q.pop_front();
        if (x > 0)
        {
            --x;
            auto [u, v] = idtoedge[x];
            deleted[x] = 1;
            if (ban[u] || ban[v])
                continue;
            if (degree[u] >= LB)
            {
                --degree[u];
                if (degree[u] < LB)
                    q.push_front(-u);
            }
            if (degree[v] >= LB)
            {
                --degree[v];
                if (degree[v] < LB)
                    q.push_front(-v);
            }
            for (int i = pstart[u]; i < pend[u]; ++i)
                adj[edges[i]] = edgeid[i] + 1;
            for (ept k = pstart[v]; k < pend[v]; k++)
                if (!ban[edges[k]] && adj[edges[k]])
                {
                    int w = edgeid[k];
                    if (w != -1 && tri_cnt[w] > LB - 2 && !deleted[w])
                    {
                        --tri_cnt[w];
                        if (tri_cnt[w] <= LB - 2)
                            q.push_back(w+1);
                    }
                    w = adj[edges[k]] - 1;
                    if (w != -1 && tri_cnt[w] > LB - 2 && !deleted[w])
                    {
                        --tri_cnt[w];
                        if (tri_cnt[w] <= LB - 2)
                            q.push_back(w+1);
                    }
                }
            for (int i = pstart[u]; i < pend[u]; ++i)
                adj[edges[i]] = 0;
        }
        else
        {
            int u = -x;
            ban[u] = 1;
            for (int i = pstart[u]; i < pend[u]; ++i)
            {
                int v = edges[i];
                if (ban[v] || deleted[edgeid[i]])
                    continue;
                if (degree[v] >= LB)
                {
                    --degree[v];
                    if (degree[v] < LB)
                        q.push_front(-v);
                }
            }
            for (int i = pstart[u]; i < pend[u]; ++i)
                if (!ban[edges[i]] && !deleted[edgeid[i]])
                {
                    for (int j = i + 1; j < pend[u]; ++j)
                        if (!ban[edges[j]] && !deleted[edgeid[i]])
                        {
                            int w = ask_edge_id(edges[i], edges[j]);
                            if (w != -1 && tri_cnt[w] > LB - 2 && !deleted[w])
                            {
                                --tri_cnt[w];
                                if (tri_cnt[w] <= LB - 2)
                                    q.push_back(w+1);
                            }
                        }
                }
        }
    }
    // for (int i=)
}
bool work_lazy(int isclq = 0)
{
    ui cnt = 0;
    for (ui i = 0; i < n; i++)
        if (!ban[i])
        {
            rid[i] = cnt;
            peel_sequence[cnt] = i;
            out_mapping[cnt] = out_mapping[i];
            ++cnt;
        }
    // cerr<<n<<' '<<cnt<<' '<<isclq<<endl;
    if (cnt != n)
    {
        cnt = 0;
        ept pos = 0;
        for (ui i = 0; i < n; i++)
            if (!ban[i])
            {
                ept t_start = pstart[i];
                pstart[cnt] = pos;
                for (ept j = t_start; j < pstart[i + 1]; j++)
                    if (!ban[edges[j]] && !deleted[edgeid[j]])
                    {
                        edges[pos++] = rid[edges[j]];
                    }
                pend[cnt] = pos;
                // degree[cnt]=pend[cnt]-pstart[cnt];
                ++cnt;
            }
        for (int i = 0; i < cnt; ++i)
            degree[i] = pend[i] - pstart[i];
        pstart[cnt] = pos;
        // for (ui i = 0; i < cnt; i++)
        // {
        //     peel_sequence[i] = rid[peel_sequence[n - cnt + i]];
        // }

        // if (pos > 0 && pos < m / 2)
        // {
        //     ept *pstart_new = new ept[cnt + 1];
        //     ui *edges_new = new ui[pos];
        //     memcpy(pstart_new, pstart, sizeof(ept) * (cnt + 1));
        //     memcpy(edges_new, edges, sizeof(ui) * pos);
        //     delete[] pstart;
        //     pstart = pstart_new;
        //     delete[] edges;
        //     edges = edges_new;
        // }

        n = cnt;
        m = pos;
        // #ifndef NDEBUG
        if (!isclq)
            printf("*** After triangle shrink: n = %s, m = %s (undirected)\n", Utility::integer_to_string(n).c_str(), Utility::integer_to_string(m / 2).c_str());
        else
            printf("*** After clique shrink: n = %s, m = %s (undirected)\n", Utility::integer_to_string(n).c_str(), Utility::integer_to_string(m / 2).c_str());
        // #endif
        return true;
    }
    else
    {
        ept pos = 0;
        for (ui i = 0; i < n; i++)
        {
            ept t_start = pstart[i];
            pstart[i] = pos;
            for (ept j = t_start; j < pstart[i + 1]; j++)
                if (!ban[edges[j]] && !deleted[edgeid[j]])
                {
                    edges[pos++] = rid[edges[j]];
                }
            pend[i] = pos;
            degree[i] = pend[i] - pstart[i];
        }
        return false;
    }
    return false;
}
bool truss_shrink_graph()
{
    lazy_delete();
    return work_lazy();
}
int *omega;

[[maybe_unused]] vector<int> *nei_clq;
[[maybe_unused]] void lazy_neighbor_clique()
{
    memset(ban, 0, sizeof(int) * n);
    if (nei_clq == nullptr)
        nei_clq = new vector<int>[n];
    for (int i = 0; i < n; ++i)
    {
        nei_clq[i] = neg_clq_nodes(i);
        if (nei_clq[i].size() < LB)
            ban[i] = 1;
    }
}
vector<vector<int>> clqs;
void lazy_neighbor_clique_all()
{
    // memset(ban, 0, sizeof(int) * n);
    if (omega == nullptr)
        omega = new int[n];
    memset(omega, 0, sizeof(int) * n);
    clqs.clear();
    for (int i = 0; i < n; ++i)
    {
        if (ban[i]==1)
            continue;
        vector<int> clq = neg_clq_nodes(i);
        // if (i%100==0)
        //     cerr<<i<<':'<<clq.size()<<endl;
        // nei_clq[i]=neg_clq_nodes(i);
        // if (clq.size() >= LB && clq.size()>omega[i])
        if (clq.size() >= LB)
        {
            clq.push_back(i);
            int clqsz = clq.size();
            for (int x : clq)
                omega[x] = max(omega[x], clqsz);
            clqs.push_back(clq);
        }
        else
            omega[i] = clq.size() + 1;
        if (omega[i] <= LB)
            ban[i] = 1;
    }
}
void lazy_neighbor_clique_kuo(int notfirst = 0)
{
    if (notfirst == 0)
    {
        memset(ban, 0, sizeof(int) * n);
        if (omega == nullptr)
            omega = new int[n];
        memset(omega, 0, sizeof(int) * n);
        clqs.clear();
        for (int i = 0; i < n; ++i)
        {
            if (omega[i] == 0)
            {
                vector<int> clq = neg_clq_nodes(i);
                // nei_clq[i]=neg_clq_nodes(i);
                if (clq.size() >= LB)
                {
                    clq.push_back(i);
                    int clqsz = clq.size();
                    for (int x : clq)
                        omega[x] = max(omega[x], clqsz);
                    clqs.push_back(clq);
                }
                else
                    omega[i] = clq.size() + 1;
            }
            if (omega[i] <= LB)
                ban[i] = 1;
        }
    }
    else
    {
        memset(ban, 0, sizeof(int) * n);
        bool b = true;
        for (auto &v : clqs)
            if (v.size() <= LB)
                b = false;
        if (b)
            return;
        vector<vector<int>> newclqs;
        for (auto &v : clqs)
            if ((int)v.size() <= LB)
            {
                for (int i = 0; i < (int)v.size() - 1; ++i)
                    if (omega[v[i]] <= LB)
                        omega[v[i]] = 0;
            }
            else
            {
                newclqs.push_back(v);
            }
        for (int i = 0; i < n; ++i)
        {
            if (omega[i] == 0)
            {
                vector<int> clq = neg_clq_nodes(i);
                // nei_clq[i]=neg_clq_nodes(i);
                if (clq.size() >= LB)
                {
                    clq.push_back(i);
                    int clqsz = clq.size();
                    for (int x : clq)
                        omega[x] = max(omega[x], clqsz);
                    clqs.push_back(clq);
                }
                else
                    omega[i] = clq.size() + 1;
            }
            if (omega[i] <= LB)
                ban[i] = 1;
        }
    }
}
bool nei_clq_del()
{
    ui cnt = 0;
    for (ui i = 0; i < n; i++)
        if (!ban[i])
        {
            rid[i] = cnt;
            peel_sequence[cnt] = i;
            out_mapping[cnt] = out_mapping[i];
            ++cnt;
        }
    for (int i = 0; i < (int)clqs.size(); ++i)
        for (int &x : clqs[i])
            x = rid[x];
    if (cnt != n)
    {
        cnt = 0;
        ept pos = 0;
        for (ui i = 0; i < n; i++)
            if (!ban[i])
            {
                ept t_start = pstart[i];
                pstart[cnt] = pos;
                for (ept j = t_start; j < pstart[i + 1]; j++)
                    if (!ban[edges[j]])
                    {
                        edges[pos++] = rid[edges[j]];
                    }
                pend[cnt] = pos;
                omega[cnt] = omega[i];
                // nei_clq[cnt] = nei_clq[i];
                // for (int &x : nei_clq[cnt])
                //     x = rid[x];
                ++cnt;
            }
        for (int i = 0; i < cnt; ++i)
            degree[i] = pend[i] - pstart[i];
        pstart[cnt] = pos;
        // for (ui i = 0; i < cnt; i++)
        // {
        //     peel_sequence[i] = rid[peel_sequence[n - cnt + i]];
        // }

        // if (pos > 0 && pos < m / 2)
        // {
        //     ept *pstart_new = new ept[cnt + 1];
        //     ui *edges_new = new ui[pos];
        //     memcpy(pstart_new, pstart, sizeof(ept) * (cnt + 1));
        //     memcpy(edges_new, edges, sizeof(ui) * pos);
        //     delete[] pstart;
        //     pstart = pstart_new;
        //     delete[] edges;
        //     edges = edges_new;
        // }

        n = cnt;
        m = pos;
        // #ifndef NDEBUG
        printf("*** After clique shrink: n = %s, m = %s (undirected)\n", Utility::integer_to_string(n).c_str(), Utility::integer_to_string(m / 2).c_str());
        cerr << "n: " << n << ' ' << "m: " << m << ' ';
        cerr << "time: " << ((double)clock() - bgt) / (double)CLOCKS_PER_SEC << endl;
        // #endif
        return true;
    }
    return false;
}
bool clique_shrink_graph()
{
    // lazy_clique_delete();
    // lazy_neighbor_clique_kuo();
    lazy_neighbor_clique_all();
    // return work_lazy(1);
    return nei_clq_del();
}
void lazy_neighbor_clique_after_LB_change()
{
    memset(ban, 0, sizeof(int) * n);
    for (int i = 0; i < n; ++i)
    {
        if (nei_clq[i].size() < LB)
            ban[i] = 1;
    }
}
bool clique_shrink_graph_after_LB_change()
{
    // lazy_clique_delete();
    lazy_neighbor_clique_after_LB_change();
    // return work_lazy(1);
    return nei_clq_del();
}
map<int, int> *mps;
void reduce()
{
    degen();
    core_shrink_graph();
    truss_shrink_graph();
    if (!clique_shrink_graph())
        my_orient_graph();
}
int get_UB();
// MYILP myilp;
double redti;
vector<pair<int,double> > red;
void pre_reduce()
{
    LB = fast_color();
    if (peel_sequence == nullptr)
        peel_sequence = new ui[n];
    if (core == nullptr)
        core = new ui[n];
    if (degree == nullptr)
        degree = new ui[n];
    if (vis == nullptr)
        vis = new char[n];
    if (mps == nullptr)
        mps = new map<int, int>[n];
    if (heap == nullptr)
        heap = new ListLinearHeap(n, n - 1);
    degen();
    out_mapping = new ui[n];
    for (int i = 0; i < n; ++i)
        out_mapping[i] = i;
    rid = new ui[n];
    core_shrink_graph();
    red.push_back(make_pair(n,((double)clock() - bgt) / (double)CLOCKS_PER_SEC));
    truss_shrink_graph();
    red.push_back(make_pair(n,((double)clock() - bgt) / (double)CLOCKS_PER_SEC));
    LB = max(LB, exact_color());
    aftercoln =n;
    if (n != 0)
        color();
    red.push_back(make_pair(aftercoln,((double)clock() - bgt) / (double)CLOCKS_PER_SEC));
    clique_shrink_graph();
    red.push_back(make_pair(n,((double)clock() - bgt) / (double)CLOCKS_PER_SEC));
    redti=((double)clock() - bgt) / (double)CLOCKS_PER_SEC;
    cerr<<"redti:"<<redti<<endl;
    my_orient_graph();
}
int *UB;
int *dist;
const int mod = 998244353; // 应该不会撞吧，希望人没事
bool cmprid(int x, int y)
{
    return rid[x] > rid[y];
}
int _n;
int alltime = 0;
int *hitcount;
vector<int> *hitclq;
int hitsum;
int clqcnt;
int *clqlb;
int *clqsz;
int *sel;
int *domed;
int resnode;
void reduce_during_search(int u, vector<int> &del);
bool cmpcol(int x, int y)
{
    return col[x] > col[y];
}
int get_UB();
int exact_UB();
int clq_col_ub_sel(int x)
{
    int sum = 0;
    for (int i = pstart[x]; i < pend[x]; ++i)
        if (sel[edges[i]] && !vis[col[edges[i]]])
        {
            ++sum;
            vis[col[edges[i]]] = 1;
        }
    for (int i = pstart[x]; i < pend[x]; ++i)
        if (sel[edges[i]])
        {
            vis[col[edges[i]]] = 0;
        }
    return sum + 1;
}
int final_max_clique(int bg = 0)
{
    int cnt = 0;
    for (int i = bg; i < n; ++i)
        if (!ban[i])
        {
            idtonode[cnt] = i;
            dict[i] = cnt++;
        }
    if (cnt <= 1)
    {
        for (int i = bg; i < n; ++i)
            if (!ban[i])
            {
                dict[i] = -1;
            }
        return cnt;
    }
    Graph subg(".");
    vector<pair<int, int>> subedges;
    subedges.clear();
    for (int i = bg; i < n; ++i)
        if (!ban[i])
            for (int j = pstart[i]; j < pend[i]; ++j)
            {
                int k = edges[j];
                if (!ban[k] && k > i)
                    subedges.push_back(mp(dict[i], dict[k]));
            }
    for (int i = bg; i < n; ++i)
        if (!ban[i])
        {
            dict[i] = -1;
        }
    if (subedges.size() <= 1)
        return subedges.size() + 1;
    if (subedges.size() >= cnt * (cnt - 1) / 2 - 1)
        return cnt - (subedges.size() - cnt * (cnt - 1) / 2);
    subg.myinit(subedges);
    return subg.max_clique_size();
}
int final_max_clique_nei(int u)
{
    int cnt = 0;
    for (int i = pstart[u]; i < pend[u]; ++i)
        if (!ban[edges[i]])
        {
            idtonode[cnt] = edges[i];
            dict[edges[i]] = cnt++;
        }
    if (cnt <= 1)
    {
        for (int i = pstart[u]; i < pend[u]; ++i)
            if (!ban[edges[i]])
            {
                dict[edges[i]] = -1;
            }
        return cnt;
    }
    Graph subg(".");
    vector<pair<int, int>> subedges;
    subedges.clear();
    for (int _i = pstart[u]; _i < pend[u]; ++_i)
    {
        int i = edges[_i];
        if (!ban[i] && dict[i] != -1)
            for (int j = pstart[i]; j < pend[i]; ++j)
            {
                int k = edges[j];
                if (!ban[k] && k > i && dict[k] != -1)
                    subedges.push_back(mp(dict[i], dict[k]));
            }
    }
    for (int i = pstart[u]; i < pend[u]; ++i)
        if (!ban[edges[i]])
        {
            dict[edges[i]] = -1;
        }
    if (subedges.size() <= 1)
        return subedges.size() + 1;
    if (subedges.size() >= cnt * (cnt - 1) / 2 - 1)
        return cnt - (subedges.size() - cnt * (cnt - 1) / 2);
    subg.myinit(subedges);
    return subg.max_clique_size();
}
vector<int> final_max_clique_nodes(int bg = 0)


{
    int cnt = 0;
    for (int i = bg; i < n; ++i)
        if (!ban[i])
        {
            idtonode[cnt] = i;
            dict[i] = cnt++;
        }
    if (cnt == 0)
    {
        return vector<int>();
    }
    Graph subg(".");
    vector<pair<int, int>> subedges;
    subedges.clear();
    for (int i = bg; i < n; ++i)
        if (!ban[i])
            for (int j = pstart[i]; j < pend[i]; ++j)
            {
                int k = edges[j];
                if (!ban[k] && k > i)
                    subedges.push_back(mp(dict[i], dict[k]));
            }
    for (int i = bg; i < n; ++i)
        if (!ban[i])
        {
            dict[i] = -1;
        }
    subg.myinit(subedges);
    vector<ui> tmp = subg.max_clique_nodes();
    vector<int> fin;
    for (int x : tmp)
        fin.push_back(idtonode[x]);
    return fin;
}
bool cmpdeg(int x, int y)
{
    return degree[x] > degree[y];
}
int get_UB()
{
    if (n < LB || n == 0 || n < K)
        return LB;
    vector<int> colord;
    for (int i = 0; i < n; ++i)
        colord.push_back(i);
    sort(colord.begin(), colord.end(), cmpcol);
    memset(ban, 0, sizeof(int) * n);
    for (int i = 0; i < K; ++i)
        ban[colord[i]] = 1;
    int tmp = final_max_clique();
    for (int i = 0; i < K; ++i)
        ban[colord[i]] = 0;
    sort(colord.begin(), colord.end(), cmpdeg);
    for (int i = 0; i < K; ++i)
        ban[colord[i]] = 1;
    tmp = min(tmp, final_max_clique());
    for (int i = 0; i < K; ++i)
        ban[colord[i]] = 0;
    return max(tmp, LB);
}

// mt19937 rnd(time(0));
int exact_UB()
{
    if (n < LB || n == 0 || n < K)
        return LB;
    for (int i = 0; i < K; ++i)
    {
        vector<int> tmp = final_max_clique_nodes();
        // if (i!=0)
        //     clqs.push_back(tmp);
        int tmpsz = -1, tmpnd = 0;
        for (int x : tmp)
            ban[x] = 1;
        for (int x : tmp)
        {
            // int tmpc=final_max_clique_nei(x);
            int tmpc = degree[x];
            if (tmpc > tmpsz)
            {
                tmpc = tmpsz;
                tmpnd = x;
            }
        }
        for (int x : tmp)
            if (x != tmpnd)
                ban[x] = 0;
    }
    int ans = final_max_clique();
    memset(ban, 0, sizeof(int) * n);
    return max(ans, LB);
}
bool cmpcandidate(int x, int y)
{
    return hitcount[x] < hitcount[y];
}
int nodesum = 0;
int con_cnt = 0;
int ilpcut,ilpnode;
struct MYILP
{
    IloEnv env;
    IloModel model;
    IloBoolVarArray x;
    IloIntVar lb;
    IloCplex cplex;
    int n;

    // 添加的懒惰约束回调类
    class LazyConstraintCallback : public IloCplex::LazyConstraintCallbackI
    {
    private:
        IloBoolVarArray _x;
        IloIntVar _lb;
        IloEnv _env;

    public:
        LazyConstraintCallback(IloEnv env, IloBoolVarArray x, IloIntVar lb)
            : IloCplex::LazyConstraintCallbackI(env), _x(x), _lb(lb), _env(env) {}
        void main() override
        {
            // if (!IsFeasible())
            //     return;
            int n = _x.getSize();
            // LB = max(LB, (int)getValue(_lb));
            vector<int> v;
            for (int i = 0; i < n; ++i)
            {
                if (round(getValue(_x[i])) == 0)
                {
                    v.push_back(i);
                }
            }
            // for (int i = 0; i < 20; ++i)
            // {
            //     cout << "x[" << i << "] = " << getValue(_x[i]) << ' ';
            // }
            // cout<<endl;
            // get_select_nodes(v);
            for (int x : v)
                ban[x] = 1;
            vector<int> clq = final_max_clique_nodes();
            // ans = min(ans, (int)clq.size());
            vector<int> neis;
            vector<vector<int>> clqs;
            int nowlb = round(getValue(_lb));
            if (clq.size() <= LB)
            {
                for (int x : v)
                    ban[x] = 0;
                return;
            }
            else
            {
                // printf("node %d bad clique size %d :", ++nodesum, clq.size());
                // sort(clq.begin(), clq.end());
                // for (int x : clq)
                //     printf("%d ", x);
                // puts("");
            }
            while (clq.size() > LB)
            {

                for (int x : v)
                {
                    bool b = true;
                    for (int y : clq)
                        if (!iscon(x, y))
                        {
                            b = false;
                            break;
                        }
                    if (b)
                    {
                        bool bb = false;
                        // cerr<<x<<endl;
                        for (int i = 0; i < clqs.size(); ++i)
                        {
                            bool bbb = true;
                            for (int z : clqs[i])
                                if (!iscon(x, z))
                                {
                                    bbb = false;
                                    break;
                                }
                            if (bbb)
                            {
                                bb = true;
                                clqs[i].push_back(x);
                                break;
                            }
                        }
                        if (!bb)
                        {
                            clqs.push_back(vector<int>{x});
                        }
                    }
                }
                if (clqs.empty())
                {
                    IloExpr lazyConstraint(_env);
                    for (int i : clq)
                    {
                        lazyConstraint += _x[i];
                    }
                    // 添加懒惰约束
                    add(lazyConstraint <= _lb);
                    lazyConstraint.end();
                    con_cnt++;
                }
                else
                {
                    for (int i = 0; i < clqs.size(); ++i)
                    {
                        IloExpr lazyConstraint(_env);
                        for (int y : clq)
                        {
                            lazyConstraint += _x[y];
                        }
                        for (int y : clqs[i])
                        {
                            lazyConstraint += _x[y];
                        }
                        // 添加懒惰约束
                        add(lazyConstraint <= _lb);
                        lazyConstraint.end();
                        con_cnt++;
                    }
                }
                break;
                clqs.clear();
                int x = clq[0];
                for (int y : clq)
                    if (omega[y] > omega[x] || (omega[y] == omega[x] && degree[y] > degree[x]))
                        x = y;
                v.push_back(x);
                ban[x] = 1;
                clq = final_max_clique_nodes();
            }
            for (int x : v)
                ban[x] = 0;
            // if (nodesum % 10 == 0)
            // {
            //     cerr << nodesum << ':' << LB << ' ' << ans << ' ' << con_cnt << endl;
            // }
        }
        IloCplex::CallbackI *duplicateCallback() const override
        {
            return new (_env) LazyConstraintCallback(_env, _x, _lb);
        }
    };

    MYILP(int _n, int k, int _LB, int _UB)
    {
        n = _n;
        k = min(k, _n);
        model = IloModel(env);
        x = IloBoolVarArray(env, n);
        lb = IloIntVar(env, _LB, _UB);
        model.add(IloMinimize(env, lb));
        IloExpr expr(env);
        for (int y = 0; y < n; ++y)
            expr += x[y];
        model.add(expr >= n - k);
        expr.end();
        cplex = IloCplex(model);
        cplex.setParam(IloCplex::Param::MIP::Display, 2);
        // cplex.setOut(env.getNullStream());
        cplex.setParam(IloCplex::MIPSearch, IloCplex::Traditional);
        // 注册懒惰约束回调
        cplex.setParam(IloCplex::Param::TimeLimit, 300); 
        cplex.use(new (env) LazyConstraintCallback(env, x, lb)); // 修改点
    }

    ~MYILP()
    {
        env.end();
    }

    void update_lb(int _LB)
    {
        lb.setLB(IloNum(_LB));
    }

    void add_clq(vector<int> &clq)
    {
        ++con_cnt;
        IloExpr expr(env);
        for (int y : clq)
            expr += x[y];
        model.add(expr <= lb);
        expr.end();
    }

    void add_clqs(vector<vector<int>> &clqs)
    {
        int m = clqs.size();
        for (int i = 0; i < m; ++i)
        {
            add_clq(clqs[i]);
        }
    }

    int get_constraint_count() const
    {
        try
        {
            return cplex.getNrows();
        }
        catch (const IloException &e)
        {
            std::cerr << "Error retrieving constraint count: " << e.getMessage() << std::endl;
            return -1; // 表示错误
        }
    }

    bool solve()
    {
        bool solved = cplex.solve();
        ilpnode = cplex.getNnodes();
        ilpcut = cplex.getNcuts(IloCplex::CutUser);
        // 检查是否超时
        if (!solved)
        {
            std::cout << "Time limit reached or no feasible solution found." << std::endl;
            
            // 获取当前的上下界
            double upperBound = get_upper_bound();  // 最佳目标值（上界）
            double lowerBound = get_lower_bound();  // 当前目标值（下界）

            std::cout << "Upper Bound: " << upperBound << std::endl;
            std::cout << "Lower Bound: " << lowerBound << std::endl;
            
            // 根据情况决定后续的操作
            // 你可以选择将当前的解视为最终结果，或者输出超时相关信息，进行其他处理
        }

        return solved;
    }


    void set_ub(int ub)
    {
        IloNumVarArray mipStart(env);
        IloNumArray startValues(env);
        mipStart.add(lb);
        startValues.add(ub);
        cplex.deleteMIPStarts(0, cplex.getNMIPStarts());
        cplex.addMIPStart(mipStart, startValues);
        mipStart.end();
        startValues.end();
    }

    int get_ans()
    {
        return round(cplex.getValue(lb));
    }

    void get_select_nodes(vector<int> &v)
    {
        for (int i = 0; i < n; ++i)
            if (round(cplex.getValue(x[i])) == 0)
                v.push_back(i);
    }

    double get_upper_bound()
    {
        return cplex.getBestObjValue();
    }
    double get_lower_bound()
    {
        return cplex.getObjValue();
    }
};
int ilp_search()
{
    ans = n;//get_UB();
    cerr << "UB" << ':' << ans << endl;
    if (n <= LB)
    {
        printf("Maximal Interdiction Clique: %d\n", ans);
        printf("totol time = %.3lf s", ((double)clock() - bgt) / (double)CLOCKS_PER_SEC);
        return LB;
    }
    MYILP myilp(n, K, LB, ans);
    myilp.add_clqs(clqs);
    myilp.solve();
    return round(myilp.get_ans());
}
int main(int argc, char *argv[])
{
    std::ofstream outfile("summary.txt", std::ios::app);
    outfile << std::fixed << std::setprecision(3);
    outfile<<endl;
    freopen(argv[1], "r", stdin);
    // cerr<<argc<<endl;
    if (argc==2)
        freopen("out.txt", "w", stdout);
    else
        freopen(argv[2],"w",stdout);
    read_graph_std();
    // K=20;
    K = (n - 1) / 200 + 1;
    if (argc>3)
    {
        double dk=atof(argv[3]);
        K =ceil(n*dk);
    }
    int inK=K;
    // K = 5;
    // K=1;
    bgt = clock();
    ban = new int[n];
    memset(ban, 0, sizeof(int) * n);
    deleted = new int[m];
    memset(deleted, 0, sizeof(int) * m);
    dict = new int[n];
    memset(dict, -1, sizeof(int) * n);
    pre_reduce();
    UB = new int[n];
    dist = new int[n];
    memset(dist, 0, sizeof(int) * n);
    char lujing[100];
    int fi=0;
    for (int i=0;i<strlen(argv[1]);++i)
        if (argv[1][i]=='/')
            fi=i+1;
    for (int i=fi;i<strlen(argv[1]);++i)
        lujing[i-fi]=argv[1][i];
    lujing[strlen(argv[1])-fi]=0;
    printf("%s\t%d\t%d\t%d\t",argv[1],inn,inm,inK);
    outfile<<lujing<<'\t'<<inn<<'\t'<<inm<<'\t'<<inK<<'\t';
    for (auto x:red)
    {
        printf("%d\t%.3lf\t",x.first,x.second);
        outfile<<x.first<<'\t'<<x.second<<'\t';
    }
    outfile.flush();
    printf("\n");
    int ans = ilp_search();

    cerr << "node sum:" << nodesum << endl;
    cerr << ans << endl;
    cerr<<"totol time = "<<((double)clock() - bgt) / (double)CLOCKS_PER_SEC<<" resnode = "<<n<<endl;
    // cerr << LB << ' ' << ans << endl;
    printf("Maximal Interdiction Clique: %d\n", ans);
    printf("totol time = %.3lf s\n", ((double)clock() - bgt) / (double)CLOCKS_PER_SEC);
    // printf("%d\t%.3lf\t%d\t%.3lf\t%d\t%d\t%d\n",ans,((double)clock() - bgt) / (double)CLOCKS_PER_SEC,n,redti,LB,ilpnode,ilpcut);    
    printf("%s\t%d\t%d\t",argv[1],inn,inm);
    for (auto x:red)
        printf("%d\t%.3lf\t",x.first,x.second);
    printf("%d\t%.3lf\t%d\t%.3lf\t%d\t%d\t%d\n",ans,((double)clock() - bgt) / (double)CLOCKS_PER_SEC,n,redti,LB,ilpnode,ilpcut);    
    outfile<<ans<<'\t'<<((double)clock() - bgt) / (double)CLOCKS_PER_SEC<<'\t'<<LB<<'\t'<<ilpnode<<'\t'<<ilpcut<<'\t';
    // printf("\n");
    outfile.flush();
    outfile.close();
    return 0;
}