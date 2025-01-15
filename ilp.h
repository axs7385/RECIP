
#include <ilcplex/ilocplex.h>
#include <vector>
ILOSTLBEGIN
// int get_new_LB(int n, vector<vector<int>> clqs, int _LB, int _UB, int k)
// {
//     IloEnv env;
//     IloModel model(env);
//     // IloBoolVarArray x(env, n);
//     IloNumVarArray x(env, n, 0, 1, ILOBOOL); // 0 或 1 的二进制变量
//     IloIntVar lb(env, (IloInt)_LB, (IloInt)_UB);
//     model.add(IloMinimize(env, lb));
//     int m = clqs.size();
//     for (int i = 0; i < m; ++i)
//     {
//         IloExpr expr(env);
//         for (int y : clqs[i])
//             expr += x[y];
//         expr += lb;
//         model.add(expr >= (int)clqs[i].size());
//         // cerr<<clqs[i].size()<<' ';
//         expr.end();
//     }
//     // cerr<<endl;
//     IloExpr expr(env);
//     for (int y = 0; y < n; ++y)
//         expr += x[y];
//     model.add(expr <= k);
//     expr.end();
//     IloCplex cplex(model);
//     cplex.setOut(env.getNullStream());
//     cplex.solve();
//     int lbValue = -1; // 默认值
//     // for (int i=0;i<n;++i)
//     //     cerr<<cplex.getValue(x[i]);cerr<<endl;
//     if (cplex.getStatus() == IloAlgorithm::Optimal)
//     {
//         lbValue = (int)cplex.getValue(lb); // 获取 lb 的解值
//     }
//     env.end();
//     return lbValue; // 返回 lb 的值
// }
struct MYILP
{
    IloEnv env;
    IloModel model;
    IloBoolVarArray x; // 0 或 1 的二进制变量
    IloIntVar lb;
    IloCplex cplex;
    int n;
    MYILP()
    {
        n = 0;
    }
    MYILP(int _n, int k, int _LB, int _UB)
    {
        n = _n;
        k = min(k,_n);
        model = IloModel(env);
        x = IloBoolVarArray(env, n);
        lb = IloIntVar(env, _LB, _UB);
        model.add(IloMinimize(env, lb));
        IloExpr expr(env);
        for (int y = 0; y < n; ++y)
            expr += x[y];
        model.add(expr <= k);
        expr.end();
        cplex = IloCplex(model);
        cplex.setOut(env.getNullStream());
        cplex.setParam(IloCplex::MIPSearch, IloCplex::Traditional);
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
        IloExpr expr(env);
        for (int y : clq)
            expr += x[y];
        expr += lb;
        model.add(expr >= (int)clq.size());
        expr.end();
    }
    void add_clqs(vector<vector<int>> &clqs)
    {
        int m = clqs.size();
        for (int i = 0; i < m; ++i)
        {
            add_clq(clqs[i]);
            // IloExpr expr(env);
            // for (int y:clqs[i])
            //     expr += x[y];
            // expr += lb;
            // model.add(expr >= (int)clqs[i].size());
            // expr.end();
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
        return cplex.solve();
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
        return cplex.getValue(lb);
    }
    void get_select_nodes(vector<int> &v)
    {
        for (int i = 0; i < n; ++i)
            if (round(cplex.getValue(x[i])) == 1)
                v.push_back(i);
    }
};
// int main()
// {
//     int n=7;
//     int k=2;
//     vector<vector<int> > clqs;
//     clqs.push_back(vector<int>{0,1,2});
//     clqs.push_back(vector<int>{2,3,4});
//     clqs.push_back(vector<int>{4,5,6});
//     printf("%d\n",ask(n,clqs,0,n,k));
//     return 0;
// }