#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <climits>
#include <cfloat>
#include <ctime>
#include <cassert>
#include <map>
#include <utility>
#include <set>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <algorithm>
#include <functional>
#include <sstream>
#include <complex>
#include <stack>
#include <queue>
#include <numeric>
#include <list>
#include <iomanip>
#include <fstream>
#include <bitset>

using namespace std;

#define foreach(it, c) for (__typeof__((c).begin()) it=(c).begin(); it != (c).end(); ++it)
template <typename T> void print_container(ostream& os, const T& c) { const char* _s = " "; if (!c.empty()) { __typeof__(c.begin()) last = --c.end(); foreach (it, c) { os << *it; if (it != last) os << _s; } } }
template <typename T> ostream& operator<<(ostream& os, const vector<T>& c) { print_container(os, c); return os; }
template <typename T> ostream& operator<<(ostream& os, const set<T>& c) { print_container(os, c); return os; }
template <typename T> ostream& operator<<(ostream& os, const multiset<T>& c) { print_container(os, c); return os; }
template <typename T> ostream& operator<<(ostream& os, const deque<T>& c) { print_container(os, c); return os; }
template <typename T, typename U> ostream& operator<<(ostream& os, const map<T, U>& c) { print_container(os, c); return os; }
template <typename T, typename U> ostream& operator<<(ostream& os, const pair<T, U>& p) { os << "(" << p.first << ", " << p.second << ")"; return os; }

template <typename T> void print(T a, int n, const string& split = " ") { for (int i = 0; i < n; i++) { cout << a[i]; if (i + 1 != n) cout << split; } cout << endl; }
template <typename T> void print2d(T a, int w, int h, int width = -1, int br = 0) { for (int i = 0; i < h; ++i) { for (int j = 0; j < w; ++j) { if (width != -1) cout.width(width); cout << a[i][j] << ' '; } cout << endl; } while (br--) cout << endl; }
template <typename T> void input(T& a, int n) { for (int i = 0; i < n; ++i) cin >> a[i]; }
#define dump(v) (cerr << #v << ": " << v << endl)

#define rep(i, n) for (int i = 0; i < (int)(n); ++i)
#define erep(i, n) for (int i = 0; i <= (int)(n); ++i)
#define all(a) (a).begin(), (a).end()
#define rall(a) (a).rbegin(), (a).rend()
#define clr(a, x) memset(a, x, sizeof(a))
#define sz(a) ((int)(a).size())
#define mp(a, b) make_pair(a, b)
#define ten(n) ((long long)(1e##n))

template <typename T, typename U> void upmin(T& a, const U& b) { a = min<T>(a, b); }
template <typename T, typename U> void upmax(T& a, const U& b) { a = max<T>(a, b); }
template <typename T> void uniq(T& a) { sort(a.begin(), a.end()); a.erase(unique(a.begin(), a.end()), a.end()); }
template <class T> string to_s(const T& a) { ostringstream os; os << a; return os.str(); }
template <class T> T to_T(const string& s) { istringstream is(s); T res; is >> res; return res; }
void fast_io() { cin.tie(0); ios::sync_with_stdio(false); }
bool in_rect(int x, int y, int w, int h) { return 0 <= x && x < w && 0 <= y && y < h; }

typedef long long ll;
typedef pair<int, int> pint;




const int MAX_ZONE_COUNT = 256;
const int BUY_COST = 20;

int plat_src[MAX_ZONE_COUNT];
vector<int> zone_link[MAX_ZONE_COUNT];

const int NEAUTRAL = -1;
const int inf = ten(8);

int zone_count;

int zone_dist[MAX_ZONE_COUNT][MAX_ZONE_COUNT];

struct Move
{
    int from, to;
    Move() : from(-1){}
    Move(int from, int to)
        : from(from), to(to)
    {
    }

    string to_s() const
    {
        char buf[256];
        sprintf(buf, "1 %d %d", from, to);
        return buf;
    }

    string to_p() const
    {
        char buf[256];
        sprintf(buf, "%2d -> %2d", from, to);
        return buf;
    }
};
int count_sum_src(int id, const vector<int>& owner)
{
    int sum = 0;
    rep(i, zone_count)
        if (owner[i] == id)
            sum += plat_src[i];
    return sum;
}
vector<Move> search_moves(const int id, const vector<int>& start_pod_pos, const vector<int>& start_owner, const int search_turns)
{
    const int num_pods = start_pod_pos.size();

    vector<int> pos_score(zone_count);
    rep(pos, zone_count)
    {
        if (start_owner[pos] != id)
        {
            int base_score = (plat_src[pos] + 1) * (plat_src[pos] + 1);
            base_score *= ten(4);

            rep(to, zone_count)
            {
                int d = (1 + zone_dist[pos][to]);
                pos_score[to] += base_score / (d * d);
            }
        }
    }

    struct State
    {
        vector<int> pod_pos;
        vector<int> owner;

        int gain_plat;
        int gain_pos_score;

        int prev_beam_i;
        Move move;

        bool operator<(const State& other) const
        {
            return score() > other.score();
        }

    private:
        tuple<int, int> score() const
        {
            return make_tuple(gain_plat, gain_pos_score);
        }
    };

    const int beam_width = 2;

    vector<vector<int>> prev;
    vector<vector<Move>> moves;

    vector<State> cur_beam;
    priority_queue<State> next_beam;

    State start_state;
    start_state.pod_pos = start_pod_pos;
    start_state.owner = start_owner;
    start_state.gain_plat = 0;
    start_state.gain_pos_score = 0;
    start_state.prev_beam_i = -ten(9);
    cur_beam.push_back(start_state);
    rep(turn, search_turns) rep(pod_i, num_pods)
    {
        const int ite_i = turn * num_pods + pod_i;
        assert(!cur_beam.empty());

        rep(cur_beam_i, cur_beam.size())
        {
            const State& cur = cur_beam[cur_beam_i];

            for (int to : zone_link[cur.pod_pos[pod_i]])
            {
                State next = cur;
                next.pod_pos[pod_i] = to;
                next.prev_beam_i = cur_beam_i;
                if (turn == 0) // tuning
                    next.move = Move(cur.pod_pos[pod_i], to);

                if (cur.owner[to] != id)
                {
                    next.owner[to] = id;
                    next.gain_pos_score += pos_score[to];
                }

                if (pod_i == num_pods - 1)
                    next.gain_plat += count_sum_src(id, next.owner);

                if (next_beam.size() == beam_width)
                {
                    // better score?
                    if (next < next_beam.top())
                    {
                        next_beam.pop();
                        next_beam.push(next);
                    }
                }
                else
                    next_beam.push(next);
            }
        }
        assert(!next_beam.empty());

        cur_beam.clear();
        while (!next_beam.empty())
        {
            cur_beam.push_back(next_beam.top());
            next_beam.pop();
        }

        moves.push_back(vector<Move>(cur_beam.size()));
        prev.push_back(vector<int>(cur_beam.size()));
        rep(i, cur_beam.size())
        {
            prev[ite_i][i] = cur_beam[i].prev_beam_i;
            if (turn == 0)
            {
                assert(cur_beam[i].move.from != -1);
                moves[ite_i][i] = cur_beam[i].move;
            }
        }
    }

    vector<Move> res(num_pods);
    int best_beam_i = (int)cur_beam.size() - 1; // because priority_queue order
    for (int ite_i = (int)prev.size() - 1, beam_i = best_beam_i; ite_i >= 0; --ite_i)
    {
        if (ite_i < num_pods)
        {
            res[ite_i] = moves[ite_i][beam_i];
            assert(res[ite_i].from != -1);
        }
        beam_i = prev[ite_i][beam_i];
    }
    return res;
}

void test()
{
    zone_count = 4;
    vector<pint> e = {
        pint(0, 1),
        pint(1, 2),
        pint(2, 3),
    };
    for (auto& it : e)
    {
        int u = it.first;
        int v = it.second;
        zone_link[u].push_back(v);
        zone_link[v].push_back(u);
    }

    int id = 0;

    vector<int> owner(zone_count, NEAUTRAL);
    vector<int> pos = { 1, 1 };
    for (int i : pos)
        owner[i] = id;

    auto moves = search_moves(id, pos, owner, 10);
    for (auto& it : moves)
        dump(it.to_p());
}

int main()
{
    test();
    return 0;
    int player_count; // the amount of players (2 to 4)
    int my_id; // my player ID (0, 1, 2 or 3)
//     int zone_count; // the amount of zones on the map
    int linkCount; // the amount of links between all zones
    cin >> player_count >> my_id >> zone_count >> linkCount; cin.ignore();
    for (int i = 0; i < zone_count; i++) {
        int zoneId; // this zone's ID (between 0 and zone_count-1)
        int platinumSource; // the amount of Platinum this zone can provide per game turn
        cin >> zoneId >> platinumSource; cin.ignore();
        plat_src[zoneId] = platinumSource;
    }
    for (int i = 0; i < linkCount; i++) {
        int zone1;
        int zone2;
        cin >> zone1 >> zone2; cin.ignore();
        zone_link[zone1].push_back(zone2);
        zone_link[zone2].push_back(zone1);
    }

    rep(start, zone_count)
    {
        rep(i, zone_count)
            zone_dist[start][i] = inf;
        zone_dist[start][start] = 0;
        queue<int> q;
        while (!q.empty())
        {
            int pos = q.front();
            q.pop();

            for (int to : zone_link[pos])
            {
                if (zone_dist[start][to] == inf)
                {
                    zone_dist[start][to] = zone_dist[start][pos] + 1;
                    q.push(to);
                }
            }
        }
    }

    // game loop
    rep(turn, 1919810)
    {
        int platinum; // my available Platinum
        cin >> platinum; cin.ignore();

        vector<int> owner(zone_count, NEAUTRAL);
        vector<vector<int>> pods(zone_count, vector<int>(4));
        for (int i = 0; i < zone_count; i++) {
            int zId; // this zone's ID
            int ownerId; // the player who owns this zone (-1 otherwise)
            int podsP0; // player 0's PODs on this zone
            int podsP1; // player 1's PODs on this zone
            int podsP2; // player 2's PODs on this zone (always 0 for a two player game)
            int podsP3; // player 3's PODs on this zone (always 0 for a two or three player game)
            cin >> zId >> ownerId >> podsP0 >> podsP1 >> podsP2 >> podsP3; cin.ignore();

            owner[zId] = ownerId;
            pods[zId][0] += podsP0;
            pods[zId][1] += podsP1;
            pods[zId][2] += podsP2;
            pods[zId][3] += podsP3;
        }

        // Write an action using cout. DON'T FORGET THE "<< endl"
        // To debug: cerr << "Debug messages..." << endl;


        vector<vector<int>> next_pods(zone_count, vector<int>(4));
        {
//             cout << "WAIT" << endl; // first line for movement commands, second line for POD purchase (see the protocol in the statement for details)

            vector<Move> move_commands;
            rep(i, zone_count)
            {
                rep(_, pods[i][my_id])
                {
                    int next = -1;
                    for (int to : zone_link[i])
                    {
                        if (owner[to] != my_id && pods[to][my_id] == 0 && next_pods[to][my_id] == 0)
                            next = to;
                    }

                    if (next == -1)
                    {
                        int k = rand() % (zone_link[i].size() + 1);
                        if (k == zone_link[i].size())
                        {
                            ++next_pods[i][my_id];
                        }
                        else
                        {
                            ++next_pods[zone_link[i][k]][my_id];
                            move_commands.push_back(Move(i, zone_link[i][k]));
                        }
                    }
                    else
                    {
                        ++next_pods[next][my_id];
                        move_commands.push_back(Move(i, next));
                    }
                }
            }

            if (move_commands.empty())
                cout << "WAIT" << endl;
            else
            {
                for (auto& it : move_commands)
                {
                    cout << it.to_s() << " ";
                }
                cout << endl;
            }
        }

        {
            vector<pint> cand_pos;
            rep(i, zone_count)
            {
                if (owner[i] == -1 || owner[i] == my_id)
                {
                    cand_pos.push_back(pint(plat_src[i], i));
                    if (owner[i] == my_id || next_pods[i][my_id] > 0)
                        cand_pos.back().first -= 3;
                }
            }
            sort(rall(cand_pos));
            vector<pint> buy_commands;
            rep(i, min<int>(cand_pos.size(), platinum / BUY_COST))
                buy_commands.push_back(pint(1, cand_pos[i].second));
            if (buy_commands.empty())
                cout << "WAIT" << endl;
            else
            {
                for (auto& it : buy_commands)
                    cout << it.first << " " << it.second << " ";
                cout << endl;
            }
        }
    }
}
