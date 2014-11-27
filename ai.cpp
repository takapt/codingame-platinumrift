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


#ifdef _MSC_VER
#include <Windows.h>
#else
#include <sys/time.h>
#endif
class Timer
{
    typedef double time_type;
    typedef unsigned int skip_type;

private:
    time_type start_time;
    time_type elapsed;

#ifdef _MSC_VER
    time_type get_ms() { return (time_type)GetTickCount64() / 1000; }
#else
    time_type get_ms() { struct timeval t; gettimeofday(&t, NULL); return (time_type)t.tv_sec * 1000 + (time_type)t.tv_usec / 1000; }
#endif

public:
    Timer() {}

    void start() { start_time = get_ms(); }
    time_type get_elapsed() { return elapsed = get_ms() - start_time; }
};




const int MAX_ZONE_COUNT = 256;
const int BUY_COST = 20;

int plat_src[MAX_ZONE_COUNT];
vector<int> zone_link[MAX_ZONE_COUNT];

const int NEAUTRAL = -1;
const int inf = ten(8);

int zone_count;

int zone_dist[MAX_ZONE_COUNT][MAX_ZONE_COUNT];

struct Land;
vector<Land> lands;

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

struct Land
{
    vector<int> pos;

    bool perfect(int id, const vector<int>& owner)
    {
        for (int i : pos)
            if (owner[i] != id)
                return false;
        return true;
    }

    vector<int> can_buy_pos(int id, const vector<int>& owner)
    {
        vector<int> p;
        for (int i : pos)
            if (owner[i] == id || owner[i] == NEAUTRAL)
                p.push_back(i);
        return p;
    }

    vector<int> list_pods_pos(int id, const vector<vector<int>>& pods)
    {
        vector<int> p;
        for (int i : pos)
        {
            rep(j, pods[i][id])
                p.push_back(i);
        }
        return p;
    }
};
vector<Land> list_lands()
{
    vector<Land> lands;
    vector<bool> visit(zone_count);
    rep(s, zone_count)
    {
        if (!visit[s])
        {
            vector<int> ps;

            queue<int> q;
            q.push(s);
            visit[s] = true;
            while (!q.empty())
            {
                int p = q.front();
                q.pop();

                ps.push_back(p);

                for (int to : zone_link[p])
                {
                    if (!visit[to])
                    {
                        q.push(to);
                        visit[to] = true;
                    }
                }
            }

            Land land;
            land.pos = ps;
            lands.push_back(land);
        }
    }
    return lands;
}

vector<Move> search_moves(const int id, const vector<int>& start_pod_pos, const vector<int>& start_owner, const int search_turns, const int beam_width)
{
    const int num_pods = start_pod_pos.size();
    if (num_pods == 0)
        return {};

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


//     rep(i, zone_count)
//     {
//         fprintf(stderr, "%3d (%2d): %5d %5d\n", i, start_owner[i], plat_src[i], pos_score[i]);
//         fprintf(stderr, "%3d -> %3d: %5d\n", start_pod_pos[0], i, zone_dist[start_pod_pos[0]][i]);
//     }

    typedef bitset<MAX_ZONE_COUNT> Own;
    Own start_own;
    rep(i, zone_count)
        start_own[i] = start_owner[i] == id;

    struct State
    {
        vector<int> pod_pos;
//         vector<int> owner;
        Own own;

        int gain_plat;
        int sum_gain_plat;
        int gain_pos_score;
        int cur_sum_pos_score;

        int prev_beam_i;
        Move move;

        bool operator<(const State& other) const
        {
            return score() > other.score();
        }

        tuple<int, int, int, int> score() const
        {
            return make_tuple(sum_gain_plat, gain_plat, gain_pos_score, cur_sum_pos_score);
        }
    };

    vector<vector<int>> prev;
    vector<vector<Move>> moves;

    vector<State> cur_beam;
    priority_queue<State> next_beam;

    State start_state;
    start_state.pod_pos = start_pod_pos;
//     start_state.owner = start_owner;
    start_state.own = start_own;
    start_state.gain_plat = 0;
    start_state.sum_gain_plat = 0;
    start_state.gain_pos_score = 0;
    start_state.cur_sum_pos_score = 0;
    start_state.prev_beam_i = -ten(9);
    cur_beam.push_back(start_state);
    rep(turn, search_turns) rep(pod_i, num_pods)
    {
        const int ite_i = turn * num_pods + pod_i;
        assert(!cur_beam.empty());

        rep(cur_beam_i, cur_beam.size())
        {
            const State& cur = cur_beam[cur_beam_i];
//             dump(cur.score());
            auto tup = cur.score();
//             fprintf(stderr, "cur (%d %d %d), %5d %5d %5d\n", turn, pod_i, cur_beam_i, get<0>(tup), get<1>(tup), get<2>(tup));

            for (int to : zone_link[cur.pod_pos[pod_i]])
            {
                State next = cur;
                next.pod_pos[pod_i] = to;
                next.prev_beam_i = cur_beam_i;
                if (turn == 0) // tuning
                    next.move = Move(cur.pod_pos[pod_i], to);

//                 if (cur.owner[to] != id)
                if (!cur.own[to])
                {
//                     next.owner[to] = id;
                    next.own[to] = true;
                    next.gain_plat += plat_src[to];
                    next.gain_pos_score += pos_score[to];
                }
                next.cur_sum_pos_score += pos_score[to];

                if (next_beam.size() == beam_width)
                {
                    if (next.score() > next_beam.top().score())
                    {
                        auto tup = next_beam.top().score();
//                         fprintf(stderr, "pop %5d %5d %5d\n", get<0>(tup), get<1>(tup), get<2>(tup));
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

            cur_beam[i].sum_gain_plat += cur_beam[i].gain_plat;
            cur_beam[i].cur_sum_pos_score = 0;
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

vector<bool> all_own(int id, const vector<int>& own)
{
    vector<bool> seen(zone_count);
    vector<bool> res(zone_count);
    rep(i, zone_count)
    {
        if (!seen[i])
        {
            bool f = true;
            rep(j, zone_count)
                if (zone_dist[i][j] != inf)
                    f &= own[j] == id;
            rep(j, zone_count)
                if (zone_dist[i][j] != inf)
                    res[j] = f;
        }
    }
    return res;
}

int main()
{
    int player_count; // the amount of players (2 to 4)
    int my_id; // my player ID (0, 1, 2 or 3)
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
        q.push(start);
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

    ::lands = list_lands();

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


        {

            vector<Move> moves;
            vector<int> pods_pos;
            for (Land& land : lands)
            {
                if (!land.perfect(my_id, owner))
                {
                    vector<int> land_pods_pos = land.list_pods_pos(my_id, pods);
                    pods_pos.insert(pods_pos.end(), all(land_pods_pos));
//                     continue;
//
//                     int beam_width;
//                     if (land.pos.size() < 10)
//                         beam_width = 5;
//                     else
//                     {
//                         if (land_pods_pos.size() < 5)
//                             beam_width = 30;
//                         else if (land_pods_pos.size() < 10)
//                             beam_width = 15;
//                         else
//                             beam_width = 5;
//                     }
//
//                     int search_turns = 5;
//                     if (land_pods_pos.size() >= 10)
//                         search_turns = 3;
//
//                     vector<Move> land_moves = search_moves(my_id, land_pods_pos, owner, search_turns, beam_width);
//                     moves.insert(moves.end(), all(land_moves));
                }
            }

            {
                int beam_width = 30;
                int search_turns = 5;
                if (pods_pos.size() >= 20)
                {
                    beam_width = 2;
                    search_turns = 1;
                }
                else if (pods_pos.size() >= 10)
                {
                    beam_width = 20;
                    search_turns = 5;
                }
//                 else if (pods_pos.size() >= 5)
//                 {
//                 }

                Timer timer;
                timer.start();
                moves = search_moves(my_id, pods_pos, owner, search_turns, beam_width);
                fprintf(stderr, "%3d: %3d, %3d: %f\n", (int)pods_pos.size(), search_turns, beam_width, timer.get_elapsed());
            }

            if (moves.empty())
                cout << "WAIT" << endl;
            else
            {
                for (auto& move : moves)
                {
                    cout << move.to_s() << " ";
                }
                cout << endl;
            }
        }

        {
            const auto next_pods = pods;
            const auto is_all_own = all_own(my_id, owner);

            vector<int> zones;
            if (turn == 0)
            {
                vector<int> sum_plat_src(lands.size());
                rep(land_i, lands.size())
                {
                    Land& land = lands[land_i];

                    int sum = 0;
                    for (int i : land.pos)
                        sum += plat_src[i];
                    sum_plat_src[land_i] = sum;
                }
                int max_land_i = max_element(all(sum_plat_src)) - sum_plat_src.begin();
                zones = lands[max_land_i].pos;
            }
            else
            {
//                 rep(i, zone_count)
//                     zones.push_back(i);
                for (Land& land : lands)
                {
                    if (!land.perfect(my_id, owner))
                    {
                        vector<vector<int>> land_pods(player_count);
                        rep(id, player_count)
                            land_pods[id] = land.list_pods_pos(id, pods);

                        vector<int> num_pods(player_count);
                        rep(id, player_count)
                            num_pods[id] = land_pods[id].size();

                        int max_ene_num_pods = -1;
                        rep(id, player_count)
                            if (id != my_id)
                                upmax(max_ene_num_pods, num_pods[id]);

                        if (max_ene_num_pods + land.pos.size() / 2 >= num_pods[my_id])
                        {
                            auto p = land.can_buy_pos(my_id, owner);
                            zones.insert(zones.end(), all(p));
                        }
                    }
                }
            }

            vector<tuple<int, int, int>> cand_pos;
            for (int i : zones)
            {
                if (!is_all_own[i])
                {
                    tuple<int, int, int> add(-1, -1, -1);

                    if (owner[i] == NEAUTRAL)
                    {
//                         cand_pos.push_back(make_tuple(plat_src[i], i, turn == 0 ? 2 : 1));
                        add = make_tuple(plat_src[i], i, turn == 0 ? 2 : 1);
                        if (next_pods[i][my_id] > 0)
                            get<0>(add) -= 3;
                    }
                    else if (owner[i] == my_id)
                    {
                        int around_ene = 0;
                        for (int j : zone_link[i]) rep(id, player_count)
                            if (id != my_id && pods[j][id])
                                around_ene += pods[j][id];
                        if (around_ene > 0)
                        {
                            int need = around_ene;
//                             cand_pos.push_back(make_tuple(plat_src[i], i, need));
                            add = make_tuple(plat_src[i], i, need);
                        }
                    }

                    if (get<0>(add) != -1)
                    {
                        for (int j : zone_link[i])
                            if (owner[j] != NEAUTRAL && owner[j] != my_id)
                                upmax(get<0>(add), plat_src[i]);

                        cand_pos.push_back(add);
                    }
                }
            }
            sort(rall(cand_pos));
            vector<pint> buy_commands;
            int rem = platinum;
            while (rem > 0)
            {
                for (auto& it : cand_pos)
                {
                    if (rem == 0)
                        break;
                    int num = min(rem, get<2>(it));
                    buy_commands.push_back(pint(num, get<1>(it)));
                    rem -= num;
                }
            }

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

