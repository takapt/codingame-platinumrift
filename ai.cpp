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
int main()
{
    int player_count; // the amount of players (2 to 4)
    int my_id; // my player ID (0, 1, 2 or 3)
    int zone_count; // the amount of zones on the map
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

    // game loop
    rep(turn, 1919810)
    {
        int platinum; // my available Platinum
        cin >> platinum; cin.ignore();

        vector<int> owner(zone_count, 114514);
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

            vector<tuple<int, int, int>> move_commands;
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
                            move_commands.emplace_back(1, i, zone_link[i][k]);
                        }
                    }
                    else
                    {
                        ++next_pods[next][my_id];
                        move_commands.emplace_back(1, i, next);
                    }
                }
            }

            if (move_commands.empty())
                cout << "WAIT" << endl;
            else
            {
                for (auto& it : move_commands)
                {
                    int a, b, c;
                    tie(a, b, c) = it;
                    cout << a << " " << b << " " << c << " ";
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
