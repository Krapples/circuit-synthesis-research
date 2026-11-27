// See regional_kernel.hpp.  Comments name the Python reference lines they mirror
// (theory/regional_block_completion.py, local_blocks with production flags).
#include "regional_kernel.hpp"

#include <algorithm>
#include <bit>
#include <list>
#include <memory>
#include <optional>
#include <span>
#include <unordered_map>
#include <unordered_set>

namespace regional {
namespace {

struct Aborted {};
struct WorkLimit {};

template <int W>
struct Tab {
    std::array<uint64_t, W> w{};
    bool operator==(const Tab& o) const { return w == o.w; }
    bool operator!=(const Tab& o) const { return w != o.w; }
    Tab operator&(const Tab& o) const { Tab r; for (int i = 0; i < W; ++i) r.w[i] = w[i] & o.w[i]; return r; }
    Tab operator|(const Tab& o) const { Tab r; for (int i = 0; i < W; ++i) r.w[i] = w[i] | o.w[i]; return r; }
    Tab operator^(const Tab& o) const { Tab r; for (int i = 0; i < W; ++i) r.w[i] = w[i] ^ o.w[i]; return r; }
    Tab andnot(const Tab& o) const { Tab r; for (int i = 0; i < W; ++i) r.w[i] = w[i] & ~o.w[i]; return r; }
    bool nonzero() const { for (int i = 0; i < W; ++i) if (w[i]) return true; return false; }
    bool test(int bit) const { return (w[bit >> 6] >> (bit & 63)) & 1; }
    void set(int bit) { w[bit >> 6] |= uint64_t(1) << (bit & 63); }
    Tab shr(unsigned s) const {
        Tab r; const unsigned ws = s >> 6, bs = s & 63;
        for (int i = 0; i < W; ++i) {
            const unsigned src = i + ws;
            if (src >= unsigned(W)) continue;
            uint64_t v = w[src] >> bs;
            if (bs && src + 1 < unsigned(W)) v |= w[src + 1] << (64 - bs);
            r.w[i] = v;
        }
        return r;
    }
    Tab shl(unsigned s) const {
        Tab r; const unsigned ws = s >> 6, bs = s & 63;
        for (int i = 0; i < W; ++i) {
            if (unsigned(i) < ws) continue;
            uint64_t v = w[i - ws] << bs;
            if (bs && unsigned(i) >= ws + 1) v |= w[i - ws - 1] >> (64 - bs);
            r.w[i] = v;
        }
        return r;
    }
};

using Key = std::vector<uint64_t>;
using KeyView = std::span<const uint64_t>;
struct KeyHash {
    using is_transparent = void;
    size_t operator()(const Key& k) const { return (*this)(KeyView(k)); }
    size_t operator()(KeyView k) const {
        uint64_t h = 0x9E3779B97F4A7C15ull ^ k.size();
        for (uint64_t x : k) {
            x += 0x9E3779B97F4A7C15ull + (h << 6) + (h >> 2);
            x ^= x >> 30; x *= 0xBF58476D1CE4E5B9ull; x ^= x >> 27; x *= 0x94D049BB133111EBull; x ^= x >> 31;
            h ^= x;
        }
        return size_t(h);
    }
};

struct KeyEq {
    using is_transparent = void;
    bool operator()(KeyView a, KeyView b) const { return std::equal(a.begin(), a.end(), b.begin(), b.end()); }
    bool operator()(const Key& a, const Key& b) const { return a == b; }
    bool operator()(const Key& a, KeyView b) const { return (*this)(KeyView(a), b); }
    bool operator()(KeyView a, const Key& b) const { return (*this)(a, KeyView(b)); }
};

// Bounded LRU with the observable behaviour of functools.lru_cache(maxsize): hit -> most recent;
// miss -> computed, then inserted (evicting the least recent entry when full).  Lookups take a view of a scratch
// key (no allocation); only inserts copy the key.
template <class V>
struct Lru {
    size_t cap;
    std::list<std::pair<Key, V>> order;  // front = most recent
    std::unordered_map<Key, typename std::list<std::pair<Key, V>>::iterator, KeyHash, KeyEq> map;
    explicit Lru(size_t c) : cap(c) { map.reserve(c * 2); }
    const V* get(KeyView k) {
        auto it = map.find(k);
        if (it == map.end()) return nullptr;
        order.splice(order.begin(), order, it->second);
        return &it->second->second;
    }
    void put(KeyView kv, V v) {
        if (map.find(kv) != map.end()) return;  // inserted during its own computation (cannot happen here)
        Key k(kv.begin(), kv.end());
        if (map.size() >= cap && !order.empty()) {
            map.erase(order.back().first);
            order.pop_back();
        }
        order.emplace_front(std::move(k), std::move(v));
        map.emplace(order.front().first, order.begin());
    }
};

template <int W, int R>
struct Obls {
    uint64_t any = 0;               // bit row set = ANY
    std::array<Tab<W>, R> v{};      // value per row (zero where ANY); rows >= n unused
};

using Counts = std::array<uint8_t, MAX_PROVIDERS>;

template <int W, int R>
class Engine {
   public:
    using T = Tab<W>;
    using O = Obls<W, R>;
    explicit Engine(const Query& q) : q_(q) {
        m_ = q.m; P_ = int(q.provider_ids.size()); n_ = int(q.pats.size());
        full_ = (1u << m_) - 1;
        const int bits = 1 << m_;
        for (int b = 0; b < bits; ++b) one_.set(b);
        last_.set(bits - 1);
        for (int i = 0; i < m_; ++i) {
            T c;
            for (int b = 0; b < bits; ++b) if (b >> i & 1) c.set(b);
            col_[i] = c;
            low_[i] = one_ ^ c;
        }
        all_rows_ = n_ == 64 ? ~uint64_t(0) : (uint64_t(1) << n_) - 1;
        targets_.any = 0;
        for (int r = 0; r < n_; ++r) {
            if (q.target_any[r]) { targets_.any |= uint64_t(1) << r; continue; }
            for (int k = 0; k < W; ++k) targets_.v[r].w[k] = q.target_words[4 * r + k];
        }
        for (int i = 0; i < m_; ++i) { forced_[0][i] = q.forced_and[i]; forced_[1][i] = q.forced_or[i]; }
        exposed_state_.assign(size_t(n_) << m_, 0);
        exposed_value_.resize(size_t(n_) << m_);
    }

    Result run() {
        Result res;
        Counts avail{};
        for (int p = 0; p < P_; ++p) avail[p] = uint8_t(q_.counts[p]);
        try {
            const int root = solve(full_, avail, targets_);
            res.root = root;
            res.status = root >= 0 ? Status::SAT : Status::UNSAT;
        } catch (const Aborted&) {
            res.status = Status::ABORTED;
        } catch (const WorkLimit&) {
            res.status = Status::WORK_LIMIT;
        }
        stats_.peak_cache_entries = int64_t(complete_cache_.map.size());
        res.stats = stats_;
        res.nodes = std::move(nodes_);
        return res;
    }

   private:
    const Query& q_;
    int m_, P_, n_;
    uint32_t full_;
    T one_, last_;
    std::array<T, MAX_M> col_{}, low_{};
    uint64_t all_rows_;
    O targets_;
    uint32_t forced_[2][MAX_M]{};  // [0] = forced['&'], [1] = forced['|']
    Stats stats_;
    std::vector<Node> nodes_;
    Lru<int> complete_cache_{8192};
    Lru<std::optional<O>> canonical_cache_{4096};
    std::unordered_map<uint32_t, std::vector<uint32_t>> components_[2];
    struct RowOrder { uint64_t zero = 0, high = 0; std::vector<uint64_t> supers; };  // supers[i]: j != i, rows[i] ⊆ rows[j]
    std::unordered_map<uint32_t, RowOrder> row_order_;
    std::unordered_map<uint32_t, std::vector<uint64_t>> ordered_rows_[2];
    std::vector<uint8_t> exposed_state_;  // 0 unknown, 1 None, 2 value
    std::vector<T> exposed_value_;

    // ---- work accounting: charge() in the reference, plus cooperative polling
    void charge() {
        ++stats_.work;
        if (q_.work_limit >= 0 && stats_.work > q_.work_limit) throw WorkLimit{};
        if (stats_.work % POLL_INTERVAL == 0 && q_.poll && q_.poll()) throw Aborted{};
    }

    // ---- PackedTables
    uint32_t support(const T& t) const {
        uint32_t s = 0;
        for (int i = 0; i < m_; ++i)
            if (((t ^ t.shr(1u << i)) & low_[i]).nonzero()) s |= 1u << i;
        return s;
    }
    T project(T t, uint32_t inside, bool exists) const {
        uint32_t outside = full_ ^ inside;
        while (outside) {
            const int axis = std::countr_zero(outside);
            outside &= outside - 1;
            const unsigned s = 1u << axis;
            const T swapped = (t & low_[axis]).shl(s) | (t & col_[axis]).shr(s);
            t = exists ? (t | swapped) : (t & swapped);
        }
        return t;
    }
    // exposed(row, inside) on the ORIGINAL targets (as the reference)
    const T* exposed(int row, uint32_t inside) {
        const size_t idx = (size_t(row) << m_) | inside;
        if (exposed_state_[idx] == 0) {
            exposed_state_[idx] = 1;
            const T& t = targets_.v[row];
            if (!inside || !t.nonzero() || t == one_) {
            } else if (inside == full_) {
                exposed_state_[idx] = 2; exposed_value_[idx] = t;
            } else {
                const uint32_t outside = full_ ^ inside;
                const T active = project(t, outside, true).andnot(project(t, outside, false));
                if (active.nonzero()) {
                    const T cand = project(t & active, inside, true);
                    if (!((t ^ cand) & active).nonzero()) { exposed_state_[idx] = 2; exposed_value_[idx] = cand; }
                }
            }
        }
        return exposed_state_[idx] == 2 ? &exposed_value_[idx] : nullptr;
    }

    uint32_t port_mask(const Counts& a) const {
        uint32_t mask = 0;
        for (int p = 0; p < P_; ++p) if (a[p]) mask |= 1u << p;
        return mask;
    }

    const std::vector<uint32_t>& components(uint32_t primary, int opi) {
        auto& memo = components_[opi];
        auto it = memo.find(primary);
        if (it != memo.end()) return it->second;
        const uint32_t* edges = forced_[opi == 0 ? 1 : 0];   // forced['|'] for '&', forced['&'] for '|'
        std::vector<uint32_t> groups;
        uint32_t remaining = primary;
        while (remaining) {
            uint32_t block = remaining & (0u - remaining), pending = block;
            while (pending) {
                const uint32_t bit = pending & (0u - pending);
                pending ^= bit;
                const uint32_t adjacent = edges[std::countr_zero(bit)] & remaining & ~block;
                block |= adjacent;
                pending |= adjacent;
            }
            groups.push_back(block);
            remaining ^= block;
        }
        return memo.emplace(primary, std::move(groups)).first->second;
    }

    const RowOrder& row_order(uint32_t mask) {
        auto it = row_order_.find(mask);
        if (it != row_order_.end()) return it->second;
        RowOrder ro; ro.supers.assign(n_, 0);
        for (int i = 0; i < n_; ++i) {
            const uint32_t a = q_.pats[i] & mask;
            if (a == 0) ro.zero |= uint64_t(1) << i;
            if (a == mask) ro.high |= uint64_t(1) << i;
            for (int j = 0; j < n_; ++j)
                if (i != j && (a & (q_.pats[j] & mask)) == a) ro.supers[i] |= uint64_t(1) << j;
        }
        return row_order_.emplace(mask, std::move(ro)).first->second;
    }

    const std::vector<uint64_t>& ordered_rows(uint32_t mask, bool is_and) {
        auto& memo = ordered_rows_[is_and ? 0 : 1];
        auto it = memo.find(mask);
        if (it != memo.end()) return it->second;
        const RowOrder& ro = row_order(mask);
        std::vector<uint64_t> comparable(n_, 0);
        for (int lo = 0; lo < n_; ++lo)
            for (uint64_t s = ro.supers[lo]; s; s &= s - 1) {
                const int hi = std::countr_zero(s);
                if (is_and) comparable[hi] |= uint64_t(1) << lo;
                else comparable[lo] |= uint64_t(1) << hi;
            }
        return memo.emplace(mask, std::move(comparable)).first->second;
    }

    // ---- nodes
    int leaf(int id, bool neg, int compact_provider) {
        Node nd{'x', id, int(neg), 0, all_rows_};
        if (compact_provider >= 0) {
            uint64_t values = 0;
            for (int r = 0; r < n_; ++r)
                values |= uint64_t(((q_.pats[r] >> compact_provider) & 1) ^ uint32_t(neg)) << r;
            nd.lo = nd.hi = values;
        }
        nodes_.push_back(nd);
        return int(nodes_.size()) - 1;
    }
    int internal(bool is_and, int a, int b) {
        const Node& x = nodes_[a];
        const Node& y = nodes_[b];
        Node nd{is_and ? '&' : '|', a, b, is_and ? (x.lo & y.lo) : (x.lo | y.lo), is_and ? (x.hi & y.hi) : (x.hi | y.hi)};
        nodes_.push_back(nd);
        return int(nodes_.size()) - 1;
    }

    // ---- keys
    Key scratch_;   // reused lookup key (lookups never recurse while the key is in use)

    void push_obls(Key& k, const O& ob) const {
        k.push_back(ob.any);
        for (int r = 0; r < n_; ++r)
            if (!(ob.any >> r & 1)) for (int i = 0; i < W; ++i) k.push_back(ob.v[r].w[i]);
    }
    void complete_key(Key& k, uint32_t primary, const Counts& a, const O& ob) const {
        k.clear();
        k.push_back(primary);
        for (int base = 0; base < P_; base += 8) {
            uint64_t c = 0;
            for (int p = base; p < base + 8 && p < P_; ++p) c |= uint64_t(a[p]) << (8 * (p - base));
            k.push_back(c);
        }
        push_obls(k, ob);
    }

    // ---- row quotient (regional_row_quotient.quotient_rows on observed_patterns(mask))
    std::optional<O> quotient(uint32_t mask, const O& ob) const {
        O kept; kept.any = all_rows_;
        std::vector<std::pair<uint32_t, int>> requested;  // insertion order: pattern -> row
        for (int r = 0; r < n_; ++r) {
            if (ob.any >> r & 1) continue;
            const uint32_t pattern = q_.pats[r] & mask;
            auto it = std::find_if(requested.begin(), requested.end(), [&](auto& e) { return e.first == pattern; });
            if (it != requested.end()) {
                if (ob.v[r] != kept.v[it->second]) return std::nullopt;
            } else {
                requested.emplace_back(pattern, r);
                kept.any &= ~(uint64_t(1) << r);
                kept.v[r] = ob.v[r];
            }
        }
        if (!q_.is_signed) {
            for (int pass = 0; pass < 2; ++pass) {
                const T value = pass == 0 ? T{} : one_;
                std::vector<std::pair<uint32_t, int>> matching;
                for (auto& e : requested)
                    if (kept.v[e.second] == value && !(kept.any >> e.second & 1)) matching.push_back(e);
                std::stable_sort(matching.begin(), matching.end(), [&](auto& x, auto& y) {
                    const int a = std::popcount(x.first), b = std::popcount(y.first);
                    return pass == 0 ? a > b : a < b;
                });
                std::vector<uint32_t> extremal;
                for (auto& [pattern, row] : matching) {
                    bool dominated = false;
                    for (uint32_t prior : extremal)
                        if ((pattern & prior) == (pass == 0 ? pattern : prior)) { dominated = true; break; }
                    if (dominated) { kept.any |= uint64_t(1) << row; kept.v[row] = T{}; }
                    else extremal.push_back(pattern);
                }
            }
        }
        return kept;
    }

    int solve(uint32_t primary, const Counts& a, const O& ob) {
        if (!q_.row_quotient) return complete(primary, a, ob);
        const uint32_t mask = port_mask(a);
        Key& k = scratch_;
        k.clear(); k.push_back(mask); push_obls(k, ob);
        if (const auto* hit = canonical_cache_.get(k)) {
            if (!*hit) return -1;
            const O normalized = **hit;  // copy: the recursion may evict the entry
            return complete(primary, a, normalized);
        }
        auto normalized = quotient(mask, ob);
        if (!normalized) ++stats_.quotient_conflicts;
        else stats_.quotient_dropped += std::popcount(normalized->any) - std::popcount(ob.any);
        canonical_cache_.put(k, normalized);
        if (!normalized) return -1;
        return complete(primary, a, *normalized);
    }

    int complete(uint32_t primary, const Counts& a, const O& ob) {
        complete_key(scratch_, primary, a, ob);
        if (const int* hit = complete_cache_.get(scratch_)) { ++stats_.complete_cache_hits; return *hit; }
        const int r = complete_impl(primary, a, ob);
        complete_key(scratch_, primary, a, ob);   // the recursion reused the scratch key
        complete_cache_.put(scratch_, r);
        return r;
    }

    bool endpoint_allows(bool any, const T& target, uint32_t pattern, uint32_t mask) const {
        if (any) return true;
        pattern &= mask;
        return (pattern != 0 || !target.test(0)) && (pattern != mask || target.test((1 << m_) - 1));
    }

    struct Pair { bool a_any, b_any; T a, b; };
    struct Options { int count; Pair p[2]; };

    int complete_impl(uint32_t primary, const Counts& avail, const O& ob) {
        charge();
        ++stats_.rec;
        int size = std::popcount(primary);
        for (int p = 0; p < P_; ++p) size += avail[p];
        if (!size) return -1;
        // Reuse each exact row's support in both root operations. An absorbing target
        // constrains the witness cover instead of imposing a support demand.
        const uint64_t requested = all_rows_ & ~ob.any;
        uint64_t exact_rows[2] = {requested, requested};  // AND, OR
        std::array<uint32_t, R> row_support;
        for (uint64_t rows = requested; rows; rows &= rows - 1) {
            const int r = std::countr_zero(rows);
            const T& target = ob.v[r];
            if (!target.nonzero()) {
                row_support[r] = 0;
                exact_rows[0] &= ~(uint64_t(1) << r);
            } else if (target == one_) {
                row_support[r] = 0;
                exact_rows[1] &= ~(uint64_t(1) << r);
            } else {
                row_support[r] = support(target);
                if (row_support[r] & ~primary) return -1;
            }
        }
        if (!q_.is_signed) {  // row_filter
            const RowOrder& ro = row_order(port_mask(avail));
            bool reject = false;
            for (uint64_t s = ro.zero & ~ob.any; s && !reject; s &= s - 1)
                if (ob.v[std::countr_zero(s)].test(0)) reject = true;
            const int top = (1 << m_) - 1;
            for (uint64_t s = ro.high & ~ob.any; s && !reject; s &= s - 1)
                if (!ob.v[std::countr_zero(s)].test(top)) reject = true;
            for (uint64_t s = ~ob.any & all_rows_; s && !reject; s &= s - 1) {
                const int i = std::countr_zero(s);
                for (uint64_t u = ro.supers[i] & ~ob.any; u; u &= u - 1)
                    if (ob.v[i].andnot(ob.v[std::countr_zero(u)]).nonzero()) { reject = true; break; }
            }
            if (reject) { ++stats_.row_reject; return -1; }
        }
        if (q_.module_filter) {
            for (int r = 0; r < n_; ++r) {
                if (ob.any >> r & 1) continue;
                const T& t = ob.v[r];
                if (!t.nonzero() || t == one_) continue;
                const T* e = exposed(r, primary);
                if (!e || *e != t) { ++stats_.module_reject; return -1; }
            }
        }
        if (size == 1) {
            int id, compact = -1;
            std::vector<T> values(n_);
            if (primary) {
                const int i = 31 - std::countl_zero(primary);
                id = i;
                for (int r = 0; r < n_; ++r) values[r] = col_[i];
            } else {
                int p = 0;
                while (!avail[p]) ++p;
                compact = p;
                id = m_ + q_.provider_ids[p];
                for (int r = 0; r < n_; ++r) values[r] = (q_.pats[r] >> p & 1) ? one_ : T{};
            }
            int phases[2], nph = 0;
            if (id < m_ && q_.phase[id] >= 0) phases[nph++] = q_.phase[id];
            else { phases[nph++] = 0; if (q_.is_signed) phases[nph++] = 1; }
            for (int k = 0; k < nph; ++k) {
                const bool neg = phases[k] != 0;
                bool ok = true;
                for (int r = 0; r < n_ && ok; ++r)
                    if (!(ob.any >> r & 1) && ob.v[r] != (neg ? values[r] ^ one_ : values[r])) ok = false;
                if (ok) return leaf(id, neg, compact);
            }
            return -1;
        }
        for (int opi = 0; opi < 2; ++opi) {
            const int found = port_partitions(primary, avail, opi, ob, exact_rows[opi], row_support);
            if (found >= 0) return found;
        }
        return -1;
    }

    // port_partitions(...) generator fused with the consuming loop of complete(); returns a node id or -1.
    int port_partitions(uint32_t primary, const Counts& avail, int opi, const O& ob, uint64_t exact_rows,
                        const std::array<uint32_t, R>& row_support) {
        const bool is_and = opi == 0;
        const std::vector<uint32_t> blocks = components(primary, opi);  // copy: memo may rehash in recursion
        int port_anchor = -1;
        if (blocks.empty())
            for (int p = 0; p < P_; ++p) if (avail[p]) { port_anchor = p; break; }
        Counts lo{}, taking{};
        for (int p = 0; p < P_; ++p) taking[p] = lo[p] = uint8_t(p == port_anchor);
        std::vector<uint32_t> hits_left, hits_right, free;
        while (true) {
            charge();
            ++stats_.port_allocations;
            Counts remaining{};
            bool any_taking = false, any_remaining = false;
            for (int p = 0; p < P_; ++p) {
                remaining[p] = uint8_t(avail[p] - taking[p]);
                any_taking |= taking[p] != 0;
                any_remaining |= remaining[p] != 0;
            }
            const uint32_t left_mask = port_mask(taking), right_mask = port_mask(remaining);
            const uint32_t forbid_left = support_demands(left_mask, exact_rows, row_support, is_and, hits_left);
            const uint32_t forbid_right = support_demands(right_mask, exact_rows, row_support, is_and, hits_right);
            const uint32_t force_left = forbid_right | (blocks.empty() ? 0u : blocks[0]);
            free.clear();
            uint32_t left = 0, right = 0;
            bool broke = false;
            for (uint32_t block : blocks) {
                if (block & force_left) {
                    if (block & forbid_left) { broke = true; break; }
                    left |= block;
                } else if (block & forbid_left) {
                    right |= block;
                } else {
                    free.push_back(block);
                }
            }
            bool accepted = false;
            if (!broke) {
                bool ok = true;
                for (uint32_t hit : hits_left) if (!(hit & (primary ^ right))) { ok = false; break; }
                if (ok) for (uint32_t hit : hits_right) if (!(hit & (primary ^ left))) { ok = false; break; }
                if (ok) {
                    accepted = true;
                    const size_t nf = free.size();
                    const uint64_t combos = uint64_t(1) << nf;
                    for (uint64_t c = 0; c < combos; ++c) {  // product(*((0, block) ...)): free[0] varies slowest
                        uint32_t inside = left;
                        for (size_t f = 0; f < nf; ++f)
                            if (c >> (nf - 1 - f) & 1) inside |= free[f];
                        const uint32_t outside = primary ^ inside;
                        if (!((any_taking || inside) && (any_remaining || outside))) continue;
                        bool hok = true;
                        for (uint32_t hit : hits_left) if (!(hit & inside)) { hok = false; break; }
                        if (hok) for (uint32_t hit : hits_right) if (!(hit & outside)) { hok = false; break; }
                        if (!hok) continue;
                        const int found = split(primary, inside, taking, remaining, is_and, ob);
                        if (found >= 0) return found;
                    }
                }
            }
            if (!accepted) ++stats_.port_allocation_reject;
            // next taking: itertools.product order (last provider varies fastest)
            int p = P_ - 1;
            while (p >= 0) {
                if (taking[p] < avail[p]) { ++taking[p]; break; }
                taking[p] = lo[p];
                --p;
            }
            if (p < 0) return -1;
        }
    }

    uint32_t support_demands(uint32_t mask, uint64_t exact_rows, const std::array<uint32_t, R>& row_support,
                             bool is_and, std::vector<uint32_t>& hits) const {
        uint32_t forbidden = 0;
        std::pair<uint32_t, uint32_t> first[MAX_ROWS];
        int nfirst = 0;
        hits.clear();
        for (uint64_t rows = exact_rows; rows; rows &= rows - 1) {
            const int row = std::countr_zero(rows);
            const uint32_t required = row_support[row];
            const uint32_t pattern = q_.pats[row] & mask;
            int f = 0;
            while (f < nfirst && first[f].first != pattern) ++f;
            if (f == nfirst) first[nfirst++] = {pattern, required};
            forbidden |= required ^ first[f].second;
            if (!q_.is_signed && pattern == (is_and ? 0u : mask))
                if (std::find(hits.begin(), hits.end(), required) == hits.end()) hits.push_back(required);
        }
        return forbidden;
    }

    // body of `for left, taking in splits:` in complete()
    int split(uint32_t primary, uint32_t left, const Counts& taking, const Counts& remaining, bool is_and,
              const O& ob) {
        ++stats_.partition_checks;
        const uint32_t right = primary ^ left;
        const T absorbing = is_and ? T{} : one_;
        const T neutral = one_ ^ absorbing;
        const bool endpoint_test = !q_.is_signed;
        const uint32_t left_ports = port_mask(taking), right_ports = port_mask(remaining);
        std::vector<Options> options(n_);
        bool ambiguous_any = false;
        for (int r = 0; r < n_; ++r) {
            Options& o = options[r];
            const bool any = ob.any >> r & 1;
            const T& t = ob.v[r];
            if (any) {
                o.count = 1; o.p[0] = {true, true, T{}, T{}};
            } else if (t == absorbing) {
                o.count = 2; o.p[0] = {false, true, absorbing, T{}}; o.p[1] = {true, false, T{}, absorbing};
            } else if (t == neutral) {
                o.count = 1; o.p[0] = {false, false, neutral, neutral};
            } else {
                const T a = project(t, left, is_and), b = project(t, right, is_and);
                if ((is_and ? (a & b) : (a | b)) != t) return -1;
                o.count = 1; o.p[0] = {false, false, a, b};
            }
            if (endpoint_test && !any) {
                int kept = 0;
                for (int k = 0; k < o.count; ++k) {
                    const Pair& pr = o.p[k];
                    if (endpoint_allows(pr.a_any, pr.a, q_.pats[r], left_ports) &&
                        endpoint_allows(pr.b_any, pr.b, q_.pats[r], right_ports))
                        o.p[kept++] = pr;
                }
                o.count = kept;
                if (!kept) { ++stats_.endpoint_split_reject; return -1; }
            }
            ambiguous_any |= o.count > 1;
        }
        if (endpoint_test && ambiguous_any) {  // dominance_branches
            if (!prune_constant_branches(options, left_ports, right_ports, is_and, absorbing)) {
                ++stats_.dominance_split_reject;
                return -1;
            }
            ambiguous_any = false;
            for (const Options& o : options) ambiguous_any |= o.count > 1;
        }
        ++stats_.obligation_partitions;
        if (ambiguous_any) {  // witness_cover
            return cover(left, taking, right, remaining, options, is_and, absorbing);
        }
        O at, bt;
        for (int r = 0; r < n_; ++r) {
            const Pair& pr = options[r].p[0];
            if (pr.a_any) at.any |= uint64_t(1) << r; else at.v[r] = pr.a;
            if (pr.b_any) bt.any |= uint64_t(1) << r; else bt.v[r] = pr.b;
        }
        const int a = solve(left, taking, at);
        if (a >= 0) {
            const int b = solve(right, remaining, bt);
            if (b >= 0) return internal(is_and, a, b);
        }
        return -1;
    }

    bool prune_constant_branches(std::vector<Options>& options, uint32_t left_ports, uint32_t right_ports,
                                 bool is_and, const T& absorbing) {
        const std::vector<uint64_t>& rl = ordered_rows(left_ports, is_and);
        const std::vector<uint64_t>& rr = ordered_rows(right_ports, is_and);
        uint64_t opposing[2] = {0, 0};
        for (int r = 0; r < n_; ++r) {
            const Options& o = options[r];
            if (o.count != 1) continue;
            const Pair& pr = o.p[0];
            if (!pr.a_any && pr.a != absorbing) opposing[0] |= uint64_t(1) << r;
            if (!pr.b_any && pr.b != absorbing) opposing[1] |= uint64_t(1) << r;
        }
        for (int r = 0; r < n_; ++r) {
            Options& o = options[r];
            if (o.count <= 1) continue;
            int kept = 0;
            for (int k = 0; k < o.count; ++k) {
                const Pair& pr = o.p[k];
                const bool ok = (pr.a_any || !(rl[r] & opposing[0])) && (pr.b_any || !(rr[r] & opposing[1]));
                if (ok) o.p[kept++] = pr;
            }
            o.count = kept;
            if (!kept) return false;
        }
        return true;
    }

    int cover(uint32_t left, const Counts& taking, uint32_t right, const Counts& remaining,
              const std::vector<Options>& options, bool is_and, const T& absorbing) {
        O a_fixed, b_fixed;
        uint64_t ambiguous = 0;
        for (int r = 0; r < n_; ++r) {
            const Options& o = options[r];
            if (o.count == 1) {
                if (o.p[0].a_any) a_fixed.any |= uint64_t(1) << r; else a_fixed.v[r] = o.p[0].a;
                if (o.p[0].b_any) b_fixed.any |= uint64_t(1) << r; else b_fixed.v[r] = o.p[0].b;
            } else {
                a_fixed.any |= uint64_t(1) << r; b_fixed.any |= uint64_t(1) << r;
                ambiguous |= uint64_t(1) << r;
            }
        }
        std::unordered_set<uint64_t> visited;
        int a_out = -1, b_out = -1;
        if (!branch(0, visited, left, taking, right, remaining, a_fixed, b_fixed, ambiguous, is_and, absorbing,
                    a_out, b_out))
            return -1;
        return internal(is_and, a_out, b_out);
    }

    O require(const O& fixed, uint64_t rows, const T& absorbing) const {
        O r = fixed;
        for (uint64_t s = rows; s; s &= s - 1) {
            const int row = std::countr_zero(s);
            r.any &= ~(uint64_t(1) << row);
            r.v[row] = absorbing;
        }
        return r;
    }

    bool branch(uint64_t required, std::unordered_set<uint64_t>& visited, uint32_t left, const Counts& taking,
                uint32_t right, const Counts& remaining, const O& a_fixed, const O& b_fixed,
                uint64_t ambiguous, bool is_and, const T& absorbing, int& a_out, int& b_out) {
        if (visited.count(required)) return false;
        if (visited.size() < 4096) visited.insert(required);
        charge();
        ++stats_.cover_nodes;
        const int a = solve(left, taking, require(a_fixed, required, absorbing));
        if (a < 0) return false;
        const Node& na = nodes_[a];
        const uint64_t uncovered = ambiguous & (is_and ? na.hi : ~na.lo);
        const int b = solve(right, remaining, require(b_fixed, uncovered, absorbing));
        if (b >= 0) { a_out = a; b_out = b; return true; }
        for (uint64_t s = uncovered; s; s &= s - 1) {
            const int row = std::countr_zero(s);
            if (branch(required | (uint64_t(1) << row), visited, left, taking, right, remaining, a_fixed, b_fixed,
                       ambiguous, is_and, absorbing, a_out, b_out))
                return true;
        }
        return false;
    }
};

void validate(const Query& q) {
    if (q.m < 0 || q.m > MAX_M) throw std::invalid_argument("m out of native range");
    const size_t P = q.provider_ids.size(), n = q.pats.size();
    if (P > size_t(MAX_PROVIDERS) || q.counts.size() != P) throw std::invalid_argument("providers out of native range");
    if (n < 1 || n > size_t(MAX_ROWS)) throw std::invalid_argument("rows out of native range");
    if (q.target_any.size() != n || q.target_words.size() != 4 * n) throw std::invalid_argument("bad targets");
    if (q.phase.size() != size_t(q.m) || q.forced_and.size() != size_t(q.m) || q.forced_or.size() != size_t(q.m))
        throw std::invalid_argument("bad phase/forced");
    for (int c : q.counts) if (c < 1 || c > 255) throw std::invalid_argument("bad provider count");
}

}  // namespace

Result solve(const Query& q) {
    validate(q);
    const bool small = q.pats.size() <= 16;
    if (q.m <= 6) return small ? Engine<1, 16>(q).run() : Engine<1, 64>(q).run();
    if (q.m == 7) return small ? Engine<2, 16>(q).run() : Engine<2, 64>(q).run();
    return small ? Engine<4, 16>(q).run() : Engine<4, 64>(q).run();
}

// ======================================================================= stage B
void Stats::add(const Stats& o) {
    rec += o.rec; row_reject += o.row_reject; module_reject += o.module_reject; port_allocations += o.port_allocations;
    port_allocation_reject += o.port_allocation_reject; partition_checks += o.partition_checks;
    endpoint_split_reject += o.endpoint_split_reject; dominance_split_reject += o.dominance_split_reject;
    obligation_partitions += o.obligation_partitions; cover_nodes += o.cover_nodes;
    quotient_conflicts += o.quotient_conflicts; quotient_dropped += o.quotient_dropped; work += o.work;
    complete_cache_hits += o.complete_cache_hits; peak_cache_entries = std::max(peak_cache_entries, o.peak_cache_entries);
    local += o.local; phase_first_calls += o.phase_first_calls; phase_clauses += o.phase_clauses;
    phase_nodes += o.phase_nodes; phase_classes += o.phase_classes; monotone_calls += o.monotone_calls;
    phase_reject += o.phase_reject;
}

namespace {

inline int tbit(const uint64_t* t, int a) { return int((t[a >> 6] >> (a & 63)) & 1); }

// one_sharing_core.tree(m, t, signed) followed by local_blocks.learn on it.  Only the learned facts matter:
// leaf phases and, for each pair of leaves, the operation at their lowest common ancestor (child order and
// anchored_region.canonical's flattening change neither).
bool learn_target(int m, const uint64_t* t, bool is_signed, std::vector<int8_t>& phase, uint32_t forced[2][MAX_M]) {
    const int N = 1 << m;
    int inds[MAX_M], m2 = 0;
    for (int i = 0; i < m; ++i)
        for (int a = 0; a < N; ++a)
            if (!(a >> i & 1) && tbit(t, a) != tbit(t, a | 1 << i)) { inds[m2++] = i; break; }
    if (!m2) return false;
    const int N2 = 1 << m2;
    uint8_t g[1 << MAX_M], h[1 << MAX_M];
    for (int a = 0; a < N2; ++a) {
        int idx = 0;
        for (int j = 0; j < m2; ++j) if (a >> j & 1) idx |= 1 << inds[j];
        g[a] = uint8_t(tbit(t, idx));
    }
    uint32_t neg = 0;
    for (int i = 0; i < m2; ++i) {
        bool up = false, down = false;
        for (int a = 0; a < N2; ++a)
            if (!(a >> i & 1)) { const int d = int(g[a | 1 << i]) - int(g[a]); up |= d > 0; down |= d < 0; }
        if (up == down) return false;               // len(d) != 1
        if (down) { if (!is_signed) return false; neg |= 1u << i; }
    }
    for (int a = 0; a < N2; ++a) h[a] = g[a ^ neg];
    // anchored_region.recognize(m2, h): full support and monotonicity hold by construction
    uint32_t adj[MAX_M] = {};
    for (int a = 0; a < N2; ++a) {
        if (!h[a]) continue;
        bool minimal = true;
        for (int i = 0; i < m2 && minimal; ++i) if ((a >> i & 1) && h[a ^ (1 << i)]) minimal = false;
        if (!minimal) continue;
        for (int i = 0; i < m2; ++i) if (a >> i & 1) adj[i] |= uint32_t(a) ^ (1u << i);
    }
    auto comp = [&](uint32_t S, bool complement) {
        std::vector<uint32_t> out;
        while (S) {
            uint32_t todo = S & (0u - S); S ^= todo; uint32_t seen = todo;
            while (todo) {
                const uint32_t u = todo & (0u - todo); todo ^= u;
                const int i = std::countr_zero(u);
                const uint32_t a = S & (complement ? ~adj[i] : adj[i]);
                S ^= a; todo |= a; seen |= a;
            }
            out.push_back(seen);
        }
        return out;
    };
    struct RNode { char op; int leaf; std::vector<int> ch; };
    std::vector<RNode> nodes;
    std::function<int(uint32_t)> rec = [&](uint32_t S) -> int {
        if (std::popcount(S) == 1) { nodes.push_back({'x', std::countr_zero(S), {}}); return int(nodes.size()) - 1; }
        auto ch = comp(S, false); char op = '|';
        if (ch.size() == 1) { ch = comp(S, true); op = '&'; }
        if (ch.size() == 1) return -1;
        std::vector<int> sub;
        for (uint32_t c : ch) { const int r = rec(c); if (r < 0) return -1; sub.push_back(r); }
        nodes.push_back({op, -1, std::move(sub)});
        return int(nodes.size()) - 1;
    };
    const int root = rec(uint32_t(N2 - 1));
    if (root < 0) return false;
    std::function<int(int, int)> eval = [&](int id, int a) -> int {
        const RNode& nd = nodes[id];
        if (nd.op == 'x') return a >> nd.leaf & 1;
        int v = nd.op == '&';
        for (int c : nd.ch) v = nd.op == '&' ? (v & eval(c, a)) : (v | eval(c, a));
        return v;
    };
    for (int a = 0; a < N2; ++a) if (eval(root, a) != h[a]) return false;
    // learn(remap(tree)): leaf j is variable inds[j] with phase bit j of neg
    bool ok = true;
    std::function<uint32_t(int)> learn = [&](int id) -> uint32_t {
        const RNode& nd = nodes[id];
        if (nd.op == 'x') {
            const int i = inds[nd.leaf]; const int8_t p = int8_t(neg >> nd.leaf & 1);
            if (phase[i] >= 0 && phase[i] != p) { ok = false; return 0; }
            phase[i] = p;
            return 1u << i;
        }
        const int opi = nd.op == '&' ? 0 : 1, opposite = 1 - opi;
        uint32_t seen = 0;
        for (int c : nd.ch) {
            const uint32_t used = learn(c);
            if (!ok) return 0;
            for (uint32_t s = used; s; s &= s - 1) {
                const int i = std::countr_zero(s);
                if (forced[opposite][i] & seen) { ok = false; return 0; }
                forced[opi][i] |= seen;
            }
            for (uint32_t s = seen; s; s &= s - 1) forced[opi][std::countr_zero(s)] |= used;
            seen |= used;
        }
        return seen;
    };
    learn(root);
    return ok;
}

}  // namespace

bool prelude(int m, const std::vector<uint8_t>& target_any, const std::vector<uint64_t>& target_words, bool is_signed,
             std::vector<int8_t>& phase, std::vector<uint32_t>& forced_and, std::vector<uint32_t>& forced_or) {
    const int n = int(target_any.size()), N = 1 << m;
    phase.assign(m, -1);
    uint32_t forced[2][MAX_M] = {};
    std::vector<std::array<uint64_t, 4>> distinct;
    for (int r = 0; r < n; ++r) {
        if (target_any[r]) continue;
        std::array<uint64_t, 4> t{target_words[4 * r], target_words[4 * r + 1], target_words[4 * r + 2],
                                  target_words[4 * r + 3]};
        bool zero = true, full = true;
        for (int a = 0; a < N; ++a) { const int b = tbit(t.data(), a); zero &= !b; full &= b != 0; }
        if (zero || full) continue;
        if (std::find(distinct.begin(), distinct.end(), t) != distinct.end()) continue;
        distinct.push_back(t);
        if (!learn_target(m, t.data(), is_signed, phase, forced)) return false;
    }
    forced_and.assign(forced[0], forced[0] + m);
    forced_or.assign(forced[1], forced[1] + m);
    return true;
}

namespace {

// local_blocks(..., stats, module_filter, **PRODUCTION_FLAGS) including its prelude; nodes appended to `out`.
int local_blocks_into(Query q, Stats& stats, std::vector<Node>& out, Status& status) {
    ++stats.local;
    if (!prelude(q.m, q.target_any, q.target_words, q.is_signed, q.phase, q.forced_and, q.forced_or)) return -1;
    Result r = solve(q);
    stats.add(r.stats);
    status = r.status;
    if (r.status != Status::SAT) return -1;
    const int base = int(out.size());
    for (Node nd : r.nodes) {
        if (nd.op != 'x') { nd.a += base; nd.b += base; }
        out.push_back(nd);
    }
    return base + r.root;
}

int copy_lifted(const std::vector<Node>& src, int id, std::vector<Node>& out, int m, uint32_t flip,
                const std::vector<std::pair<int, int>>& refs, const std::vector<int>& provider_ids) {
    const Node& nd = src[id];
    if (nd.op == 'x') {
        Node leaf = nd;
        if (nd.a < m) leaf.b = int(flip >> nd.a & 1);
        else { const auto& [p, ph] = refs[nd.a - m]; leaf.a = m + provider_ids[p]; leaf.b = ph; }
        out.push_back(leaf);
        return int(out.size()) - 1;
    }
    const int a = copy_lifted(src, nd.a, out, m, flip, refs, provider_ids);
    const int b = copy_lifted(src, nd.b, out, m, flip, refs, provider_ids);
    out.push_back(Node{nd.op, a, b, 0, 0});
    return int(out.size()) - 1;
}

// regional_phase_first.phase_problem + phase_domains + phase_first over the native monotone solver.
int phase_first(const Query& q, Stats& stats, std::vector<Node>& out, Status& status) {
    const int m = q.m, P = int(q.provider_ids.size()), n = int(q.pats.size()), N = 1 << m;
    const int D = m + P;
    uint64_t polls = 0;
    const auto cancelled = [&](uint64_t interval) {
        if (++polls % interval != 0 || !q.poll || !q.poll()) return false;
        status = Status::ABORTED;
        return true;
    };
    // ---- phase_problem: class vectors of the labelled (row, assignment) cells
    std::vector<uint32_t> pos, neg;
    auto insert_unique = [](std::vector<uint32_t>& v, uint32_t x) {
        if (std::find(v.begin(), v.end(), x) == v.end()) v.push_back(x);
    };
    for (int r = 0; r < n; ++r) {
        if (cancelled(16)) return -1;
        if (q.target_any[r]) continue;
        const uint64_t* t = &q.target_words[4 * r];
        const uint32_t provider_bits = q.pats[r] << m;
        for (int x = 0; x < N; ++x) insert_unique(tbit(t, x) ? pos : neg, uint32_t(x) | provider_bits);
    }
    const uint32_t full = D == 32 ? ~0u : (1u << D) - 1;
    std::vector<std::pair<uint32_t, uint32_t>> clauses;
    clauses.reserve(pos.size() * neg.size() + pos.size() + neg.size());
    for (uint32_t a : pos) {
        if (cancelled(64)) return -1;
        for (uint32_t b : neg) clauses.emplace_back(a & ~b, b & ~a);
    }
    for (uint32_t a : pos) clauses.emplace_back(a, full ^ a);
    for (uint32_t b : neg) clauses.emplace_back(full ^ b, b);
    try {
        std::sort(clauses.begin(), clauses.end(), [&](const auto& x, const auto& y) {
            if (cancelled(8192)) throw Aborted{};
            const int sx = std::popcount(x.first) + std::popcount(x.second);
            const int sy = std::popcount(y.first) + std::popcount(y.second);
            return sx != sy ? sx < sy : x < y;
        });
    } catch (const Aborted&) {
        return -1;
    }
    clauses.erase(std::unique(clauses.begin(), clauses.end()), clauses.end());  // the reference builds a set
    std::vector<std::pair<uint32_t, uint32_t>> minimal;
    for (const auto& [a, b] : clauses) {
        if (cancelled(POLL_INTERVAL)) return -1;
        bool subsumed = false;
        for (const auto& [u, v] : minimal) if (!(u & ~a) && !(v & ~b)) { subsumed = true; break; }
        if (!subsumed) minimal.emplace_back(a, b);
    }
    stats.phase_clauses += int64_t(minimal.size());
    // ---- phase_domains: compiled clauses of (variable, allowed-value mask)
    using Clause = std::vector<std::pair<int, uint8_t>>;
    std::vector<Clause> compiled;
    for (const auto& [a, b] : minimal) {
        Clause cl;
        for (int j = 0; j < D; ++j)
            if ((a | b) >> j & 1) cl.emplace_back(j, uint8_t(((a >> j) & 1 ? 5 : 0) | ((b >> j) & 1 ? 6 : 0)));
        compiled.push_back(std::move(cl));
    }
    std::vector<uint8_t> dom(D);
    for (int i = 0; i < m; ++i) dom[i] = 3;
    for (int p = 0; p < P; ++p) dom[m + p] = q.counts[p] > 1 ? 7 : 3;
    const int64_t before = stats.monotone_calls;
    int found = -1;

    // consume one sign-availability class; returns true to stop (witness, abort)
    auto consume = [&](const std::vector<uint8_t>& state) -> bool {
        ++stats.phase_classes;
        uint32_t flip = 0;
        for (int i = 0; i < m; ++i) if (state[i] == 2) flip |= 1u << i;
        std::vector<uint64_t> ts(q.target_words);
        if (flip)
            for (int r = 0; r < n; ++r) {
                if (q.target_any[r]) continue;
                uint64_t* t = &ts[4 * r];
                const std::array<uint64_t, 4> old{t[0], t[1], t[2], t[3]};
                t[0] = t[1] = t[2] = t[3] = 0;
                for (int a = 0; a < N; ++a)
                    if (tbit(old.data(), a ^ int(flip))) t[a >> 6] |= uint64_t(1) << (a & 63);
            }
        // product over providers: (0,) if positive only, (c,) if negative only, range(1, c) if both
        std::vector<int> lo(P), hi(P), ns(P);
        for (int p = 0; p < P; ++p) {
            const uint8_t s = state[m + p];
            const int c = q.counts[p];
            if (s == 1) lo[p] = hi[p] = 0;
            else if (s == 2) lo[p] = hi[p] = c;
            else { lo[p] = 1; hi[p] = c - 1; }
            ns[p] = lo[p];
        }
        while (true) {
            if (cancelled(64)) return true;
            std::vector<std::pair<int, int>> refs;   // (compact provider, phase)
            Query mono;
            mono.m = m; mono.is_signed = false; mono.module_filter = q.module_filter; mono.row_quotient = true;
            mono.poll = q.poll; mono.work_limit = -1;
            for (int p = 0; p < P; ++p) {
                const int c = q.counts[p];
                const int ks[2] = {c - ns[p], ns[p]};
                for (int ph = 0; ph < 2; ++ph)
                    if (ks[ph]) {
                        mono.provider_ids.push_back(int(refs.size()));
                        mono.counts.push_back(ks[ph]);
                        refs.emplace_back(p, ph);
                    }
            }
            mono.pats.resize(n);
            for (int r = 0; r < n; ++r) {
                uint32_t v = 0;
                for (size_t j = 0; j < refs.size(); ++j)
                    v |= uint32_t(((q.pats[r] >> refs[j].first) & 1) ^ uint32_t(refs[j].second)) << j;
                mono.pats[r] = v;
            }
            mono.target_any = q.target_any;
            mono.target_words = ts;
            ++stats.monotone_calls;
            std::vector<Node> tmp;
            Status st = Status::UNSAT;
            const int w = local_blocks_into(std::move(mono), stats, tmp, st);
            if (st == Status::ABORTED || st == Status::WORK_LIMIT) { status = st; return true; }
            if (w >= 0) {
                found = copy_lifted(tmp, w, out, m, flip, refs, q.provider_ids);
                status = Status::SAT;
                return true;
            }
            int p = P - 1;
            while (p >= 0) {
                if (ns[p] < hi[p]) { ++ns[p]; break; }
                ns[p] = lo[p];
                --p;
            }
            if (p < 0) return false;
        }
    };

    std::function<bool(std::vector<uint8_t>)> rec = [&](std::vector<uint8_t> d) -> bool {
        if (cancelled(64)) return true;
        std::vector<Clause> active;
        while (true) {
            bool changed = false;
            active.clear();
            for (const Clause& cl : compiled) {
                Clause live;
                bool satisfied = false;
                for (const auto& [j, mask] : cl) {
                    if (!(d[j] & ~mask)) { satisfied = true; break; }
                    if (d[j] & mask) live.emplace_back(j, mask);
                }
                if (satisfied) continue;
                if (live.empty()) return false;
                if (live.size() == 1) { d[live[0].first] &= live[0].second; changed = true; }
                else active.push_back(std::move(live));
            }
            if (!changed) break;
        }
        ++stats.phase_nodes;
        if (active.empty()) {
            // product over (4, 1, 2) restricted to each domain, last variable fastest
            std::vector<std::vector<uint8_t>> vals(D);
            for (int j = 0; j < D; ++j)
                for (uint8_t v : {uint8_t(4), uint8_t(1), uint8_t(2)}) if (d[j] & v) vals[j].push_back(v);
            std::vector<size_t> idx(D, 0);
            std::vector<uint8_t> state(D);
            while (true) {
                for (int j = 0; j < D; ++j) state[j] = vals[j][idx[j]];
                if (consume(state)) return true;
                int j = D - 1;
                while (j >= 0) {
                    if (++idx[j] < vals[j].size()) break;
                    idx[j] = 0;
                    --j;
                }
                if (j < 0) return false;
            }
        }
        // weight = Counter(j for cl in active for j, _ in cl); max(key=(weight, -|d_j|)) keeps the first maximum
        std::vector<int> order, weight(D, 0);
        for (const Clause& cl : active)
            for (const auto& [j, mask] : cl) { if (!weight[j]) order.push_back(j); ++weight[j]; }
        int best = -1;
        for (int j : order) {
            if (std::popcount(unsigned(d[j])) <= 1) continue;
            if (best < 0 || weight[j] > weight[best] ||
                (weight[j] == weight[best] && std::popcount(unsigned(d[j])) < std::popcount(unsigned(d[best]))))
                best = j;
        }
        for (uint8_t v : {uint8_t(4), uint8_t(1), uint8_t(2)}) {
            if (!(d[best] & v)) continue;
            std::vector<uint8_t> dd = d;
            dd[best] = v;
            if (rec(dd)) return true;
        }
        return false;
    };
    rec(dom);
    if (status == Status::ABORTED || status == Status::WORK_LIMIT) return -1;
    if (found < 0 && stats.monotone_calls == before) ++stats.phase_reject;
    return found;
}

}  // namespace

Result solve_completion(const Query& q, bool adaptive) {
    validate(q);
    Result res;
    Status status = Status::UNSAT;
    const int n = int(q.pats.size());
    int labels = 0, total_ports = 0;
    for (int r = 0; r < n; ++r) labels += !q.target_any[r];
    labels <<= q.m;
    for (int c : q.counts) total_ports += c;
    const int repeats = total_ports - int(q.counts.size());
    const bool rule = labels <= 4096 && !(repeats == 0 && q.m >= 4);   // regional_phase_first.phase_rule
    int root;
    if (adaptive && q.is_signed && q.m + total_ports > 0 && rule) {
        ++res.stats.phase_first_calls;
        root = phase_first(q, res.stats, res.nodes, status);
    } else {
        root = local_blocks_into(q, res.stats, res.nodes, status);
    }
    res.root = root;
    res.status = root >= 0 ? Status::SAT : (status == Status::SAT ? Status::UNSAT : status);
    return res;
}


}  // namespace regional
