#pragma once
// Standalone C++20 exact residual solver, slack 0..3. Uses the previous
// directed tree kernel and parity filter; independent of Percy. Slack three and
// the occurrence-symmetric tree solver are opt-in (use_symmetric, run(a, 3)).
#include "residual_directed.hpp"
#include "residual_symmetric_directed.hpp"
#include "residual_parity_filter.hpp"
#include "residual_phase_screen.hpp"
#include "residual_provider_unate.hpp"
#include "residual_decoder_phase.hpp"
#include <functional>
#include <map>
#include <set>
#include <tuple>
namespace residual_slack_two {
using namespace residual_directed;
using Clock=std::chrono::steady_clock;
struct Region { std::vector<Leaf> inputs; unsigned output; U column; Witness witness; };
struct PhaseStats {
    U checks = 0, rejects = 0, work = 0, cache_hits = 0, dominance_hits = 0;
};
// Last-provider decoder phase screen (use_decoder >= 1): screens built, allocations rejected
// before any candidate, candidate columns rejected before exact recognition, screens skipped
// (more than six singleton wires), and charged work.
struct DecoderStats {
    U screens = 0, rejects = 0, column_rejects = 0, skipped = 0, work = 0;
};
struct Answer { Status status; std::vector<Region> regions; U work,allocations,parity_rejects,provider_trials,tree_calls,memo_hits,unate_rejects,unate_merges; PhaseStats phase; DecoderStats decoder; };
struct Entry { Leaf leaf; unsigned count; };
class Engine {
    struct Limit{};
    using Columns=std::map<U,Tree>;
    U care,anchor,target,limit,work=0,allocs=0,rejects=0,trials=0,tree_calls=0;
    Clock::time_point end;
    bool parity, direct, memoize, unate;
    bool phase_screen, cache_phases, symmetric;
    PhaseStats phase_stats;
    unsigned decoder;
    DecoderStats decoder_stats;
    struct PhaseMasks { std::vector<unsigned> feasible, infeasible; };
    std::map<std::pair<U, std::vector<U>>, PhaseMasks> phase_cache;
    U unate_rejects=0,unate_merges=0;
    using State = std::pair<std::vector<std::tuple<U,bool,unsigned>>,std::vector<unsigned>>;
    std::set<State> failed;
    U memo_hits=0;
    unsigned k;
    bool used=false;
    std::vector<Region> path;
    void tick(U n=1) { if(n>limit-work || ((work&63)==0 && Clock::now()>=end))throw Limit{};work+=n; }
    U norm(U c)const {c&=care;return c&anchor?c^care:c;}
    static std::vector<Leaf> expand(const std::vector<Entry>& a) { std::vector<Leaf> out;for(auto e:a)for(unsigned j=0;j<e.count;++j)out.push_back(e.leaf);return out; }
    static std::vector<U> cols(const std::vector<Leaf>& a) {std::vector<U> out;for(auto l:a)out.push_back(l.column);return out;}
    bool phase_feasible(const std::vector<Leaf>& leaves, U column) {
        const auto wires = residual_phase_screen::collect(leaves);
        const unsigned repeated = wires.repeated;
        PhaseMasks* masks = nullptr;
        if (cache_phases) {
            auto key = std::make_pair(norm(column), wires.columns);
            auto it = phase_cache.find(key);
            if (it == phase_cache.end() && phase_cache.size() < 128)
                it = phase_cache.try_emplace(std::move(key)).first;
            if (it != phase_cache.end()) masks = &it->second;
        }
        const auto subset = [](unsigned a, unsigned b) { return (a & b) == a; };
        if (masks) {
            for (const auto known : masks->feasible)
                if (subset(known, repeated)) {
                    ++phase_stats.cache_hits;
                    phase_stats.dominance_hits += known != repeated;
                    return true;
                }
            for (const auto known : masks->infeasible)
                if (subset(repeated, known)) {
                    ++phase_stats.cache_hits;
                    phase_stats.dominance_hits += known != repeated;
                    return false;
                }
        }
        ++phase_stats.checks;
        const bool feasible = residual_phase_screen::feasible(wires, column, care ^ column, [&](unsigned units) {
            if (Clock::now() >= end) throw Limit{};
            tick(units);
            phase_stats.work += units;
        });
        if (masks) {
            auto& entries = feasible ? masks->feasible : masks->infeasible;
            std::erase_if(entries, [&](unsigned known) {
                return feasible ? subset(repeated, known) : subset(known, repeated);
            });
            entries.push_back(repeated);
        }
        return feasible;
    }
    // Exact tree lookup, preserving the witness phase and shared deadline.
    Witness ask(const std::vector<Leaf>& a,U c) {
        tick();
        if (phase_screen && !phase_feasible(a, c)) {
            ++phase_stats.rejects;
            return {};
        }
        ++tree_calls;
        auto r = symmetric ? SymmetricSolver(a, care, limit - work, end).run(c, care ^ c)
                           : Solver(a, care, limit - work, end).run(c, care ^ c);
        tick(r.work);
        if (r.status == Status::unknown) throw Limit{};
        return r.witness;
    }
    // Column enumeration for provider regions when there are too many free
    // parity components to enumerate their orientations. Occurrence subsets
    // are local to this allocation. Signed output normalized at anchor.
    class ProviderDP {
        Engine& e;const std::vector<Leaf>& a;std::map<Sub,Columns> memo;
    public:
        ProviderDP(Engine& ee,const std::vector<Leaf>& aa):e(ee),a(aa){}
        const Columns& get(Sub s) {
            if(auto it=memo.find(s);it!=memo.end())return it->second;
            e.tick();Columns out;
            if(std::has_single_bit(s)){unsigned i=std::countr_zero(s);out.emplace(a[i].column,std::make_shared<Node>(Node{int(i),{},{},false,false,false}));}
            else for(Sub x=(s-1)&s;x;x=(x-1)&s){
                e.tick();if(!(x&(s&-s)))continue;Sub y=s^x;
                if(std::has_single_bit(x)&&std::has_single_bit(y)) { auto l=a[std::countr_zero(x)],r=a[std::countr_zero(y)];if(l.wire==r.wire||(l.raw&&r.raw))continue; }
                auto& xx=get(x);auto& yy=get(y);
                for(auto&[c,t]:xx)for(auto&[d,u]:yy)for(int p=0;p<2;++p)for(int q=0;q<2;++q){
                    e.tick();U v=(c^(p?e.care:0))&(d^(q?e.care:0));U z=e.norm(v);
                    if(!out.contains(z))out.emplace(z,std::make_shared<Node>(Node{-1,t,u,bool(p),bool(q),bool(v&e.anchor)}));
                }
            }
            return memo.emplace(s,std::move(out)).first->second;
        }
    };
    bool whole_distinguishes(const std::vector<Entry>& a) {
        auto f=residual_filter::fibers(cols(expand(a)),care);
        for(unsigned i=0;i<f.size;++i)if((f.mask[i]&target)&&(f.mask[i]&(care^target)))return false;
        return true;
    }
    bool search(const std::vector<Entry>& a,const std::vector<unsigned>& ds,unsigned next){
        tick();
        if(!memoize)return search_impl(a,ds,next);
        State key;for(auto x:a)key.first.emplace_back(x.leaf.column,x.leaf.raw,x.count);
        std::sort(key.first.begin(),key.first.end());
        key.second.assign(ds.begin()+next,ds.end());
        if(failed.contains(key)){++memo_hits;return false;}
        if(search_impl(a,ds,next))return true;
        failed.insert(std::move(key));return false;
    }
    bool search_impl(const std::vector<Entry>& a,const std::vector<unsigned>& ds,unsigned next){
        if(!whole_distinguishes(a))return false;
        if(next==ds.size()){
            auto leaves=expand(a);if(leaves.size()<2)return false;
            auto w=ask(leaves,target);if(!w)return false;
            path.push_back({std::move(leaves),k+next,target,w});return true;
        }
        std::vector<unsigned> taken(a.size());
        // Enumerate counts, not labeled copies of identical wire occurrences.
        std::function<bool(unsigned,unsigned)> split=[&](unsigned i,unsigned n){
            tick();if(i<a.size()){
                for(unsigned c=0;c<=a[i].count;++c){taken[i]=c;if(split(i+1,n+c))return true;}
                return false;
            }
            if(n<2)return false;
            std::vector<Entry> rest;std::vector<Leaf> inside;bool allraw=true;
            for(unsigned j=0;j<a.size();++j){
                for(unsigned c=0;c<taken[j];++c)inside.push_back(a[j].leaf);
                if(taken[j]&&!a[j].leaf.raw)allraw=false;
                if(taken[j]<a[j].count)rest.push_back({a[j].leaf,a[j].count-taken[j]});
            }
            if(allraw||(n==2&&inside[0].wire==inside[1].wire))return false;
            // No provider can be the residual output: every provider has >=2 readers.
            // All remaining allocated regions must have at least two leaves.
            unsigned remaining=ds[next];for(auto x:rest)remaining+=x.count;
            for(unsigned j=next+1;j<ds.size();++j)remaining+=ds[j];
            if(remaining<2*(ds.size()-next))return false;
            ++allocs;
            auto in_f=residual_filter::fibers(cols(inside),care);
            auto out_f=residual_filter::fibers(cols(expand(rest)),care);
            auto pc=residual_filter::provider_components(in_f,out_f,target,care);
            if(parity&&!pc.consistent){++rejects;return false;}
            if(parity&&unate){
                auto ref=residual_provider_unate::refine(inside,in_f,std::move(pc));pc=std::move(ref.components);unate_merges+=ref.merges;
                if(!pc.consistent){++unate_rejects;return false;}
            }
            // Decoder phase screen: only at the last provider, whose remaining region is the
            // final decoder (earlier singletons may feed later providers).
            residual_decoder_phase::Screen dec;
            if(decoder&&parity&&next+1==ds.size()){
                dec=residual_decoder_phase::build(expand(rest),pc,target,care^target,decoder>=2,
                    [&](U units){tick(units);decoder_stats.work+=units;});
                if(!dec.enabled)++decoder_stats.skipped;else ++decoder_stats.screens;
                if(dec.enabled&&!dec.allowed){++decoder_stats.rejects;return false;}
            }
            auto screened=[&](U c){
                if(!dec.enabled)return true;
                tick(dec.edges.size()+1);decoder_stats.work+=dec.edges.size()+1;
                if(dec.accepts(c))return true;
                ++decoder_stats.column_rejects;return false;
            };
            auto try_provider=[&](U c,Witness w){
                tick();++trials;
                std::vector<Entry> newa=rest;newa.push_back({Leaf{k+next,c,false},ds[next]});
                if(!whole_distinguishes(newa))return false;
                path.push_back({inside,k+next,c,w});
                if(search(newa,ds,next+1))return true;
                path.pop_back();return false;
            };
            if(parity&&direct&&pc.sides.size()<=5){
                // One component orientation fixed: global complement free.
                U first=pc.sides[0][0];std::set<U> seen;
                for(unsigned bits=0;bits<(1u<<(pc.sides.size()-1));++bits){
                    tick();U c=first;for(unsigned j=1;j<pc.sides.size();++j)c|=pc.sides[j][(bits>>(j-1))&1];c=norm(c);
                    if(!seen.insert(c).second||!screened(c))continue;
                    auto w=ask(inside,c);if(w&&try_provider(c,w))return true;
                }
            }else{
                ProviderDP dp(*this,inside);
                for(auto&[c,t]:dp.get((Sub(1)<<inside.size())-1)){
                    tick(); // Test distinction before recursing, even if parity disabled.
                    bool good=true;for(unsigned j=0;j<out_f.size;++j){U p=out_f.mask[j]&target,z=out_f.mask[j]&(care^target);if(p&&z&&!(((c&p)==p&&!(c&z))||((c&z)==z&&!(c&p)))){good=false;break;}}
                    if(good&&screened(c)&&try_provider(c,Witness{t,false}))return true;
                }
            }
            return false;
        };
        return split(0,0);
    }
public:
    Engine(U mask,U f,U cap=1000000,Clock::time_point deadline=Clock::time_point::max(),bool use_parity=true,bool use_direct=true,bool use_memo=true,bool use_unate=false,bool use_phase_screen=false,bool use_phase_cache=false,bool use_symmetric=false,unsigned use_decoder=0)
      :care(mask),anchor(mask&-mask),target(f&mask),limit(cap),end(deadline),parity(use_parity),direct(use_direct),memoize(use_memo),unate(use_unate),phase_screen(use_phase_screen),cache_phases(use_phase_cache),symmetric(use_symmetric),decoder(use_decoder){if(use_decoder>2)throw std::invalid_argument("use_decoder is 0, 1 or 2");if(!care)throw std::invalid_argument("empty care");}
    Answer run(std::vector<Leaf> a,unsigned s){
        if(used)throw std::invalid_argument("Engine is single-use");used=true;
        k=a.size();if(k<2||k>8||s>3)throw std::invalid_argument("reference supports k=2..8, s=0..3");
        for(unsigned i=0;i<k;++i){if(a[i].wire!=i)throw std::invalid_argument("boundary IDs must be 0..k-1");a[i].column=norm(a[i].column);}
        try{
            for(unsigned q=0;q<=s;++q){
                // Each shared internal output consumes one extra read already.
                std::vector<unsigned> extra(k+q);
                std::function<bool(unsigned,unsigned)> dist=[&](unsigned i,unsigned left){
                    tick();if(i==extra.size()){
                        if(left)return false;
                        std::vector<Entry> entries;for(unsigned j=0;j<k;++j)entries.push_back({a[j],1+extra[j]});
                        std::vector<unsigned> ds;for(unsigned j=0;j<q;++j)ds.push_back(2+extra[k+j]);
                        return search(entries,ds,0);
                    }
                    for(unsigned c=0;c<=left;++c){extra[i]=c;if(dist(i+1,left-c))return true;}return false;
                };
                if(dist(0,s-q)){if(Clock::now()>=end)throw Limit{};return {Status::sat,path,work,allocs,rejects,trials,tree_calls,memo_hits,unate_rejects,unate_merges,phase_stats,decoder_stats};}
            }
            if(Clock::now()>=end)throw Limit{};
            return {Status::unsat,{},work,allocs,rejects,trials,tree_calls,memo_hits,unate_rejects,unate_merges,phase_stats,decoder_stats};
        }catch(const Limit&){return {Status::unknown,{},work,allocs,rejects,trials,tree_calls,memo_hits,unate_rejects,unate_merges,phase_stats,decoder_stats};}
    }
};
}
