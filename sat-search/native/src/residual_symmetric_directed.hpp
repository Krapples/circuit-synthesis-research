// Occurrence-symmetric directed tree solver (opt-in alternative to residual_directed::Solver).
// Ported unchanged from the residual occurrence-symmetry research bundle (2026-11-25). Occurrences
// of one wire ID are interchangeable; count-vector splits, split caching, canonical subset memo
// keys and final occurrence relabeling. Distinct wires with equal columns stay distinct.
#pragma once
#include "residual_directed.hpp"
#include <array>
#include <functional>
namespace residual_directed {
class SymmetricSolver {
    struct Limit{};
    using Columns=std::unordered_map<U,Tree>;
    std::vector<Leaf> leaves; U mask,anchor,limit,work=0,joins=0,states=0;
    bool dominance;
    std::chrono::steady_clock::time_point deadline;
    std::unordered_map<Sub,std::vector<U>> group_cache;
    std::unordered_map<Sub,Columns> columns;
    std::unordered_map<Key,Witness,Hash> memo;
    Sub raw=0;
    bool quotient,canonical_memo;
    std::vector<Sub> wire_groups, repeated_groups;
    Sub canonical(Sub s) const {if(!canonical_memo)return s;for(Sub g:repeated_groups){unsigned n=std::popcount(s&g);s&=~g;while(n--){Sub b=g&-g;s|=b;g^=b;}}return s;}
    Tree relabel(Tree t,std::vector<Sub>& available){if(!t)return {};if(t->occurrence>=0){unsigned i=t->occurrence,j=0;while(!(wire_groups[j]&(Sub(1)<<i)))++j;Sub b=available[j]&-available[j];if(!b)throw std::logic_error("occurrence count");available[j]^=b;return leaf(std::countr_zero(b));}return gate(relabel(t->a,available),relabel(t->b,available),t->pa,t->pb,t->po);}

    std::unordered_map<Sub,std::vector<Sub>> split_cache;
    // Representatives of unordered bipartitions under permutations of equal-wire occurrences.
    const std::vector<Sub>& splits(Sub s){
        if(auto it=split_cache.find(s);it!=split_cache.end())return it->second;
        std::vector<Sub> out;
        bool any_repeat=false;for(Sub g:repeated_groups)if(std::popcount(g&s)>1){any_repeat=true;break;}
        if(!quotient||!any_repeat){for(Sub a=(s-1)&s;a;a=(a-1)&s){charge();if((a&(s&-s))&&split_ok(a,s^a))out.push_back(a);}}
        else {
            std::vector<Sub> g;for(Sub w:wire_groups)if(w&s)g.push_back(w&s);
            // Generate one canonical prefix in each group. Compare its mask
            // with the canonical prefix for the complementary count vector.
            auto rec=[&](auto&& self,unsigned i,Sub a,Sub b)->void{
                charge();if(i==g.size()){if(a&&a!=s&&a<=b&&split_ok(a,s^a))out.push_back(a);return;}
                Sub w=g[i];unsigned m=std::popcount(w);std::array<Sub,13> pref{};for(unsigned j=1;j<=m;++j){Sub v=w&-w;w^=v;pref[j]=pref[j-1]|v;}
                for(unsigned j=0;j<=m;++j)self(self,i+1,a|pref[j],b|pref[m-j]);
            };rec(rec,0,0,0);
            // Preserve the original approximate descending split order.
            std::sort(out.begin(),out.end(),std::greater<Sub>());
        }
        return split_cache.emplace(s,std::move(out)).first->second;
    }

    void charge(){
        if(work>=limit)throw Limit{};
        if((work&63)==0 && std::chrono::steady_clock::now()>=deadline)throw Limit{};
        ++work;
    }
    U norm(U x)const{return x&anchor?x^mask:x;}
    bool legal(Sub s)const{return s && (std::has_single_bit(s)||(s&~raw));}
    bool split_ok(Sub a,Sub b)const{
        if(!legal(a)||!legal(b))return false;
        if(std::has_single_bit(a)&&std::has_single_bit(b)){
            auto i=std::countr_zero(a),j=std::countr_zero(b);
            return leaves[i].wire!=leaves[j].wire && !(leaves[i].raw&&leaves[j].raw);
        }
        return true;
    }
    const std::vector<U>& groups(Sub s){
        if(auto it=group_cache.find(s);it!=group_cache.end())return it->second;
        charge();std::vector<U> g{mask};
        for(Sub t=s;t;t&=t-1){
            U c=leaves[std::countr_zero(t)].column;std::vector<U> next;
            for(U m:g){charge();if(U v=m&c)next.push_back(v);if(U v=m&~c)next.push_back(v);}
            g=std::move(next);
        }
        return group_cache.emplace(s,std::move(g)).first->second;
    }
    U forced(Sub s,U p){U u=0;for(U g:groups(s)){charge();if(g&p)u|=g;}return u;}
    bool close(Sub s,U& p,U& n){
        U pp=0,nn=0;for(U g:groups(s)){charge();if(g&p){if(g&n)return false;pp|=g;}else if(g&n)nn|=g;}
        p=pp;n=nn;return true;
    }
    Tree leaf(unsigned i){charge();return std::make_shared<Node>(Node{int(i),{}, {},false,false,false});}
    Tree gate(Tree a,Tree b,bool pa,bool pb,bool po){charge();return std::make_shared<Node>(Node{-1,std::move(a),std::move(b),pa,pb,po});}
    const Columns& dp(Sub s){
        s=canonical(s);
        if(auto it=columns.find(s);it!=columns.end())return it->second;
        charge();Columns out;
        if(!legal(s))return columns.emplace(s,std::move(out)).first->second;
        if(std::has_single_bit(s)){auto i=std::countr_zero(s);out.emplace(leaves[i].column,leaf(i));}
        else for(Sub a:splits(s)){
            charge();Sub b=s^a;
            auto const& aa=dp(a);auto const& bb=dp(b);
            for(auto const& [x,ta]:aa)for(auto const& [y,tb]:bb){
                ++joins;
                for(int pa=0;pa<2;++pa)for(int pb=0;pb<2;++pb){
                    charge();U v=(x^(pa?mask:0))&(y^(pb?mask:0));U c=norm(v);
                    if(!out.contains(c))out.emplace(c,gate(ta,tb,pa,pb,bool(v&anchor)));
                }
            }
        }
        return columns.emplace(s,std::move(out)).first->second;
    }
    Witness ask(Sub s,U p,U n){
        s=canonical(s);
        charge();if(!legal(s)||!close(s,p,n))return {};
        bool flip=p>n;if(flip)std::swap(p,n);Key key{s,p,n};
        if(auto it=memo.find(key);it!=memo.end()){auto w=it->second;w.phase^=flip;return w;}
        auto w=solve(s,p,n);memo.emplace(key,w);w.phase^=flip;return w;
    }
    Witness solve(Sub s,U p,U n){
        charge();++states;
        if(std::has_single_bit(s)){
            auto i=std::countr_zero(s);U c=leaves[i].column;
            for(int phase=0;phase<2;++phase){U v=c^(phase?mask:0);if((v&p)==p&&!(v&n))return {leaf(i),bool(phase)};}return {};
        }
        for(Sub t:splits(s)){
            charge();Sub a=t,b=s^t;
            if(std::popcount(a)>std::popcount(b))std::swap(a,b);
            for(int po=0;po<2;++po){
                U pos=po?n:p,neg=po?p:n;U ua=forced(a,pos),ub=forced(b,pos);
                if(ua&ub&neg)continue;
                U za=ub&neg;
                std::unordered_map<U,Witness> candidates;
                for(auto const& [c,tree]:dp(a))for(int pa=0;pa<2;++pa){
                    charge();U x=c^(pa?mask:0);if((x&pos)!=pos||(x&za))continue;
                    U pp=pos,req=x&neg;if(!close(b,pp,req))continue;
                    candidates.try_emplace(req,Witness{tree,bool(pa)});
                }
                std::vector<U> order;order.reserve(candidates.size());
                for(auto const& [req,w]:candidates)order.push_back(req);
                std::sort(order.begin(),order.end(),[](U a,U b){return std::popcount(a)==std::popcount(b)?a<b:std::popcount(a)<std::popcount(b);});
                std::vector<U> failed;
                for(U req:order){
                    charge();bool skip=false;if(dominance)for(U z:failed){charge();if((z&req)==z){skip=true;break;}}
                    if(skip)continue;
                    auto wb=ask(b,pos,req);if(!wb){failed.push_back(req);continue;}
                    auto wa=candidates.at(req);bool ph=wa.phase&&wb.phase;
                    return {gate(wa.tree,wb.tree,wa.phase,wb.phase,ph),bool(ph^bool(po))};
                }
            }
        }
        return {};
    }
public:
    SymmetricSolver(std::vector<Leaf> input,U cared,U work_limit=1000000,
           std::chrono::steady_clock::time_point end=std::chrono::steady_clock::time_point::max(),bool use_dominance=false,bool use_quotient=true,bool use_canonical_memo=true)
      :leaves(std::move(input)),mask(cared),anchor(cared&-cared),limit(work_limit),dominance(use_dominance),deadline(end),quotient(use_quotient),canonical_memo(use_canonical_memo){
        if(!mask||leaves.empty())throw std::invalid_argument("nonempty care and leaves required");
        if(leaves.size()>12)throw std::invalid_argument("reference width limit 12");
        for(unsigned i=0;i<leaves.size();++i){
            leaves[i].column=norm(leaves[i].column&mask);
            if(leaves[i].raw)raw|=Sub(1)<<i;
            for(unsigned j=0;j<i;++j)if(leaves[i].wire==leaves[j].wire && (leaves[i].column!=leaves[j].column||leaves[i].raw!=leaves[j].raw))throw std::invalid_argument("inconsistent repeated wire");
        }
        for(unsigned i=0;i<leaves.size();++i){unsigned j=0;while(j<wire_groups.size()&&leaves[std::countr_zero(wire_groups[j])].wire!=leaves[i].wire)++j;if(j==wire_groups.size())wire_groups.push_back(0);wire_groups[j]|=Sub(1)<<i;}
        for(Sub g:wire_groups)if(std::popcount(g)>1)repeated_groups.push_back(g);
    }
    Result run(U p,U n){
        if((p|n)&~mask || p&n)throw std::invalid_argument("invalid obligations");
        try{
            auto w=ask((Sub(1)<<leaves.size())-1,p,n);
            if(w&&canonical_memo&&!repeated_groups.empty()){auto available=wire_groups;w.tree=relabel(w.tree,available);for(Sub g:available)if(g)throw std::logic_error("unused occurrence");}
            if(std::chrono::steady_clock::now()>=deadline)return {Status::unknown,{},work,joins,states};
            return {w?Status::sat:Status::unsat,w,work,joins,states};
        }catch(const Limit&){return {Status::unknown,{},work,joins,states};}
    }
};
}
