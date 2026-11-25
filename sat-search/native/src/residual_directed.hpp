#pragma once
// Exact constrained signed read-once completion over fixed occurrences.
// Independent kernel for integration; no Percy or platform dependencies.
// Leaf columns must agree on cared rows for occurrences of the same wire.
#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdint>
#include <limits>
#include <memory>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>

namespace residual_directed {
using U=std::uint64_t;
using Sub=std::uint32_t;
struct Leaf { unsigned wire; U column; bool raw; };
struct Node;
using Tree=std::shared_ptr<const Node>;
// Leaves use the normalized input column. Gates evaluate signed AND, then
// normalize by the stored output phase. Occurrence index is retained.
struct Node { int occurrence; Tree a,b; bool pa=false,pb=false,po=false; };
struct Witness { Tree tree; bool phase=false; explicit operator bool()const{return bool(tree);} };
enum class Status { sat, unsat, unknown };
struct Result { Status status; Witness witness; U work, joins, states; };
struct Key { Sub s; U p,n; bool operator==(const Key&)const=default; };
struct Hash { std::size_t operator()(const Key& k)const noexcept {
    std::size_t h=std::hash<U>{}(k.p); h^=std::hash<U>{}(k.n)+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);
    h^=std::hash<Sub>{}(k.s)+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);return h;
}};
class Solver {
    struct Limit{};
    using Columns=std::unordered_map<U,Tree>;
    std::vector<Leaf> leaves; U mask,anchor,limit,work=0,joins=0,states=0;
    bool dominance;
    std::chrono::steady_clock::time_point deadline;
    std::unordered_map<Sub,std::vector<U>> group_cache;
    std::unordered_map<Sub,Columns> columns;
    std::unordered_map<Key,Witness,Hash> memo;
    Sub raw=0;
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
        if(auto it=columns.find(s);it!=columns.end())return it->second;
        charge();Columns out;
        if(!legal(s))return columns.emplace(s,std::move(out)).first->second;
        if(std::has_single_bit(s)){auto i=std::countr_zero(s);out.emplace(leaves[i].column,leaf(i));}
        else for(Sub a=(s-1)&s;a;a=(a-1)&s){
            charge();Sub b=s^a;if(!(a&(s&-s))||!split_ok(a,b))continue;
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
        for(Sub t=(s-1)&s;t;t=(t-1)&s){
            charge();if(!(t&(s&-s)))continue;Sub a=t,b=s^t;
            if(!split_ok(a,b))continue;
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
    Solver(std::vector<Leaf> input,U cared,U work_limit=1000000,
           std::chrono::steady_clock::time_point end=std::chrono::steady_clock::time_point::max(),bool use_dominance=false)
      :leaves(std::move(input)),mask(cared),anchor(cared&-cared),limit(work_limit),dominance(use_dominance),deadline(end){
        if(!mask||leaves.empty())throw std::invalid_argument("nonempty care and leaves required");
        if(leaves.size()>12)throw std::invalid_argument("reference width limit 12");
        for(unsigned i=0;i<leaves.size();++i){
            leaves[i].column=norm(leaves[i].column&mask);
            if(leaves[i].raw)raw|=Sub(1)<<i;
            for(unsigned j=0;j<i;++j)if(leaves[i].wire==leaves[j].wire && (leaves[i].column!=leaves[j].column||leaves[i].raw!=leaves[j].raw))throw std::invalid_argument("inconsistent repeated wire");
        }
    }
    Result run(U p,U n){
        if((p|n)&~mask || p&n)throw std::invalid_argument("invalid obligations");
        try{
            auto w=ask((Sub(1)<<leaves.size())-1,p,n);
            if(std::chrono::steady_clock::now()>=deadline)return {Status::unknown,{},work,joins,states};
            return {w?Status::sat:Status::unsat,w,work,joins,states};
        }catch(const Limit&){return {Status::unknown,{},work,joins,states};}
    }
};
} // namespace residual_directed
