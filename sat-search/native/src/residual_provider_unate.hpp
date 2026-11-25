#pragma once
// Refine provider parity components by consistent literal signs on wires
// appearing once in the provider region. C++20, packed cared-row columns.
#include "residual_parity_filter.hpp"
#include "residual_directed.hpp"
#include <bit>
#include <map>
namespace residual_provider_unate {
using namespace residual_filter;
using residual_directed::Leaf;
struct Refined { ParityComponents components; unsigned merges=0; };
inline Refined refine(std::span<const Leaf> leaves,const Fibers& fibers,ParityComponents pc) {
    if(!pc.consistent)return {std::move(pc),0};
    // In a read-once tree over occurrences, a wire appearing exactly once
    // has a fixed sign (unate dependence), even with repeated other wires.
    std::vector<Leaf> unique;std::vector<unsigned> counts;
    for(auto l:leaves){unsigned j=0;while(j<unique.size()&&unique[j].wire!=l.wire)++j;if(j==unique.size()){unique.push_back(l);counts.push_back(0);}++counts[j];}
    std::vector<unsigned> patterns(fibers.size); // prototype <= 12 occurrences
    for(unsigned i=0;i<fibers.size;++i){Word r=fibers.mask[i]&-fibers.mask[i];for(unsigned j=0;j<unique.size();++j)if(unique[j].column&r)patterns[i]|=1u<<j;}
    struct Pair {unsigned lo,hi,var;};std::vector<Pair> pairs;
    for(unsigned i=0;i<fibers.size;++i)for(unsigned j=i+1;j<fibers.size;++j){unsigned d=patterns[i]^patterns[j];if(!std::has_single_bit(d))continue;unsigned v=std::countr_zero(d);if(counts[v]!=1)continue;pairs.push_back({patterns[i]&d?j:i,patterns[i]&d?i:j,v});}
    unsigned merges=0;
    while(true){
        unsigned n=pc.sides.size();std::vector<unsigned> comp(fibers.size),color(fibers.size);
        for(unsigned i=0;i<fibers.size;++i)for(unsigned c=0;c<n;++c)for(unsigned b=0;b<2;++b)if(fibers.mask[i]&pc.sides[c][b]){comp[i]=c;color[i]=b;}
        ParityDSU dsu(n);std::vector<int> first(unique.size(),-1);std::vector<unsigned> sign(unique.size());unsigned joined=0;
        for(auto [lo,hi,v]:pairs){if(comp[lo]!=comp[hi]||color[lo]==color[hi])continue;
            unsigned c=comp[lo],b=color[lo]; // sign_v = flip_c XOR b
            if(first[v]<0){first[v]=int(c);sign[v]=b;continue;}
            auto [a,p]=dsu.find(unsigned(first[v]));auto [r,q]=dsu.find(c);unsigned want=sign[v]^b;
            if(a==r){if((p^q)!=want)return {{false,{}},merges+joined};continue;}
            if(dsu.rank[a]<dsu.rank[r])std::swap(a,r);
            dsu.parent[r]=a;dsu.parity[r]=p^q^want;if(dsu.rank[a]==dsu.rank[r])++dsu.rank[a];++joined;
        }
        if(!joined)return {std::move(pc),merges};
        merges+=joined;ParityComponents next;std::array<int,64> indices;indices.fill(-1);
        for(unsigned i=0;i<n;++i){auto [r,p]=dsu.find(i);if(indices[r]<0){indices[r]=int(next.sides.size());next.sides.push_back({0,0});}auto& s=next.sides[indices[r]];s[p]|=pc.sides[i][0];s[p^1]|=pc.sides[i][1];}
        pc=std::move(next);
    }
}
}
