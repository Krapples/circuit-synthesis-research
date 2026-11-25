#pragma once
// C++20 reference kernels for cared-row residual completion, 1..64 rows.
// Inputs are packed columns; all row masks are restricted to full.
// No SAT/UNSAT verdict about read-once realizability is returned here.
#include <array>
#include <cstdint>
#include <stdexcept>
#include <span>
#include <vector>
#include <utility>
#include <cstddef>
namespace residual_filter {
using Word = std::uint64_t;
inline Word row_mask(unsigned rows) {
    if (rows < 1 || rows > 64) throw std::invalid_argument("rows must be 1..64");
    return rows==64 ? ~Word{0} : ((Word{1}<<rows)-1);
}
struct Fibers {
    std::array<Word,64> mask{};
    unsigned size=0;
};
inline Fibers fibers(std::span<const Word> columns, Word full) {
    Fibers a; if (!full) return a;
    a.mask[0]=full; a.size=1;
    for (Word c: columns) {
        const unsigned n=a.size;
        for(unsigned i=0;i<n;++i) {
            Word x=a.mask[i]&c, y=a.mask[i]&~c;
            if(x&&y) { a.mask[i]=x; a.mask[a.size++]=y; }
            // If unsplit, original mask already equals the nonempty part.
        }
    }
    return a;
}
inline Word forced_ones(const Fibers& f,Word positive) {
    Word out=0;for(unsigned i=0;i<f.size;++i) if(f.mask[i]&positive) out|=f.mask[i];
    return out;
}
inline bool root_and_possible(const Fibers& a,const Fibers& b,Word positive) {
    return (forced_ones(a,positive)&forced_ones(b,positive))==positive;
}
// A consistent bipartite component is two masks of opposite forced provider
// values. Each component can flip independently. Isolated fibers have an empty
// second side. This describes all arbitrary Boolean provider columns on the
// observed rows, not necessarily all read-once provider columns.
struct ParityComponents {
    bool consistent=true;
    std::vector<std::array<Word,2>> sides;
};
struct ParityDSU {
    std::array<unsigned,64> parent{}, rank{}, parity{};
    explicit ParityDSU(unsigned n) {for(unsigned i=0;i<n;++i)parent[i]=i;}
    std::pair<unsigned,unsigned> find(unsigned i) {
        if(parent[i]==i)return {i,0};
        auto [r,p]=find(parent[i]); parity[i]^=p;parent[i]=r;return {r,parity[i]};
    }
    bool opposite(unsigned a,unsigned b) {
        auto [ra,pa]=find(a);auto [rb,pb]=find(b);
        if(ra==rb)return (pa^pb)==1;
        if(rank[ra]<rank[rb])std::swap(ra,rb);
        parent[rb]=ra;parity[rb]=pa^pb^1;
        if(rank[ra]==rank[rb])++rank[ra];
        return true;
    }
};
inline ParityComponents provider_components(const Fibers& inside,const Fibers& outside,Word positive,Word full) {
    ParityDSU d(inside.size);
    for(unsigned j=0;j<outside.size;++j) {
        Word p=outside.mask[j]&positive, n=outside.mask[j]&(full^positive);
        if(!p||!n)continue;
        unsigned pi=inside.size,ni=inside.size;
        for(unsigned i=0;i<inside.size;++i) {
            if(pi==inside.size&&(inside.mask[i]&p))pi=i;
            if(ni==inside.size&&(inside.mask[i]&n))ni=i;
        }
        if(pi==inside.size||ni==inside.size)throw std::invalid_argument("fiber partitions disagree");
        for(unsigned i=0;i<inside.size;++i) {
            if((inside.mask[i]&p)&&!d.opposite(i,ni))return {false,{}};
            if((inside.mask[i]&n)&&!d.opposite(i,pi))return {false,{}};
        }
    }
    ParityComponents out;std::array<int,64> index;index.fill(-1);
    for(unsigned i=0;i<inside.size;++i) {
        auto [r,p]=d.find(i);
        if(index[r]<0){index[r]=static_cast<int>(out.sides.size());out.sides.push_back({0,0});}
        out.sides[index[r]][p]|=inside.mask[i];
    }
    return out;
}
} // namespace residual_filter
