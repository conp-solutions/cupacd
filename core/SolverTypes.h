/***********************************************************************************[SolverTypes.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef Minisat_SolverTypes_h
#define Minisat_SolverTypes_h

#include <assert.h>

#include "mtl/IntTypes.h"
#include "mtl/Alg.h"
#include "mtl/Vec.h"
#include "mtl/Map.h"
#include "mtl/Alloc.h"
#include "mtl/Sort.h" // for BIG sort

#include <iostream> // used for default display literals, clauses, ... into streams
#include <vector>   // used for the MarkArray class

#define PBWsize 3   // a PB weight and literal pair should be stored in every 3 literals (however, 4 results in much faster accesses)


namespace Minisat {

//=================================================================================================
// Variables, literals, lifted booleans, clauses:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#define var_Undef (-1)
#define var_Error (-2) // to have another indicator when collecting a variable during iterating over a set, but when 3 states are required


struct Lit {
    int     x;

    // Use this as a constructor:
    friend Lit mkLit(Var var, bool sign = false);

    bool operator == (Lit p) const { return x == p.x; }
    bool operator != (Lit p) const { return x != p.x; }
    bool operator <  (Lit p) const { return x < p.x;  } // '<' makes p, ~p adjacent in the ordering.
    bool operator >  (Lit p) const { return x > p.x;  } // add the other way around
};


inline  Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }
inline  Lit  operator ~(Lit p)              { Lit q; q.x = p.x ^ 1; return q; }
inline  Lit  operator ^(Lit p, bool b)      { Lit q; q.x = p.x ^ (unsigned int)b; return q; }
inline  bool sign      (Lit p)              { return p.x & 1; }
inline  int  var       (Lit p)              { return p.x >> 1; }

// Mapping Literals to and from compact integers suitable for array indexing:
inline  int  toInt     (Var v)              { return v; } 
inline  int  toInt     (Lit p)              { return p.x; } 
inline  Lit  toLit     (int i)              { Lit p; p.x = i; return p; } 

//const Lit lit_Undef = mkLit(var_Undef, false);  // }- Useful special constants.
//const Lit lit_Error = mkLit(var_Undef, true );  // }

const Lit lit_Undef = { -2 };  // }- Useful special constants.
const Lit lit_Error = { -1 };  // }


//=================================================================================================
// Lifted booleans:
//
// NOTE: this implementation is optimized for the case when comparisons between values are mostly
//       between one variable and one constant. Some care had to be taken to make sure that gcc 
//       does enough constant propagation to produce sensible code, and this appears to be somewhat
//       fragile unfortunately.

#define l_True  (lbool((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
#define l_False (lbool((uint8_t)1))
#define l_Undef (lbool((uint8_t)2))

class lbool {
    uint8_t value;

public:
    explicit lbool(uint8_t v) : value(v) { }

    lbool()       : value(0) { }
    explicit lbool(bool x) : value(!x) { }

    bool  operator == (lbool b) const { return ((b.value&2) & (value&2)) | (!(b.value&2)&(value == b.value)); }
    bool  operator != (lbool b) const { return !(*this == b); }
    lbool operator ^  (bool  b) const { return lbool((uint8_t)(value^(uint8_t)b)); }

    lbool operator && (lbool b) const { 
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xF7F755F4 >> sel) & 3;
        return lbool(v); }

    lbool operator || (lbool b) const {
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xFCFCF400 >> sel) & 3;
        return lbool(v); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};
inline int   toInt  (lbool l) { return l.value; }
inline lbool toLbool(int   v) { return lbool((uint8_t)v);  }

//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause;
typedef RegionAllocator<uint32_t>::Ref CRef;

class Clause {
    struct {
        unsigned mark      : 2;
        unsigned learnt    : 1;
        unsigned has_extra : 1;
        unsigned reloced   : 1;
	unsigned is_pb     : 1;  // indicate that the current object is a PB constraint instead of a clause
        unsigned size      : 26; }                            header;
    union { Lit lit; float act; uint32_t abs; CRef rel; } data[0];

    friend class ClauseAllocator;

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    template<class V>
    Clause(const V& ps, bool use_extra, bool learnt) {
        header.mark      = 0;
        header.learnt    = learnt;
        header.has_extra = use_extra;
        header.reloced   = 0;
	header.is_pb     = 0;  // by default the clause is not a PB constraint
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) 
            data[i].lit = ps[i];

        if (header.has_extra){
            if (header.learnt)
                data[header.size].act = 0; // its not a PB constraint, so everything is fine
            else 
                calcAbstraction(); }
    }

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    /** constructor for a clause that actually is a PB constraint: \sum w_i l_i <= k
     * has literals and weights as parameters, and the threshold
     */
    template<class V>
    Clause(const V& literals, const vec<int64_t>& weights, int64_t threshold, bool use_extra, bool learnt) {
        header.mark      = 0;
        header.learnt    = learnt;
        header.has_extra = use_extra;
        header.reloced   = 0;
	header.is_pb     = 1;  // this will be a PB object
        header.size      = literals.size();

	assert( sizeof(Lit) * 2 == sizeof( int64_t ) && "a weight should be stored in two literals" );
	
	// memory layout:
	// data.lit: Lit1 Lit2 Lit3 Lit4 Lit5 Lit6 Lit7 Lit8 Lit9 Lit10 Lit11
	// pb-data:  Threshold Lit1  Weight1  Lit2  Weight2  Lit3  Weight3  
	
	// store the threshold
	*((int64_t*)(&data[0].lit)) = threshold;
	
	// store the literals
        for (int i = 0; i < literals.size(); i++) {
            data[ PBWsize * i+2].lit = literals[i];
	}
	// store the weights
	for (int i = 0; i < weights.size(); i++) {
            *((int64_t*)(&data[ PBWsize * i+ PBWsize].lit)) = weights[i]; // cast into uin64_t to store the weight
	}

	// enable the constraint to have an activity
        if (header.has_extra){
            if (header.learnt)
                data[header.size* PBWsize + PBWsize ].act = 0; 
	}

    }  
    
public:
    void calcAbstraction() {
        assert(header.has_extra);
	assert(header.is_pb == 0 && "should not calculate the abstraction of PB constraints" );
        uint32_t abstraction = 0;
	if( header.is_pb ) {
	  for (int i = 0; i < size(); i++)
	      abstraction |= 1 << (var(data[i].lit) & 31);
	} else {
	  for (int i = 0; i < size(); i++)
	      abstraction |= 1 << (var( pbLit(i) ) & 31);
	}
        data[header.is_pb ? header.size * PBWsize + PBWsize : header.size].abs = abstraction;  }


    int          size        ()      const   { return header.size; }
    void         shrink      (int i)         { assert(i <= size()); if (header.has_extra) data[header.size-i] = data[header.size]; header.size -= i; }
    void         pop         ()              { shrink(1); }
    bool         learnt      ()      const   { return header.learnt; }
    bool         has_extra   ()      const   { return header.has_extra; }
    uint32_t     mark        ()      const   { return header.mark; }
    void         mark        (uint32_t m)    { header.mark = m; }
    const Lit&   last        ()      const   { return data[header.size-1].lit; }

    bool         reloced     ()      const   { return header.reloced; }
    CRef         relocation  ()      const   { return data[0].rel; }
    void         relocate    (CRef c)        { header.reloced = 1; data[0].rel = c; }

    // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    Lit&         operator [] (int i)         { return data[i].lit; }
    Lit          operator [] (int i) const   { return data[i].lit; }
    operator const Lit* (void) const         { return (Lit*)data; }

    float&       activity    ()              { assert(header.has_extra); return data[header.is_pb ? header.size * PBWsize + PBWsize : header.size].act; }
    const float& activity    () const        { assert(header.has_extra); return data[header.is_pb ? header.size * PBWsize + PBWsize : header.size].act; }
    uint32_t     abstraction () const        { assert(header.has_extra); return data[header.is_pb ? header.size * PBWsize + PBWsize : header.size].abs; }

    Lit          subsumes    (const Clause& other) const;
    void         strengthen  (Lit p);
    
    // extra PB functions
    // the PB constraints is: \sum w_i l_i \le threshold (use less equal)
    bool        isPBconstraint()    const   { return header.is_pb; } // return whether the current object is a PB constraint
    void        setPBconstraint()           { header.is_pb = true; } // tell the clause that it actually is a PB constraint (only use right after constructing/reallocating the data structure!)
    
    Lit&        pbLit (int i)           { return data[PBWsize * i+2].lit; } // write access to PB literals
    Lit         pbLit (int i) const     { return data[PBWsize * i+2].lit; } // read access to PB literals
    
    int64_t&    pbWeight (int i)        { return *((int64_t*)(&data[PBWsize *i+PBWsize].lit)); } // write access to PB weights
    int64_t     pbWeight (int i) const  { return *((int64_t*)(&data[PBWsize *i+PBWsize].lit)); } // read access to PB weights   
  
    int64_t&    pbThreshold ()        { return *((int64_t*)(&data[0].lit)); } // write access to constraint threshold
    int64_t     pbThreshold () const  { return *((int64_t*)(&data[0].lit)); } // read access to constraint threshold
    
    Clause(const Clause& other) {
      // copy the header information
        header.mark      = other.header.mark;
        header.learnt    = other.header.learnt;
        header.has_extra = other.header.has_extra;
        header.reloced   = other.header.reloced;
	header.is_pb     = other.header.is_pb;
        header.size      = other.header.size;
      // copy all literals
	if( other.header.is_pb ) {
	  for (int i = 0; i <= other.size()* PBWsize + PBWsize ; i++)  // there are more literals for PB constraints, copy all of them (weights and threshold)
	      data[i].lit = other[i];
	} else {
	  for (int i = 0; i < other.size(); i++) // just copy the literals of the clause
	      data[i].lit = other[i];
	}
      // fill abstraction/activity info
        if (header.has_extra){
            if (header.learnt)
                activity() = other.activity(); // its not a PB constraint, so everything is fine
            else 
                calcAbstraction(); }
    }
};

/** enum to determine the type of the clause returned by conflict analysis */
enum ClauseType {
  usualClause = 0,
  pbConstraint = 1,
  emptyClause = 2, 
}; 

//=================================================================================================
// ClauseAllocator -- a simple class for allocating memory for clauses:


const CRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;
class ClauseAllocator : public RegionAllocator<uint32_t>
{
    static int clauseWord32Size(int size, bool has_extra){
        return (sizeof(Clause) + (sizeof(Lit) * (size + (int)has_extra))) / sizeof(uint32_t); }
 public:
    bool extra_clause_field;

    ClauseAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), extra_clause_field(false){}
    ClauseAllocator() : extra_clause_field(false){}

    void moveTo(ClauseAllocator& to){
        to.extra_clause_field = extra_clause_field;
        RegionAllocator<uint32_t>::moveTo(to); }

    template<class Lits>
    CRef alloc(const Lits& ps, bool learnt = false) // allocate a usual clause
    {
        assert(sizeof(Lit)      == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));
        bool use_extra = learnt | extra_clause_field;

	assert( ps.size() > 0 && "only clauses with an actual size should be alocated" );
	// std::cerr << "c called alloc for clause " << ps << " with parameter " << clauseWord32Size(ps.size() , use_extra) << " and extra: " << use_extra << std::endl;
	
        CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(ps.size(), use_extra));
        new (lea(cid)) Clause(ps, use_extra, learnt);

        return cid;
    }


    template<class Lits>
    CRef alloc(const Lits& ps, const vec<int64_t>& weights, int64_t threshold, bool learnt = false)
    {
        assert(sizeof(Lit)      == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));
	assert(sizeof(Lit) * 2  == sizeof(int64_t));
        bool use_extra = learnt | extra_clause_field;

	// std::cerr << "c called alloc for PB " << ps << " with weights " << weights << " with parameter " << clauseWord32Size(ps.size() * PBWsize + PBWsize , use_extra) << " and extra: " << use_extra << std::endl;
	// the PB constraint contains for each literal PBWsize literals, and another 2 literals for the threshold // TODO: use factor 4, so that accesses get faster! carefully check all locations (e.g. delete)
        CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(ps.size() * PBWsize + PBWsize , use_extra));
        new (lea(cid)) Clause(ps, weights, threshold, use_extra, learnt); // create the PB object with a placement allocator

        return cid;
    }
    
    /** allocate the space for a PB clause */
    CRef allocPB(const Clause& clause) 
    {
        assert( clause.isPBconstraint() && "use this allocate method only for PB constraints" );
        bool use_extra = clause.learnt() | extra_clause_field;

	// std::cerr << "c called alloc for PB " << clause << " with parameter " << clauseWord32Size(clause.size() * PBWsize + PBWsize , use_extra) << std::endl;
	
        CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(clause.size() * PBWsize + PBWsize , use_extra));
        new (lea(cid)) Clause(clause);

        return cid;
    }

    
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Clause&       operator[](Ref r)       { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    const Clause& operator[](Ref r) const { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    Clause*       lea       (Ref r)       { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    const Clause* lea       (Ref r) const { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    Ref           ael       (const Clause* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(CRef cid)
    {
        const Clause& c = operator[](cid);
	// std::cerr << "c call free with " << c << " and size " << clauseWord32Size( c.isPBconstraint() ? (c.size()*PBWsize + PBWsize) : c.size(), c.has_extra()) << " and extra " << c.has_extra()  << std::endl;
        RegionAllocator<uint32_t>::free(clauseWord32Size( c.isPBconstraint() ? (c.size()*PBWsize + PBWsize) : c.size(), c.has_extra())); // free the right amount of memoty
    }

    void reloc(CRef& cr, ClauseAllocator& to)
    {
        Clause& c = operator[](cr);
        
        if (c.reloced()) { cr = c.relocation(); return; }

	// std::cerr << "c relocate [" << cr << "] : " << c << " with extra: " << c.has_extra() << std::endl;
        if( ! c.isPBconstraint() ) cr = to.alloc(c, c.learnt());  // usual clause alloc method, calls the constructor of the clause
        else { 
// 	  std::cerr << "c reloc clause[" << cr << "] " << c << " with extra: " << c.has_extra() << std::endl;
	  cr = to.allocPB(c);                                  // here the PB constraint is simply copied literal by literal
	}
	
        c.relocate(cr);
	// std::cerr << "c       to [" << cr << "] : " << to[cr] << " with extra: " << to[cr].has_extra() << std::endl;
        
        // Copy extra data-fields: 
        // (This could be cleaned-up. Generalize Clause-constructor to be applicable here instead?)
        to[cr].mark(c.mark());
        if (to[cr].learnt())         to[cr].activity() = c.activity();
        else if (to[cr].has_extra()) to[cr].calcAbstraction();
	if( c.isPBconstraint() ) to[cr].setPBconstraint (); // remember whether the current constraint was a PB constraint

    }
};


//=================================================================================================
// OccLists -- a class for maintaining occurence lists with lazy deletion:

template<class Idx, class Vec, class Deleted>
class OccLists
{
    vec<Vec>  occs;
    vec<char> dirty;
    vec<Idx>  dirties;
    Deleted   deleted;

 public:
    OccLists(const Deleted& d) : deleted(d) {}
    
    void  init      (const Idx& idx){ occs.growTo(toInt(idx)+1); dirty.growTo(toInt(idx)+1, 0); }
    // Vec&  operator[](const Idx& idx){ return occs[toInt(idx)]; }
    Vec&  operator[](const Idx& idx){ return occs[toInt(idx)]; }
    Vec&  lookup    (const Idx& idx){ if (dirty[toInt(idx)]) clean(idx); return occs[toInt(idx)]; }

    void  cleanAll  ();
    void  clean     (const Idx& idx);
    void  smudge    (const Idx& idx){
        if (dirty[toInt(idx)] == 0){
            dirty[toInt(idx)] = 1;
            dirties.push(idx);
        }
    }

    void  clear(bool free = true){
        occs   .clear(free);
        dirty  .clear(free);
        dirties.clear(free);
    }
};


template<class Idx, class Vec, class Deleted>
void OccLists<Idx,Vec,Deleted>::cleanAll()
{
    for (int i = 0; i < dirties.size(); i++)
        // Dirties may contain duplicates so check here if a variable is already cleaned:
        if (dirty[toInt(dirties[i])])
            clean(dirties[i]);
    dirties.clear();
}


template<class Idx, class Vec, class Deleted>
void OccLists<Idx,Vec,Deleted>::clean(const Idx& idx)
{
    Vec& vec = occs[toInt(idx)];
    int  i, j;
    for (i = j = 0; i < vec.size(); i++)
        if (!deleted(vec[i]))
            vec[j++] = vec[i];
    vec.shrink(i - j);
    dirty[toInt(idx)] = 0;
}


//=================================================================================================
// CMap -- a class for mapping clauses to values:


template<class T>
class CMap
{
    struct CRefHash {
        uint32_t operator()(CRef cr) const { return (uint32_t)cr; } };

    typedef Map<CRef, T, CRefHash> HashTable;
    HashTable map;
        
 public:
    // Size-operations:
    void     clear       ()                           { map.clear(); }
    int      size        ()                const      { return map.elems(); }

    
    // Insert/Remove/Test mapping:
    void     insert      (CRef cr, const T& t){ map.insert(cr, t); }
    void     growTo      (CRef cr, const T& t){ map.insert(cr, t); } // NOTE: for compatibility
    void     remove      (CRef cr)            { map.remove(cr); }
    bool     has         (CRef cr, T& t)      { return map.peek(cr, t); }

    // Vector interface (the clause 'c' must already exist):
    const T& operator [] (CRef cr) const      { return map[cr]; }
    T&       operator [] (CRef cr)            { return map[cr]; }

    // Iteration (not transparent at all at the moment):
    int  bucket_count() const { return map.bucket_count(); }
    const vec<typename HashTable::Pair>& bucket(int i) const { return map.bucket(i); }

    // Move contents to other map:
    void moveTo(CMap& other){ map.moveTo(other.map); }

    // TMP debug:
    void debug(){
        printf(" --- size = %d, bucket_count = %d\n", size(), map.bucket_count()); }
};


/*_________________________________________________________________________________________________
|
|  subsumes : (other : const Clause&)  ->  Lit
|  
|  Description:
|       Checks if clause subsumes 'other', and at the same time, if it can be used to simplify 'other'
|       by subsumption resolution.
|  
|    Result:
|       lit_Error  - No subsumption or simplification
|       lit_Undef  - Clause subsumes 'other'
|       p          - The literal p can be deleted from 'other'
|________________________________________________________________________________________________@*/
inline Lit Clause::subsumes(const Clause& other) const
{
    //if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
    //if (other.size() < size() || (!learnt() && !other.learnt() && (extra.abst & ~other.extra.abst) != 0))
    assert(!header.learnt);   assert(!other.header.learnt);
    assert(header.has_extra); assert(other.header.has_extra);
    if (other.header.size < header.size || (data[header.size].abs & ~other.data[other.header.size].abs) != 0)
        return lit_Error;

    Lit        ret = lit_Undef;
    const Lit* c   = (const Lit*)(*this);
    const Lit* d   = (const Lit*)other;

    for (unsigned i = 0; i < header.size; i++) {
        // search for c[i] or ~c[i]
        for (unsigned j = 0; j < other.header.size; j++)
            if (c[i] == d[j])
                goto ok;
            else if (ret == lit_Undef && c[i] == ~d[j]){
                ret = c[i];
                goto ok;
            }

        // did not find it
        return lit_Error;
    ok:;
    }

    return ret;
}

inline void Clause::strengthen(Lit p)
{
    remove(*this, p);
    calcAbstraction();
}


/** class that is used as mark array */
class MarkArray {
private:
	std::vector<uint32_t> array;
	uint32_t step;

public:
	MarkArray ():
	 step(0)
	 {}

	~MarkArray ()
	{
	  destroy();
	}

	void destroy() {
	  std::vector<uint32_t>().swap(array);
	  step = 0;
	}

	void create(const uint32_t newSize){
	  array.resize(newSize);
	  memset( &(array[0]), 0 , sizeof( uint32_t) * newSize );
	}

	void capacity(const uint32_t newSize) {
	  if( newSize > array.size() ) {
	    array.resize(newSize, 0); // add 0 as element
	  }
	}
	
	void resize(const uint32_t newSize) {
	  if( newSize > array.size() ) {
	    array.resize(newSize, 0); // add 0 as element
	  }
	}

	/** reset the mark of a single item
	 */
	void reset( const uint32_t index ) {
	  array[index] = 0;
	}

	/** reset the marks of the whole array
	 */
	void reset() {
	  memset( &(array[0]), 0 , sizeof( uint32_t) * array.size() );
	  step = 0;
	}

	/** give number of next step. if value becomes critical, array will be reset
	 */
	uint32_t nextStep() {
	  if( step >= 1 << 30 ) reset();
	  return ++step;
	}

	/** returns whether an item has been marked at the current step
	 */
	bool isCurrentStep( const uint32_t index ) const {
	  return array[index] == step;
	}

	/** set an item to the current step value
	 */
	void setCurrentStep( const uint32_t index ) {
	  array[index] = step;
	}

	/** check whether a given index has the wanted index */ 
	bool hasSameStep( const uint32_t index, const uint32_t comparestep ) const {
	  return array[index] == comparestep;
	}

	uint32_t size() const {
	  return array.size();
	}

	uint32_t getIndex(uint32_t index) const { return array[index]; }

};


/** class representing the binary implication graph of the formula */
class BIG 
{
  // TODO implement a weak "implies" check based on the implication graph sampling!
  Lit* storage;
  int* sizes;
  Lit** big;

  /** these two arrays can be used to check whether a literal l implies another literal l'
   *  Note: this is not a complete check!
   */
  uint32_t *start; // when has to literal been touch when scanning the BIG
  uint32_t *stop;  // when has to literal been finished during scanning
  
  int duringCreationVariables; // number of variables for the last construction call

//   uint32_t stampLiteral( const Lit literal, uint32_t stamp, int32_t* index, deque< Lit >& stampQueue );
  void shuffle( Lit* adj, int size ) const;

public:
  BIG();
  ~BIG();

  /** adds binary clauses */
  void create( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list);
  void create( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2);

  /** recreate the big after the formula changed */
  void recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list);
  void recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2);
  
  /** return the number of variables that are known by the BIG */
  uint32_t getVars() const { return duringCreationVariables; }
  
  /** removes an edge from the graph again */
  void removeEdge(const Lit l0, const Lit l1 );

  /** check all implication lists for duplicates and remove the duplicates 
   * Note: side effect, the arrays are sorted
   */
  void removeDuplicateEdges(const uint32_t nVars);
  
  /** sort all the arrays */
  void sort(const uint32_t nVars);
  
  Lit* getArray(const Lit l);
  const Lit* getArray(const Lit l) const;
  int getSize(const Lit l) const;

//   /** will travers the BIG and generate the start and stop indexes to check whether a literal implies another literal
//    * @return false, if BIG is not initialized yet
//    */
//   void generateImplied(Coprocessor::CoprocessorData& data);
//   void generateImplied( uint32_t nVars, vec<Lit>& tmpLits ); // alternative interface, to be able to use it during search!
//   
//   /** fill the literals in the order they would appear in a BFS in the big, starting with root nodes 
//    *  NOTE: will pollute the data.ma MarkArray
//    * @param rootsOnly: fill the vector only with root literals
//    */
//   void fillSorted( vector< Lit >& literals, Coprocessor::CoprocessorData& data, bool rootsOnly = true, bool getAll=false);
//   void fillSorted(vector<Var>& variables, CoprocessorData& data, bool rootsOnly = true, bool getAll=false);

  /** return true, if the condition "from -> to" holds, based on the stochastic scanned data */
  bool implies(const Lit& from, const Lit& to) const;

  /** return whether child occurs in the adjacence list of parent (and thus implied) */
  bool isChild(const Lit& parent, const Lit& child) const ;

  /** return whether one of the two literals is a direct child of parent (and thus implied)  */
  bool isOneChild( const Lit& parent, const Lit& child1, const Lit& child2 ) const ;
  
  /** get indexes of BIG scan algorithm */
  uint32_t getStart( const Lit& l ) { return start != 0 && var(l) < duringCreationVariables ? start[ toInt(l) ] : 0; }
  /** get indexes of BIG scan algorithm */
  uint32_t getStop( const Lit& l ) { return stop != 0 && var(l) < duringCreationVariables  ? stop[ toInt(l) ] : 0; }
};

inline BIG::BIG()
: storage(0), sizes(0), big(0), start(0), stop(0), duringCreationVariables(0)
{}

inline BIG::~BIG()
{
 if( big != 0 )    { free( big ); big = 0; }
 if( storage != 0 ){ free( storage ); storage = 0; }
 if( sizes != 0 )  { free( sizes ); sizes = 0 ; }
 if( start != 0 ) { free( start ); start = 0; }
 if( stop != 0 ) { free( stop ); stop = 0; }
 
}

inline void BIG::create(ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = (int*) malloc( sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.mark() ) continue;
    sizes[ toInt( ~c[0] )  ] ++;
    sizes[ toInt( ~c[1] )  ] ++;
    sum += 2;
  }
  storage = (Lit*) malloc( sizeof(Lit) * sum );
  big =  (Lit**)malloc ( sizeof(Lit*) * nVars * 2 );
  // memset(sizes,0, sizeof(Lit*) * nVars * 2 );
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( uint32_t i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.mark() ) continue;
    const Lit l0 = c[0]; const Lit l1 = c[1];
    
    ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
    ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
    sizes[toInt(~l0)] ++;
    sizes[toInt(~l1)] ++;
  }
}

inline void BIG::create(ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = (int*) malloc( sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.mark() ) continue;
      sizes[ toInt( ~c[0] )  ] ++;
      sizes[ toInt( ~c[1] )  ] ++;
      sum += 2;
    }
  }
  storage = (Lit*) malloc( sizeof(Lit) * sum );
  big =  (Lit**)malloc ( sizeof(Lit*) * nVars * 2 );
  // memset(sizes,0, sizeof(Lit*) * nVars * 2 );
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( uint32_t i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.mark() ) continue;
      const Lit l0 = c[0]; const Lit l1 = c[1];
      ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
      ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
      sizes[toInt(~l0)] ++;
      sizes[toInt(~l1)] ++;
    }
  }
}


inline void BIG::recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = sizes == 0 ? (int*) malloc( sizeof(int) * nVars * 2 ) : (int*) realloc( sizes, sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.mark() ) continue;
    sizes[ toInt( ~c[0] )  ] ++;
    sizes[ toInt( ~c[1] )  ] ++;
    sum += 2;
  }
  storage = storage == 0 ? (Lit*) malloc( sizeof(Lit) * sum ) : (Lit*) realloc( storage, sizeof(Lit) * sum )  ;
  big = big == 0 ? (Lit**)malloc ( sizeof(Lit*) * nVars * 2 ) : (Lit**)realloc ( big, sizeof(Lit*) * nVars * 2 );
  // should not be necessary!
  memset(storage,0, sizeof(Lit) * sum );
  memset(big, 0, sizeof(Lit*) * nVars * 2 ); 
  
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( uint32_t i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.mark() ) continue;
    const Lit l0 = c[0]; const Lit l1 = c[1];
    ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
    ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
    sizes[toInt(~l0)] ++;
    sizes[toInt(~l1)] ++;
  }
}

inline void BIG::recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = sizes == 0 ? (int*) malloc( sizeof(int) * nVars * 2 ) : (int*) realloc( sizes, sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.mark() ) continue;
      sizes[ toInt( ~c[0] )  ] ++;
      sizes[ toInt( ~c[1] )  ] ++;
      sum += 2;
    }
  }
  storage = storage == 0 ? (Lit*) malloc( sizeof(Lit) * sum ) : (Lit*) realloc( storage, sizeof(Lit) * sum )  ;
  big = big == 0 ? (Lit**)malloc ( sizeof(Lit*) * nVars * 2 ) : (Lit**)realloc ( big, sizeof(Lit*) * nVars * 2 );
  // should not be necessary!
  memset(storage,0, sizeof(Lit) * sum );
  memset(big, 0, sizeof(Lit*) * nVars * 2 ); 
  
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( uint32_t i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.mark() ) continue;
      const Lit l0 = c[0]; const Lit l1 = c[1];
      ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
      ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
      sizes[toInt(~l0)] ++;
      sizes[toInt(~l1)] ++;
    }
  }
}

inline void BIG::removeDuplicateEdges(const uint32_t nVars)
{
  const int maxVar = duringCreationVariables < nVars ? duringCreationVariables : nVars; // use only known variables
  for( Var v = 0 ; v < maxVar; ++v ) {
    for( int p = 0 ;p < 2 ; ++ p ) {
      const Lit l = mkLit(v,p==1);
      if( getSize(l) == 0 ) continue; // not for empty lists!
      Minisat::sort( getArray(l), getSize(l) );
      int j = 0;
      for( int i = 1; i < getSize(l); ++i ) {
	assert( getArray(l)[i-1] < getArray(l)[i] && "implication list should be ordered" );
	if( getArray(l)[i] != getArray(l)[j] ) getArray(l)[++j] = getArray(l)[i]; // keep elements, if they are not equal to the last element!
      }
      sizes[ toInt(l) ] = j+1; // update size information
    }
  }
}

inline void BIG::sort(const uint32_t nVars){
  const int maxVar = duringCreationVariables < nVars ? duringCreationVariables : nVars; // use only known variables
  for( Var v = 0 ; v < maxVar; ++v ) {
    for( int p = 0 ;p < 2 ; ++ p ) {
      const Lit l = mkLit(v,p==1);
      if( getSize(l) == 0 ) continue; // not for empty lists!
      Minisat::sort( getArray(l), getSize(l) );
    }
  }
}

inline void BIG::removeEdge(const Lit l0, const Lit l1)
{
  // remove literal from the two lists
  Lit* list = getArray( ~l0 );
  const int size = getSize( ~l0 );
  for( int i = 0 ; i < size; ++i )
  {
    if( list[i] == l1 ) {
      list[i] = list[ size - 1 ];
      sizes[ toInt(~l0) ] --;
      break;
    }
  }
  Lit* list2 = getArray( ~l1 );
  const int size2 = getSize( ~l1 );
  for( int i = 0 ; i < size2; ++i )
  {
    if( list2[i] == l0 ) {
      list2[i] = list2[ size2 - 1 ];
      sizes[ toInt(~l1) ] --;
      break;
    }
  }
}

inline Lit* BIG::getArray(const Lit l)
{
  return var(l) < duringCreationVariables ? big[ toInt(l) ] : 0;
}

inline const Lit* BIG::getArray(const Lit l) const
{
  return var(l) < duringCreationVariables ? big[ toInt(l) ] : 0;
}

inline int BIG::getSize(const Lit l) const
{
  return var(l) < duringCreationVariables ? sizes[ toInt(l) ] : 0;
}

inline void BIG::shuffle( Lit* adj, int size ) const
{
  for( int i = 0 ;  i+1<size; ++i ) {
    const int rnd = rand() % size;
    const Lit tmp = adj[i];
    adj[i] = adj[rnd];
    adj[rnd] = tmp;
  }
}

inline bool BIG::implies(const Lit& from, const Lit& to) const
{
  if( start == 0 || stop == 0 || var(from) >= duringCreationVariables || var(to) >= duringCreationVariables ) return false;
  return ( start[ toInt(from) ] < start[ toInt(to) ] && stop[ toInt(from) ] > stop[ toInt(to) ] )
   || ( start[ toInt(~to) ] < start[ toInt(~from) ] && stop[ toInt(~to) ] > stop[ toInt(~from) ] );
}

inline bool BIG::isChild(const Lit& parent, const Lit& child) const
{
  const Lit * list = getArray(parent);
  const int listSize = getSize(parent);
  for( int j = 0 ; j < listSize; ++ j ) {
    if( list[j] == child )
      return true;
  }
  return false;
}

inline bool BIG::isOneChild(const Lit& parent, const Lit& child1, const Lit& child2) const
{
  const Lit * list = getArray(parent);
  const int listSize = getSize(parent);
  for( int j = 0 ; j < listSize; ++ j ) {
    if( list[j] == child1 || list[j] == child2 ) return true;
  }
  return false;
}


//=================================================================================================
}


/// print lbool value into a stream
inline std::ostream& operator<<(std::ostream& other, const Minisat::lbool& l ) {
  if( l == Minisat::lbool((uint8_t)1) ) other << "l_False";
  else if( l == Minisat::lbool((uint8_t)0) ) other << "l_True";
  else other << "l_Undef";
  return other;
}

/// print literals into a stream
inline std::ostream& operator<<(std::ostream& other, const Minisat::Lit& l ) {
  if( l == Minisat::lit_Undef ) other << "lUndef";
  else if( l == Minisat::lit_Error ) other << "lError";
  else other << (sign(l) ? "-" : "") << var(l) + 1;
  return other;
}

/// print a clause into a stream
inline std::ostream& operator<<(std::ostream& other, const Minisat::Clause& c ) {
  if( c.isPBconstraint() ) {
    for( int i = 0 ; i < c.size(); ++ i )
      other << " +" << c.pbWeight(i) << " " << c.pbLit(i);
    other << " <= " << c.pbThreshold();
  } else {
    for( int i = 0 ; i < c.size(); ++ i )
      other << " " << c[i];
  }

  return other;
}

/// print elements of a vector
template <typename T>
inline std::ostream& operator<<(std::ostream& other, const std::vector<T>& data ) 
{
  for( int i = 0 ; i < data.size(); ++ i )
    other << " " << data[i];
  return other;
}

/// print elements of a vector
template <typename T>
inline std::ostream& operator<<(std::ostream& other, const Minisat::vec<T>& data ) 
{
  for( int i = 0 ; i < data.size(); ++ i )
    other << " " << data[i];
  return other;
}

#endif
