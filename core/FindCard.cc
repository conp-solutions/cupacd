/*************************************************************************************[FindCard.cc]
Copyright (c) 2012-2014, Norbert Manthey

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "mtl/Sort.h"
#include "core/SolverTypes.h"
#include "core/Solver.h"
#include "utils/System.h"

#include <vector>
#include <iostream>

using namespace Minisat;
using namespace std;

// data structures that are required for finding cardinality constraints
/** represent a (mixed) cardinality constraint*/
class CardC {
  public:
    vector<Lit> ll;
    vector<Lit> lr;
    int k;
    CardC( vector<Lit>& amo ) : ll(amo), k(1) {}; // constructor to add amo constraint
    CardC( vector<Lit>& amk, int _k ) : ll(amk), k(_k) {}; // constructor to add amk constraint
    CardC( const Clause& c ) :k(-1) { lr.resize(c.size(),lit_Undef); for(int i = 0 ; i < c.size(); ++i ) lr[i] = c[i]; }// constructor for usual clauses
    bool amo() const { return k == 1 && lr.size() == 0 ; }
    bool amt() const { return k == 2 && lr.size() == 0 ; }
    bool amk() const { return k >= 0 && lr.size() == 0 ; }
    bool alo() const { return k == -1 && ll.size() == 0; }
    bool alk() const { return k < 0 && ll.size() == 0; }
    bool isUnit() const { return (k + (int)lr.size()) == 0; } // all literals in ll have to be false, and all literals in lr have to be true
    bool failed() const { return (((int)lr.size() + k) < 0) ; }
    bool taut() const { return k >= (int)ll.size(); } // assume no literal appears both in ll and lr
    bool invalid() const { return k==0 && ll.size() == 0 && lr.size() == 0; } // nothing stored in the constraint any more
    void invalidate() { k=0;ll.clear();lr.clear();}
    CardC() : k(0) {} // default constructor
  };
  
/// structure to compare two literals
struct LitOrderHeapLt {
        vec<int>& cmp;
        bool operator () (int& x, int& y) const {
	    return cmp[ x ] > cmp[ y ]; 
        }
        LitOrderHeapLt(vec<int> & frequencies ) : cmp(frequencies) {}
};


/// struct to handle ternary clauses efficiently
struct Ternary {
  Lit lit [3];
  Ternary ( const Lit a, const Lit b, const Lit c )
  {
    lit[0] = ( a > b ? ( b > c ? c : b ) : ( a > c ? c : a ) ); // min
    lit[2] = ( a > b ? ( a > c ? a : c ) : ( b > c ? b : c)  ); // max
    lit[1] = toLit( toInt(a) ^ toInt(b) ^ toInt(c) ^ toInt( lit[0] ) ^ toInt( lit[2] ) ); // xor all three lits and min and max (the middle remains)
    
    
  }
  Lit operator[](const int position) const {
    return lit[position];
  }
};

/** this number returns the next bigger number with the same number of set bits
 */
uint64_t nextNbitNumber(uint64_t x) 
{
     uint64_t smallest, ripple, new_smallest, ones;

     if (x == 0) return 0;
     smallest     = (x & -x);
     ripple       = x + smallest;
     new_smallest = (ripple & -ripple);
     ones         = ((new_smallest/smallest) >> 1) - 1;
     return ripple | ones;
}


//
// implementation of frequently used small methods that should be inlined
//

/** class that measures the time between creation and destruction of the object, and adds it*/
class MethodTimer {
  double* pointer;
public:
  MethodTimer( double* timer ) : pointer( timer ) { *pointer = cpuTime() - *pointer;}
  ~MethodTimer() { *pointer = cpuTime() - *pointer; }
};  

/**
 * 
 *  here, code for semantic analysis
 * 
 */
void Solver::findCardsSemantic( void* vectorCardC ) {
  
	assert( decisionLevel() == 0 && "will look for card constraints only at level 0!" );
	vector<CardC>& cards = *((vector<CardC>*) vectorCardC );
	// merge-sort clauses according to size. smallest first
	double semTime = 0;
	semTime = cpuTime() - semTime; // time measurement
	
	// TODO: stats, limits, options
	int extendedCards = 0, failedExtendTries = 0, extendLits = 0, reducedDegrees = 0, totalProbes = 0, totalFailedProbes = 0, nrDisabledClauses = 0, units = 0;
	uint64_t semSteps = 0;
	
	vec<CRef> disabledClauses;	// memorize which clauses have been set to "mark() != 0", so that this change can be undone after the method!
	
	const int32_t n = clauses.size();
	int32_t m, s;
	// copy elements from vector
	CRef* tmpA = new CRef[ n ];
	CRef* a = tmpA;
	for( int32_t i = 0 ; i < n; i++ ){
		a[i] = clauses[i];
	}
	CRef *tmpB = new CRef[n];
	CRef *b = tmpB;

	// size of work fields, power of 2	
	for (s=1; s<n; s+=s)
	{
		m = n;
		do {
			m = m - 2*s;	// set begin of working field
			int32_t hi = (m+s > 0) ? m + s : 0;	// set middle of working field
			
			int32_t i = (m > 0) ? m : 0;	// lowest position in field
			int32_t j = hi;
			
			int32_t stopb = m + 2*s;	// upper bound of current work area
			int32_t currentb = i;			// current position in field for copy
			
			// merge two sorted fields into one
			while( i < hi && j < stopb)
			{
				if( ( ca[a[i]].size() ) < ( ca[a[j]].size()  )  ) // compare size!
					b[currentb++] = a[i++];
				else
					b[currentb++] = a[j++];
			}
			// copy rest of the elements
			for( ; i < hi; )
				b[currentb++] = a[i++];
				
			for( ; j< stopb; 	)
				b[currentb++] = a[j++];
				
		} while( m > 0 );
		
		// swap fields!
		CRef* tmp = a;a = b;b = tmp;
	}
	delete [] tmpB;

	// create occ lists, for each clause watch the smallest literal (should be sufficient)
	vector< vector<CRef> > occ ( 2 * nVars() );
	for( int i = 0 ; i < n; ++ i ) {
	  Clause& c = ca[ tmpA[i] ];	// not ensured to be sorted, hence check smallest literal
	  if( c.mark() || c.size() == 0 ) continue;
	  Lit minLit = c[0];
	  for( int j = 1; j < c.size(); ++ j ) if( c[0] < minLit ) minLit = c[0]; // if its the minimum, later disabling clauses is cheaper
	  occ [ toInt( minLit ) ]. push_back( tmpA[i] );
	}
	semSteps += n;	// approximate sorting
	
	vec<Lit> lits;
	vector<Lit> cc; // literals for the cardinality constraints
	vector<Lit> origCC; // literals of original CC
	int degree = 0; // threshold for the constraint
	MarkArray intersection;
	intersection.create( 2 * nVars() ); // set a flag for each literal
	intersection.nextStep();
	// work on array tmpA with current clauses
	for( int i = 0 ; i < n && (opt_pb_unlimited || (semSteps < opt_pb_semSearchLimit) ); ++ i ) { // for all the clauses (all of them are still watched), and within the limits
	  Clause& c = ca[ tmpA[i] ];
	  semSteps ++;
	  if( c.mark() != 0 || c.isPBconstraint() ) continue; // this clause has been used for a card constraint already
	  if( satisfied(c) ) continue;	// do not use clauses, which are already satisfied by units in the solver

	  if( ! opt_pb_unlimited && (c.size() < opt_pb_minCardClauseSize || c.size() > opt_pb_maxCardClauseSize )) continue; // reject certain sizes of cardinality constraints!

	  // otherwise, setup the current constraint ...
	  // for a clause C = (a,b,c,d,e), the card constraint is -a,-b,-c,-d,-e <= 4 generated, since at most 4 out of these complements can be satisfied 
	  cc.clear(); // new constraint
	  degree = -1; // from the negated literals of the clause, at most |C| - 1 literals can be true at the same time, because otherwise the clause falsifies them again
	  for( int j = 0 ; j < c.size(); ++ j ) {
	    if(  value( c[j] ) == l_Undef ) {	// handle only literals, that are not falsified yet already (or where the parameter says it does not care)
	      cc.push_back( ~c[j] ); // the complementary literals build the cardinality constraint!
	      degree ++;
	    }
	  }
	  const int origDegree = degree;	// memorize original degree
	  origCC = cc;
	  
	  if( degree > 63 ) {	// data structures do not support constraints with more than 63 bits
	    static bool didPrint = false;
	    if( !didPrint ) { cerr << "c cannot handle constraints with more than 63 literals!" << endl; didPrint = false; } // print this error message once!
	    continue;
	  }
	  
	  Lit extendLit = lit_Undef;
	  bool firstIteration = true; 
	  bool firstProbe = true;
	  intersection.nextStep();	// markArray the remembers the literals for the intersection
	  
	  if( opt_pb_semDebug ) cerr << endl << endl << "c start with card constraint " << cc << " <= " << degree  << "  --- by clause [" << tmpA[i] << "] " << c << endl;
	  
	  do {	// try to extend the card constraint with new literals by unit propagation

	    if( cc.size() > 62 ) {
	      static bool didPrint = false;
	      if( !didPrint ) { cerr << "c cannot handle constraints with more than 63 literals!" << endl; didPrint = false; } // print this error message once!
	      break;
	    }

	    if( !opt_pb_unlimited && semSteps >= opt_pb_semSearchLimit) break; // stop with the current state of the current cardinality constraint

	    extendLit = lit_Undef;
  
	    // for the "new" "degree" subsets of "degree" literals, check how many other literals are entailed as well
	    uint64_t bitField = 0;
	    for( int j = 0 ; j < degree; ++j ) { bitField = bitField << 1; bitField = (bitField | 1); } // set degree bits in the number, make sure the least siginificant bit is always set!
	    
	    if( opt_pb_semDebug ) cerr << "c start with number " << bitField << " for assign - bits ..." << endl;
	    int probes = 0, failedProbes = 0; // stats for number of propagations and failed propagations (to detect unsat)
	    while( true  ) { // find another k-bit number, until all possible combinations inside the range have been tested
	      if( firstIteration || (bitField & 1 != 0) ) { // consider this combination if its either the first iteration, or if the least siginificant bit is set
		if( opt_pb_semDebug ) cerr << "c probe " << probes << "  with bitfield " << bitField << " and with trail: " << trail << endl;
		newDecisionLevel(); // go to decision level 1!
		for( int j = 0 ; j < cc.size(); ++ j ) {	// add all literals where a bit in "bitField" is set
		  const uint64_t testPos = cc.size() - j - 1; // to hit least significant bit more easily
		  if( (bitField & (1ull << testPos)) != 0ull ) { // if the right bit is set
		    if( opt_pb_semDebug ) cerr << "c assume lit " << cc[j] << " , undefined: " << (value( cc[j] ) == l_Undef) << endl;
		    units ++;
		    uncheckedEnqueue( cc[j] ); // add all the literals, that should be propagated
		  }
		}
		probes ++;	// count number of propagations
		if( opt_pb_semDebug ) cerr << "c call propagate [" << bitField << "] " << probes << " with decL " << decisionLevel() << " and trail size " << trail.size() << endl;
		CRef confl = propagate(); // propagate, check for conflict
		semSteps += trail.size() - trail_lim[0];	// appeoximate propagation effort
		if( opt_pb_semDebug ) cerr << "c propagate [ " << confl << " ] implied " << trail << endl;
		if( confl == CRef_Undef ) { // no conflict -> build intersection
		  const int startTrail = trail_lim[0];
		  lits.clear(); // literals can be removed, because intersection is still in markArray
		  if( firstProbe ) {	// first probe -> initialize intersection
		    for( int j = trail_lim[0] + degree ; j < trail.size(); ++ j ) { intersection.setCurrentStep( toInt( trail[j] ) ); } // build intersection with vector and markArray wrt. the implied literals (not the "degree" enqueued ones)
		    for( int j = 0 ; j < cc.size(); ++ j ) {
		      if( opt_pb_semDebug ) cerr << "c reset lit " << ~cc[j] << " (set before " << intersection.isCurrentStep( toInt(~cc[j]) ) << ")" << endl;
		      intersection.reset( toInt( ~cc[j] ) ); // do not add literals of the constraint to the intersection
		    }
		    firstProbe = false;
		  } 
		  // build intersection
		  for( int j = trail_lim[0] ; j < trail.size(); ++ j ) {	// put only lits from the trail into lits, if they are already in the intersection (markArray)
		    if( intersection.isCurrentStep( toInt( trail[j] ) ) ) lits.push(trail[j]); 
		  } 
		  intersection.nextStep(); // update markArray to new intersection
		  for( int j = 0 ; j < lits.size(); ++ j ) intersection.setCurrentStep( toInt( lits[j] ) ); // set flag for all literals in the "new" intersection
		  if( opt_pb_semDebug ) cerr << "c kept " << lits.size() << " literals in the intersection: " << lits << endl;
		  
		} else { 
		  if( opt_pb_semDebug ) cerr << "c probe failed" << endl;
		  failedProbes ++;	// conflict -> everything is implied -> no intersection to be done!
		}
		cancelUntil( 0 );
		if( !firstProbe && lits.size() == 0 ) break; // intersection has been initialized, but became empty -> no commonly implied literal -> finished with the current constraint
	      }	// end probing current combination

	      if( ! opt_pb_unlimited && semSteps >= opt_pb_semSearchLimit ) { lits.clear(); break; } // add no more extension!
	      bitField = nextNbitNumber( bitField );
	      uint64_t tmp = 1, shift = cc.size();
	      tmp = (tmp << shift);
	      if( opt_pb_semDebug ) cerr << "c continue with bitfield " << bitField  << "( cmp. to. " << ( (uint64_t)1 << (uint64_t)cc.size()) << " == " << tmp << ") and cc.size: " << cc.size() << endl;
	      if( bitField >= tmp ) break;
	    }
	    
	    totalProbes += probes; totalFailedProbes += failedProbes;	// stats
	    if( firstProbe && (probes == failedProbes) ) {	// works only when nothing has been propagated yet! // TODO: what happens if this occurs after a literal has been added?
	      if( opt_pb_semDebug ) cerr << "c none of the configurations succeeds -> decrease degree by one to " << degree - 1 << endl;
	      degree --;	// decrease degree
	      reducedDegrees ++;	//stats
	      lits.clear();	// clear constraint and literals
	      break;		// TODO: could also continue here!
	    }
	    
	    // if the intersection of all of those is not empty, choose one literal (heuristically), and add it to the constraint -> next iteration!
	    if( lits.size() != 0 ) {
	      extendLit = lits[0];
	      cc.push_back( ~extendLit ); // add complement of current literal to card constraint
	      intersection.reset( toInt(~extendLit) );	// the complement is blocked, since it is inside CC now
	      if( opt_pb_semDebug ) cerr << "c add as [" << cc.size() << "] " << extendLit << " to CC" << endl;
	      lits.clear();
	    }
	    
	    firstIteration = false;	// in the next iteration, use only combinations with the new literal -> half the work
	    if( ! opt_pb_unlimited && semSteps >= opt_pb_semSearchLimit ) { lits.clear(); break; } // stop here due to limits
	  } while ( extendLit != lit_Undef && ( opt_pb_unlimited || lits.size() < opt_pb_maxCardSize) ); // repeat as long as something has been found and the card.constraint is not too long

	  if( !ok ) break;	// if unsat has been found, stop searching for more cardinality constraints!
	  
	  if( cc.size() > c.size() || degree < origDegree ) { // if this constraint is not simply a clause, but something has been added or changed
	    // sort(cc);	// TODO: not necessary here, but if implemented in Coprocessor!
	    cards.push_back( CardC(cc, degree) ); // add the constraint to the data base
	    if( opt_pb_semDebug ) cerr << "c found card constraint " << cc << "  <= " << degree << endl;
	    intersection.nextStep();
	    extendedCards ++; extendLits += (cc.size() - c.size());	// stats
	    lits.clear();	// collect all literals that have to occur in clauses to be disabled
	    for( int j = 0 ; j < cc.size(); ++ j ) {
	      intersection.setCurrentStep( toInt( ~cc[j] ) ); // mark all complements of the constraint
	      lits.push( cc[j] );
	    }
// since cc is a superset of origCC, no need to collect those literals as well
// 	    for( int j = 0 ; j < origCC.size(); ++ j ) {
// 	      if( !intersection.isCurrentStep( toInt(~origCC[j] ))) {
// 		intersection.setCurrentStep( toInt( ~origCC[j] ) ); // mark all complements of the constraint#
// 		lits.push( origCC[j] );
// 	      }
// 	    }
	    if( opt_pb_semDebug ) cerr << "c marked literals: " << lits << endl;

	    // disable all clauses that would lead to the same constraint!
	    for( int j = 0 ; j < lits.size(); ++ j ) {	// for all the literals in at least the original constraint, but also in its extension
	      for( int k = 0 ; k < occ[toInt(~lits[j])].size(); ++ k ) {	// and all the clauses that have this literal as smallest literal (watch 1 scheme, each clause only once)
		Clause& candidate = ca[ occ[toInt(~lits[j])][k] ];	// current delete candidate
		if( candidate.mark() != 0 ) continue; // candidate contains more literals than have been marked
		if( candidate.size() <= degree ) continue; // a clause that is smaller than the degree of the cardinality constraint cannot be subsumed by the constraint
		if( opt_pb_noReduct && candidate.size() > lits.size() ) continue; // there cannot be falsified literals inside the clauses
		bool failed = false;
		for( int m = 0 ; m < candidate.size(); ++ m ) {	// check whether the current clause has all the necessary literals
		  if( !opt_pb_noReduct && value( candidate[m] ) == l_False ) continue;	// do not care about disabled literals (if there are no units around)
		  if( !intersection.isCurrentStep( toInt( candidate[m] ) ) ) { failed = true; break; }	// another literal was found, keep this clause!
		}
		if( ! failed  ) {
		  if( opt_pb_semDebug ) cerr << "c disable with literal " << lits[j] << " clause[" << occ[toInt(~lits[j])][k] << "] " << candidate  << " by constraint " << origCC << " <= " << degree << endl;
		  candidate.mark(1);	// set this clause to "can be deleted"
		  nrDisabledClauses ++;
		  disabledClauses.push( occ[toInt(~lits[j])][k] );
		  if( opt_pb_semDebug ) cerr << "c current trail: " << trail << endl;
		}
	      }
	    }
	  } else failedExtendTries ++;
	  
	} // end iterating over the clauses
	
	
	
	
	delete [] tmpA;
	
	// to enable disabled clauses again
	// for( int i = 0 ; i < disabledClauses.size(); ++ i ) { // enabled disabled clauses again!
	//  ca[ disabledClauses[i] ].mark(0);
	// }
	
	semTime = cpuTime() - semTime; // time measurement
	cerr << "c FindCardSem: time: " << semTime << " s," << "steps: " << semSteps << endl;
	cerr << "c FindCardSem: cards: " <<  extendedCards 
			 << " failed: " << failedExtendTries
			 << " extLits: " << extendLits 
			 << " redDegree: " << reducedDegrees
			 << " probes: " << totalProbes 
			 << " conflictProbes: " << totalFailedProbes 
			 << " savedCls: " << nrDisabledClauses 
			 << " units: " << units
			 << endl;
}

/**
 * 
 *  below, code for syntactic analysis
 * 
 */

static bool amoExistsAlready(const vector< Lit >& lits, vector< std::vector< int > >& leftHands, vector< CardC >& cards, int64_t& searchSteps)
{
  // check whether the sorted set of literals is already present as AMO (or larger AMO!)
  // implement with while loop, running over two constraints at the same time, for all constraints with the least frequent literal
  
  if ( lits.size() == 0 ) return true; // amo() is always true!

  Lit min = lits[0];
  for( int i = 1; i < lits.size(); ++ i )
    if( leftHands[ toInt( lits[i] ) ] < leftHands[ toInt( min ) ] ) min = lits[i];
  
  // check whether an AMO, or a bigger AMO can be found in the list of min
  for( int i = 0 ; i < leftHands[ toInt(min) ].size(); ++ i ) {
    const CardC& ref = cards[ leftHands[ toInt(min) ] [i] ];
    if( !ref.amo() ) continue; // look only for amos
    searchSteps ++;
    int j = 0, k = 0; // loop over both amos!
    const vector<Lit>& rl = ref.ll;
    while( j < lits.size() && k < rl.size() )
    {
      if( lits[j] < rl[k] ) break; // the new AMO is new
      else if ( rl[k] < lits[j] ) k ++; // simply jump over lits that are in ref, but not in lits
      else { ++j; ++k; }
    }
    if( j == lits.size() ) return true; // found a AMO that is at least as strong as the current one (might contain more lits!)
  }
  
  return false;
}


// general find method
bool Solver::findCards( )
{
  double findTime = 0;
  int64_t searchSteps = 0;
  
  
  MethodTimer mt(&findTime); // measure time it took
  bool didSomething = false;

  // have a slot per literal
  MarkArray markArray;
  markArray.create( nVars() * 2 );
  
  MarkArray inAmo;
  inAmo.create( 2 * nVars() );

  // create full BIG, also rewrite learned clauses!!
  BIG big; 
  big.create( ca,nVars(),clauses,learnts ); // crate binary implication graph out of the current formula

  vector< CardC > cards; // storage for constraints, and their occurrences
  vector<Lit> lits; // storage for tmp literals
  
  double amoTime = 0, mergeTime = 0, subTime = 0, twoProdTime = 0, semTime = 0, amtTime = 0; // time stats
  int amos = 0, merged = 0, duplicates = 0, twoProducts = 0, semantic = 0, foundAmts = 0; // counter stats
  int units = 0;
  
  // approximate AMOs
  amoTime = cpuTime() - amoTime;
  if( opt_pb_atMostOne ) { // approximate AMO method?
    markArray.nextStep();
    inAmo.nextStep();
    // store frequencies of literals, store it
    vec<int> frequencies( 2*nVars() ); // store frequency per literal
    for( int cs = 0; cs < 2 ; ++ cs ) {
      vec<CRef>& list = cs == 0 ? clauses : learnts;
      for( int i = 0 ; i < list.size(); ++ i ) {
	const Clause& c = ca [ list[i] ];
	for( int j = 0 ; j < c.size(); ++ j ) {
	  frequencies[ toInt( c[j] ) ] ++;
	}
      }
    }
    // setup own structures
    Heap<LitOrderHeapLt> heap(frequencies); // heap that stores the literals according to their frequency
    heap.addNewElement( nVars() * 2 );
    heap.clear();
    for( Var v = 0 ; v < nVars(); ++ v ) {
      if( !heap.inHeap(toInt(mkLit(v,false))) )  heap.insert( toInt(mkLit(v,false)) );
      if( !heap.inHeap(toInt(mkLit(v,true))) )   heap.insert( toInt(mkLit(v,true))  );
    }
    
    if( fm_debug_out > 0) cerr << "c run with " << heap.size() << " elements" << endl;
    
    // for l in F, and only if not interrupted, and not limits are reached or active
    while (heap.size() > 0 && (opt_pb_unlimited || (opt_pb_fmSearchLimit > searchSteps ) ) && !asynch_interrupt )  // repeat until limit is reached, or interrupt
    {
      const Lit right = toLit(heap[0]);
      assert( heap.inHeap( toInt(right) ) && "item from the heap has to be on the heap");

      heap.removeMin();
      
      if( frequencies[ toInt(right) ] < 2 ) continue; // no enough occurrences -> skip!
      const uint32_t size = big.getSize( ~right );
      if( fm_debug_out > 2) cerr << "c check " << right << " with " << frequencies[toInt(right)] << " cls, and " << size << " implieds" << endl;
      if( size < 2 ) continue; // cannot result in a AMO of required size -> skip!
      const Lit* list = big.getArray( ~right );

      // create first list right -> X == -right \lor X, ==
      inAmo.nextStep(); // new AMO
      lits.clear(); // new AMO
      lits.push_back(right); // contains list of negated AMO!
      for( int i = 0 ; i < size; ++ i ) {
	searchSteps ++;
	const Lit& l = list[i];
	if( frequencies[ toInt(l) ] < 2 ) continue; // cannot become part of AMO!
	if( big.getSize( ~l ) < 2 ) continue; // cannot become part of AMO!
	if( inAmo.isCurrentStep( toInt(l) ) ) continue; // avoid duplicates!
	inAmo.setCurrentStep( toInt(l ) );
	lits.push_back(l); // l is implied by ~right -> canidate for AMO(right,l, ... )
	if( lits.size() > opt_pb_fmMaxAMO ) break; // do not collect more literals for the AMO (heuristic cut off...)
      }
      if( fm_debug_out > 2) cerr << "c implieds: " << lits.size() << ", namely " << lits << endl;
      if( lits.size() < 3 || opt_pb_fmSearchLimit <= searchSteps ) continue; // do not consider this variable, because it does not hit enough literals
      
      // TODO: should sort list according to frequency in binary clauses - ascending, so that small literals are removed first, increasing the chance for this more frequent ones to stay!
      
      // check whether each literal can be inside the AMO!
      for( int i = 0 ; i < lits.size(); ++ i ) { // keep the very first, since it created the list!
	const Lit l = lits[i];
	if( l == lit_Undef ) continue; // do not handle removed literals!

	if( opt_pb_fmSearchLimit <= searchSteps ) { // if limit is reached, invalidate current AMO candidate
	  lits.clear();
	  break;
	}

	const uint32_t size2 = big.getSize( ~l );
	const Lit* list2 = big.getArray( ~l );
	// if not all, disable this literal, remove it from lits
	inAmo.nextStep(); // new AMO
	
	if( opt_pb_rem_first ) { // if this option is chosen, all literals, which are not negated by the current literal, are removed
	  for( int j = 0 ; j < size2; ++ j ) {inAmo.setCurrentStep( toInt(list2[j]) );searchSteps++;}
	  int j = 0;
	  for( ; j<lits.size(); ++ j ) {
	    if( i!=j 
	      && lits[j] != lit_Undef 
	      && !inAmo.isCurrentStep( toInt( lits[j] ) ) 
	    ) break;
	    searchSteps++;
	  }
	  if( j != lits.size() ) {
	    if( fm_debug_out > 0) cerr << "c reject [" <<i<< "]" << lits[i] << ", because failed with [" << j << "]" << lits[j] << endl;
	    lits[i] = lit_Undef; // if not all literals are covered, disable this literal!
	  } else if( fm_debug_out > 0) cerr << "c keep [" <<i<< "]" << lits[i] << " which hits [" << j << "] literas"  << endl;
	} else { // if this option is chosen (recommended), a literal is removed, if it does not imply the complement of all others
	  for( int j = 0 ; j < size2; ++ j ) {
	    if( fm_debug_out > 2 ) cerr << "c literal " << l << " hits literal " << list2[j] << endl;
	    inAmo.setCurrentStep( toInt(list2[j]) );
	    searchSteps++;
	  }
	  inAmo.setCurrentStep( toInt(l) ); // set literal itself!
	  int j = i+1; // previous literals have been tested already!
	  for( ; j < lits.size(); ++ j ) {
	    if( lits[j] == lit_Undef ) continue; // do not process this literal!
	    searchSteps++;
	    if( fm_debug_out > 2 ) cerr << "c check literal " << lits[j] << "[" << j << "]" << endl;
	    if( !inAmo.isCurrentStep( toInt( lits[j] ) ) // not in AMO with current literal
	    ) {
	      if( fm_debug_out > 0) cerr << "c reject [" <<j<< "]" << lits[j] << ", because failed with [" << i << "]" << lits[i] << endl;
	      lits[j] = lit_Undef; // if not all literals are covered, disable this literal!
	    } else {
	      if( fm_debug_out > 0) cerr << "c keep [" <<j<< "]" << lits[j] << " which is hit by literal " << lits[i] << "[" << i << "] "  << endl;    
	    }
	  }
	}
      }
      
      // found an AMO!
      for( int i = 0 ; i < lits.size(); ++ i )
	if ( lits[i] == lit_Undef ) { lits[i] = lits[ lits.size() - 1 ]; lits.pop_back(); --i; }
      
      for( int i = 0 ; i < lits.size(); ++ i ){
	if( opt_pb_no_AMO_duplicates ) { // remove the edges in the big that represent this AMO
	  for( int j = i+1; j < lits.size(); ++ j ) {
	    searchSteps+=big.getSize(lits[i]); // approximate the number of memory hits here
	    big.removeEdge(lits[i], lits[j] );
	  }
	}
	lits[i] = ~ lits[i]; // need to negate all!
	markArray.setCurrentStep( var(lits[i]) ); // memorize that this variable is part of an AMO
      }

      // remember that these literals have been used in an amo already!
      sort(lits);
      cards.push_back( lits );

      if( opt_pb_multiVarAMO && lits.size() > 1 && opt_pb_no_AMO_duplicates && big.getSize( right ) > 0 ) heap.insert( toInt( right ) ); // this literal might have more cliques
      
      if( fm_debug_out > 0 ) cerr << "c found AMO: " << lits << endl;
    }
    
    if( opt_pb_no_AMO_duplicates && cards.size() > 0 )
      big.recreate( ca,nVars(),clauses,learnts );
    
  }
  amos = cards.size();	// store number of found constraints
  amoTime = cpuTime() - amoTime;
  
  vector< vector<int> > leftHands( nVars() * 2 ); // store occurrences of literals in found cards
  if( opt_pb_merge || opt_pb_atMostTwo || opt_pb_twoProduct ) {
    for( int i = 0 ; i < cards.size(); ++ i )
      for( int j = 0; j < cards[i].ll.size(); ++ j ) leftHands[ toInt( cards[i].ll[j] ) ].push_back( i );
  }
  mergeTime = cpuTime() - mergeTime;
  if( opt_pb_merge ) { // merge two AMO constraints, if they are x_1 + ... + x_n <= 1 and -x_n + ... x_z <= 1 -> resolve on x_n!

    for( Var v = 0 ; v < nVars(); ++v  ) {
      const Lit pl = mkLit(v,false), nl = mkLit(v,true);
      if( leftHands[ toInt(pl) ] .size() > 2 || leftHands[ toInt(nl) ] .size() > 2 ) continue; // only if the variable has very few occurrences
      for( int i = 0 ; i < leftHands[toInt(pl)].size() &&  searchSteps < opt_pb_fmSearchLimit; ++ i ) { // since all cards are compared, be careful!
	searchSteps ++;
	if( cards[leftHands[toInt(pl)][i]].invalid() ) continue;
	if( !cards[leftHands[toInt(pl)][i]].amo() ) continue; // can do this on AMO only
	for( int j = 0 ; j < leftHands[toInt(nl)].size(); ++ j ) {
	  const CardC& card1 = cards[leftHands[toInt(pl)][i]]; // get both references here, because otherwise they will become invalid!
	  const CardC& card2 = cards[leftHands[toInt(nl)][j]];
	  searchSteps ++;
	  if( card2.invalid() ) continue;
	  if( !card2.amo() ) continue; // can do this on AMO only
	  
	  // merge the two cardinality constraints card1 and card2
	  // check for duplicate literals (count them, treat them special!)
	  // otherwise combine the two left hands!
	  // add the new cards to the structure!
	  const vector<Lit>& v1 = card1.ll,& v2 = card2.ll; // get references
	  int n1=0,n2=0;
	  lits.clear();
	  while( n1 < v1.size() && n2 < v2.size() ) {
	    if( v1[n1] == v2[n2] ) { // same literal in two amos with a different literal -> have to be unit!
	      if( ! inAmo.isCurrentStep( toInt(~v1[n1]) ) ) { // store each literal only once in the queue
		  inAmo.setCurrentStep( toInt(~v1[n1]) );
		  didSomething = true;
		  if ( value( ~v1[n1] ) == l_False ) {
		    cerr << "c found formula to be UNSAT!" << endl;
		    ok = false;
		  } else if( value( ~v1[n1] ) != l_True ) {
		    units ++;
		    uncheckedEnqueue( ~v1[n1] );
		  } 
	      }
	      n1++;n2++;
	    } else if( v1[n1] < v2[n2] ) {
	      if( v1[n1] != pl ) lits.push_back(v1[n1]);
	      n1 ++;
	    } else { 
	      if( v2[n2] != nl ) lits.push_back(v2[n2]);
	      n2 ++;
	    }
	  }
	  for(; n1 < v1.size(); ++ n1 ) if( v1[n1] != pl ) lits.push_back( v1[n1] );
	  for(; n2 < v2.size(); ++ n2 ) if( v2[n2] != nl ) lits.push_back( v2[n2] );
	  if( lits.size() == 0 ) continue; // no AMO, if there are no literals inside!
	  if( fm_debug_out > 0 ) cerr << "c deduced AMO " << lits << " from AMO " << card1.ll << " and AMO " << card2.ll << endl;
	  
	  // check whether there are similar variables inside the constraint, if so - drop it!
	  bool hasComplements = false;
	  for( int k = 0 ; k + 1 < lits.size(); ++k ) {
	    if( lits[k] == ~ lits[k+1] ) { 
	      if( fm_debug_out > 2 ) cerr << "c deduced AMO contains complementary literals - set all others to false!" << endl;
	      Var uv = var(lits[k]);
	      for( int k = 0 ; k < lits.size(); ++ k ) { // if there is a complement in n AMO, all the other lits have to be false
		if( var(lits[k]) == uv ) continue; // do not enqueue complementary literal!
		if( ! inAmo.isCurrentStep( toInt(~lits[k]) ) ) { // store each literal only once in the queue
		  if ( value( ~lits[k] ) == l_False ) {
		    cerr << "c found formula to be UNSAT!" << endl;
		    ok = false;
		  } else if( value( ~lits[k] ) != l_True ) {
		    units ++;
		    uncheckedEnqueue( ~lits[k] );
		  }
		}
	      }
	      hasComplements = true; break;
	    }
	  }
	  if(hasComplements) continue;
	  
	  const int index = cards.size();
	  cards.push_back( CardC(lits) ); // create AMO
	  merged ++;
	  for( int k = 0 ; k < lits.size(); ++ k ) leftHands[ toInt( lits[k] ) ].push_back(index); // for the new AMO, store its occurrences
	}
      }
    }
  }
  mergeTime = cpuTime() - mergeTime;
  
  twoProdTime = cpuTime() - twoProdTime;
  if( opt_pb_twoProduct ) { // find the two product encoding
    MarkArray newAmoLits;
    newAmoLits.create(2*nVars());
    
    for( int i = 0 ; i < cards.size(); ++ i ) 
    {
      if( opt_pb_fmSearchLimit <= searchSteps ) { // if limit is reached, invalidate current AMO candidate
	break;
      }
      CardC& A = cards[i]; 	// cardinality constraints are sorted
      if( !cards[i].amo() || cards[i].invalid() ) continue;	// not an AMO, test next AMO, use only AMOs with size > 2 (heuristic!)
      const Lit a = cards[i].ll[0];	// since sorted, the first literal in ll is the smallest literal
      
      if( fm_debug_out > 2 ) cerr << "c work on AMO " << cards[i].ll << " with smallest lit " << a << endl;
      
      Lit* aList = big.getArray( ~a);
      if( big.getSize( ~a) == 0 ) continue; // not this AMO, because the smallest literal does not imply other literals
      Lit l = ~ aList[0];
      for( int j = 1 ; j < big.getSize( ~a); ++ j ){ // get the smallest literal, but negated!
	if( ~aList[j] < l ) l = ~aList[j];
	searchSteps++;
      }
	
      if( fm_debug_out > 2 ) cerr << "c min lit = " << l << " that implies " << big.getSize(l) << endl;
      for( int j = 0 ; j < big.getSize( l ); ++ j ) // for b in BIG(l), b!=a
      {
	if( opt_pb_fmSearchLimit <= searchSteps ) break; // if limit is reached, invalidate current AMO candidate
	const Lit b = big.getArray(l)[j];	// literal hit by the literal l.
	if( b == a ) continue;
	if( fm_debug_out > 2 ) cerr << "c current implied: " << b << endl;
	
	for( int k = 0 ; k < leftHands[ toInt(b) ].size(); ++k ) // for B in AMOs_b, A != B
	{
	  if( leftHands[ toInt(b) ][k] <= i ) {
	    if( fm_debug_out > 3 ) cerr << "c reject AMO " << cards[ leftHands[ toInt(b) ][k] ].ll << " because of position " << endl;
	    continue;		// A != B, and check each pair only once!
	  }
	  searchSteps++;
	  CardC& B = cards[ leftHands[ toInt(b) ][k] ];		// turn index into CardC
	  if( ! B.amo() ) continue; // work only on pairs of amo!
	  // if( b != B.ll[0] ) continue; // use this AMO B only, if b is its smallest literal (avoid duplicates)
	  // TODO: check sizes of A and B, use them only, if they differ with max 1
	  lits.clear();	// global AMO P, sufficient since there won't be local ones!
	  newAmoLits.nextStep();	// new set of literals
	  if( fm_debug_out > 3 ) cerr << "c check AMOs " << cards[i].ll << " and " << B.ll << endl;
	  for( int m = 0 ; m < B.ll.size(); ++m ) // for literal k in B
	  {
	    if( opt_pb_fmSearchLimit <= searchSteps ) { lits.clear(); break; } // reached limit?
	    const Lit bLit = B.ll[m]; // each literal in B should imply a set of literals, where each of these literals hits a different lit in A
	    searchSteps++;
	    if( fm_debug_out > 3 ) cerr << "c current lit in B: " << bLit << endl;
	    
	    markArray.nextStep();	// prepare for count different hits
	    for( int n = 0 ; n < cards[i].ll.size(); ++ n )  // mark all literals from AMO A for becoming hit in this iteration
	      markArray.setCurrentStep( toInt( cards[i].ll[n] ) );
	    
	    for( int n = 0 ; n < big.getSize( ~bLit ); ++ n ) // check whether this literal implies a set of literal, which hit all different literals from A
	    {
	      searchSteps++;
	      const Lit hitLit = ~ big.getArray( ~bLit )[n];
	      if( newAmoLits.isCurrentStep( toInt(hitLit) ) ) continue; // do not collect such a literal twice!
	      
	      if( fm_debug_out > 3 ) cerr << "c test hitLit " << hitLit << " which implies " << big.getSize( hitLit ) << " lits"  << endl;

	      for( int o = 0 ; o < big.getSize( hitLit ); ++o ) { // check whether this literal hits a literal from A
		searchSteps++;
		const Lit targetLit = big.getArray( hitLit )[o];
		if( markArray.isCurrentStep( toInt( targetLit ) ) ) {
		  if( fm_debug_out > 3 ) cerr << "c target lit " << targetLit << endl;
		  markArray.reset( toInt( targetLit ) );	// count hit, reset current variable
		  lits.push_back( hitLit );
		  newAmoLits.setCurrentStep( toInt(hitLit) );	// do not add this lit twice to the current set
		  break;					// take the first best literal that is hit! NOTE approximation!
		} else {
		  if( fm_debug_out > 3 ) cerr << "c re-hit target lit " << targetLit << endl;
		}
	      }
	    }  // end collecting literals that hit lits in A
	    
	  } // end for lits in B
	  // add the global set of lits as new AMO
	  if( lits.size() > 0 ) { // if there is a global AMO
	    sort( lits );
	    searchSteps += lits.size(); // approximate sorting
	    // TODO check for complementary literals! or being unit
	    if( !amoExistsAlready(lits, leftHands, cards, searchSteps ) ) {
	      if( fm_debug_out > 0 ) cerr << "c found new AMO " << lits << endl;
	      if( fm_debug_out > 2 ) cerr << "c   based on " << cards[i].ll << " and AMO " << B.ll << endl; // here, the reference is still working
	      for( int n = 0 ; n < lits.size(); ++ n )
		leftHands[ toInt( lits[n] ) ].push_back( cards.size() );	// register new AMO in data structures
	      cards.push_back( CardC( lits ) ); // actually add new AMO
	      twoProducts ++;
	    }
	  }
	} // select next B

      } // end looping over implied lits from A's smallest literal
      
    } // end looping over cardinality constraints
  
  }
  twoProdTime = cpuTime() - twoProdTime;
    
  subTime = cpuTime() - subTime;
  if( opt_pb_remDuplicates ) { // remove redundant duplicate AMOs, and subsumed ones
    for( int i = 0 ; i < cards.size(); ++ i )
    {
      CardC& c = cards[ i ];
      if( c.taut() ) c.invalidate(); // do not use this constraint any more!
      if( !c.amo() ) continue; // do only for AMOs
      if( c.ll.size() == 0 ) continue; // safe side

      Lit min = c.ll[0];
      for( int j = 1; j < c.ll.size(); ++ j )
	if( leftHands[ toInt( c.ll[j] ) ] < leftHands[ toInt( min ) ] ) min = c.ll[j];
      
      // check whether an AMO, or a bigger AMO can be found in the list of min
      for( int m = 0 ; m < leftHands[ toInt(min) ].size(); ++ m ) {
	const CardC& ref = cards[ leftHands[ toInt(min) ] [m] ];
	if( !ref.amo()  || ref.taut() || leftHands[ toInt(min) ] [m] == i ) continue; // look only for amos, and do not compare itself with the current AMO
	int j = 0, k = 0; // loop over both amos!
	const vector<Lit>& rl = ref.ll;
	while( j < c.ll.size() && k < rl.size() )
	{
	  if( c.ll[j] < rl[k] ) break; // the new AMO is new
	  else if ( rl[k] < c.ll[j] ) k ++; // simply jump over lits that are in ref, but not in lits
	  else { ++j; ++k; }
	}
	if( j == c.ll.size() ) {
	  c.invalidate(); // invalidate each AMO that has been found to be redundant
	  duplicates ++;
	}
      }
    }
  }
  subTime = cpuTime() - subTime;
  
  // perform AMT extraction
  amtTime = cpuTime() - amtTime;
  if( opt_pb_atMostTwo ) {
    cerr << "c check AMT" << endl;
    int ternaries = 0;
    // structure to watch ternary clauses efficiently
    inAmo.nextStep(); // use it to detect whether already used in AM2 constraint as well!
    vector< vector< Ternary > > tocc ( 2*nVars() );	// occurrence of ternary clauses, and get space
    for( int i = 0 ; i < clauses.size(); ++ i ) {
      const Clause& c = ca[clauses[i]];
      if( c.mark() != 0 || c.size() != 3 || c.isPBconstraint() ) continue; // not an interesting ternary clause
      ++ ternaries;
      for( int j = 0 ; j < 3; ++j ) 
	tocc[ toInt( c[j] )].push_back( Ternary( c[0], c[1], c[2] ) ); // add for each literal a ternary construct
    }
    cerr << "c found ternary clauses: " << ternaries << endl;
    
    for( Var v = 0 ; v < nVars(); ++ v ) {
      if( opt_pb_fmSearchLimit <= searchSteps ) { // if limit is reached, invalidate current AMO candidate
	lits.clear();
	break;
      }
      for( int p = 0 ; p < 2; ++ p ) { // for both polarities
	if( opt_pb_fmSearchLimit <= searchSteps ) { // if limit is reached, invalidate current AMO candidate
	  lits.clear();
	  break;
	}
        const Lit l = mkLit(v,p==1);
	if( !opt_pb_multiVarAMT && inAmo.isCurrentStep( toInt(l) ) ) continue; // each literal has the chance to be in one constraint!
	if( fm_debug_out > 1 ) cerr << "c consider literal " << l << " with " << tocc[ toInt(l) ].size() << " clauses" << endl;
        lits.clear(); markArray.nextStep(); // prepare set!
	lits.push_back(l); markArray.setCurrentStep( toInt(l) ); // add current literal!
	
	for( int i = 0 ; i < tocc[ toInt( l ) ].size(); ++ i ) { // collect all literals that occur with l in a ternary clause!
	  const Ternary& c = tocc[ toInt( l ) ][i];
	  searchSteps++;
	  if( c[0] != l ) continue; // consider only clauses, where l is the smallest literal?! (all other AMT's would have been found before!)
	  if( !opt_pb_multiVarAMT && (inAmo.isCurrentStep( toInt(c[1]) ) || inAmo.isCurrentStep( toInt(c[2]) ) ) ) continue; // do not use this ternary clause any more!
	  for( int j = 1; j < 3; ++ j ) {
	    searchSteps++;
	    if( c[j] != l && ! markArray.isCurrentStep( toInt(c[j] ) ) ) { 
	      lits.push_back(c[j]); markArray.setCurrentStep(toInt(c[j]));
	    }
	  }
	}
	sort(lits); // sort lits in list!
	assert( lits[0] == l && "current literal has to be the smallest literal!" );

	for( int i = 0 ; i < lits.size(); ++ i ) { // check whether each literal can be found with each pair of other literals!
	  // setup the map
	  const Lit l0 = lits[i];
	  for( int j = i+1 ; j < lits.size(); ++ j ) {
	    const Lit l1 = lits[j];
	    for( int k = j+1 ; k < lits.size(); ++ k ) { 
	      searchSteps++;
	      const Lit l2 = lits[k];
	      if( fm_debug_out > 2 ) cerr << "c check triple " << l0 << " - " << l1 << " - " << l2 << endl;
	      int m = 0;
	      for(  ; m < tocc[ toInt(l0) ].size(); ++ m ) { // collect all literals that occur with l in a ternary clause!
		const Ternary& c = tocc[ toInt(l0) ][m];
		if( c[1] == l1 && c[2] == l2 ) break; // found corresponding clause! - l0 < l1 -> needs to be c[0]
	      }
	      if( m == tocc[ toInt(l0) ].size() ) { // did not find triple l0,l1,l2
		for( j = i; j + 1 < lits.size(); ++ j ) lits[j] = lits[j+1]; // move all remaining literals one position to front // TODO: can be implemented faster!
		lits.pop_back(); // remove last literal => deleted current literal, list still sorted!
		--i; // reduce pointer in list
		goto checkNextLiteral;
	      } 
	    } 
	  } 
	  checkNextLiteral:; // jump here, if checking the current literal failed
	}
	
	if( lits.size() > 3 ) {
	  for( int i = 0 ; i < lits.size(); ++ i ) { 
	    if( !opt_pb_multiVarAMT ) inAmo.setCurrentStep( toInt( lits[i] ) ); // disallow the current literal to participate in another constraint as well!
	    lits[i] = ~lits[i];
	  }
	  foundAmts ++;
	  if( fm_debug_out > 1 ) cerr << "c found AM2["<<foundAmts<<"]: " << lits << endl;
	  cards.push_back( CardC( lits ) ); // use default AMO constructor
	  cards.back().k = 2; // set k to be 2, since its an at-most-two constraint!
	}
	
      }
    }
  }
  amtTime = cpuTime() - amtTime;

  semTime = cpuTime() - semTime;
  if( opt_pb_semCard ) {
    findCardsSemantic( &cards );
  }
  semTime = cpuTime() - semTime;
  
  // print statistics
  cerr << "c CardStats: time: amo: " << amoTime << " s, merge: " << mergeTime << " s, twoPr: " << twoProdTime << " s, sub: " << subTime << " s, " << " amt: " << amtTime << " s" << endl;
  cerr << "c CardStats: counts: amo: " << amos << " merged: " << merged << " units: " << units << " twoPr: " << twoProducts << " subsumed: " << duplicates << " AMTs: " << foundAmts << endl;
  cerr << "c CardSteps: steps: " << searchSteps << endl;
  cerr << "c SolverStatus: " << (ok ? "good" : "bad ") << endl;

  // units should be printed before other constraints to maybe satisfy or simplify them already
  if( opt_pb_printUnits ) {
    assert( decisionLevel() == 0 && "this output is only valid on level 0!" );
    for( int i = 0 ; i < trail.size(); ++ i ) {
      cerr << ~ trail[i] << " <= 0 " << endl;
    }
  }
  if( opt_pb_printCards ) {
    for( int i = 0 ; i < cards.size(); ++ i ) {
      if( cards[i].invalid() || cards[i].taut() ) continue; // print only the constraints that give information
      for( int j = 0 ; j < cards[i].ll.size(); ++ j ) cerr << cards[i].ll[j] << " ";
      cerr << " <= " << cards[i].k << " "; 
      for( int j = 0 ; j < cards[i].lr.size(); ++ j ) cerr << cards[i].lr [j] << " ";
      cerr << endl;
    }
  }
  
  if( opt_pb_exitAfterExtraction ) {
    cerr << "c exit after extraction" << endl;  
    exit(0);
  }
  
  // re-setup the solver with all the clauses that are left over, when there has been constraints detected
  
  if( cards.size() > 0 ) {
    // remove all clauses from the solver
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
      for (int s = 0; s < 2; s++)
	watches[ mkLit(v, s) ].clear();
    learnts_literals = 0; clauses_literals = 0;

    
    // for each constraints eliminate all clauses from the formula
    int foundConstraints = 0;
    vec<CRef> disabledClauses; 
    
    // create occ lists, for each clause watch the smallest literal
    for( int i = 0 ; i < clauses.size(); ++ i ) {
      Clause& c = ca[ clauses[i] ];	// not ensured to be sorted, hence check smallest literal
      if( c.mark() || c.size() == 0  || c.isPBconstraint()) continue;
      Lit minLit = c[0];
      for( int j = 1; j < c.size(); ++ j ) if( c[0] < minLit ) minLit = c[0]; // if its the minimum, later disabling clauses is cheaper
      watches [ minLit ]. push( Watcher(clauses[i], c[0])  ); // just watch the smallest literal
    }
    
    for ( int i = 0 ; i < cards.size(); ++ i ) 
    {
      const CardC& constraint = cards[i];
      if( constraint.invalid() || constraint.taut() ) continue; // do not process irrelevant constraints
      assert( constraint.lr.size() == 0 && "detection procedures can find only simple cardinality constraints" );
      if( constraint.lr.size() > 0 ) continue; // in case the assertion is not compile in
      const vector<Lit>& lits = constraint.ll; 
      markArray.nextStep();
      for( int j = 0 ;  j < lits.size(); ++ j ) markArray.setCurrentStep( toInt( ~lits[j] ) ); // mark all complement literals of this cardinality constraint
      
      foundConstraints ++;

      // disable all clauses that would lead to the same constraint! (hence, check the threshold)
      for( int j = 0 ; j < lits.size(); ++ j ) {	// for all the literals in at least the original constraint, but also in its extension
	for( int k = 0 ; k < watches[ ~lits[j] ].size(); ++ k ) {	// and all the clauses that have this literal as smallest literal (watch 1 scheme, each clause only once)
	  Clause& candidate = ca[ watches[ ~lits[j] ][k].cref ];	// current delete candidate
	  if( candidate.mark() != 0 ) continue; // candidate contains more literals than have been marked
	  if( candidate.size() <= constraint.k ) continue; // a clause that is smaller than the degree of the cardinality constraint cannot be subsumed by the constraint
	  if( opt_pb_noReduct && candidate.size() > lits.size() ) continue; // there cannot be falsified literals inside the clauses, and the clause is larger
	  if( constraint.k >= candidate.size() ) continue; // the constraint is not specific enough on the literals of the current clause (for a clause the at-most constraint treshold is n-1)
	  bool failed = false;
	  for( int m = 0 ; m < candidate.size(); ++ m ) {	// check whether the current clause has all the necessary literals
	    if( !opt_pb_noReduct && value( candidate[m] ) == l_False ) continue;	// do not care about disabled literals (if there are no units around)
	    if( !markArray.isCurrentStep( toInt( candidate[m] ) ) ) { failed = true; break; }	// another literal was found, keep this clause!
	  }
	  if( ! failed ) {
	    if( opt_pb_semDebug ) cerr << "c disable with literal " << lits[j] << " clause[" << watches[ ~lits[j] ][k].cref << "] " << candidate << " by constraint " << constraint.ll << " <= " << constraint.k << endl;
	    candidate.mark(1);	// set this clause to "can be deleted"
	    disabledClauses.push( watches[ ~lits[j] ][k].cref );
	  }
	}
      }
    }
    
    // remove the 1-watches again
    for (int v = 0; v < nVars(); v++)
      for (int s = 0; s < 2; s++)
	watches[ mkLit(v, s) ].clear();
    
    // remove the clauses from memory
    for( int i = 0 ; i < disabledClauses.size(); ++i ) 
      ca.free(disabledClauses[i]);
      
    // add all clauses back to the solver (since nothing has been done on the structure, all clauses should be attached as usual
    for( int i = 0 ; i < clauses.size(); ++ i ) {
      const Clause&c = ca[clauses[i]];
      if( !c.mark() ) attachClause( clauses[i] );
    }
    
    // turn the extracted cardinality constraints into clauses
    vec<int64_t> weights;
    CRef prevPB = CRef_Undef;
    for( int i = 0 ; i < cards.size(); ++ i ) {
      CardC& c = cards[i];
      if( c.taut() || c.invalid() ) continue; // no need to add this constraint
      if( c.k > 0 ) { // if <= 0, then enqueue units!
	weights.clear();
	for( int j = 0 ; j < c.ll.size(); ++ j ) weights.push(1); // we found cardinality constraints only
	CRef pbref = ca.alloc( c.ll, weights, c.k, false ); // add the constraint as non-learnt clause
	attachPB( pbref );	// add the current constraint to its watch lists
	clauses.push( pbref );	// add the constraint to the clauses
	
	if( fm_debug_out ) {
	  cerr << "c added constraint[" << pbref << "] with" << endl
	  << "c    lits:         " << c.ll << endl
	  << "c   weights:       " << weights << endl;
	  cerr << "c resulted in: " << ca[pbref] << endl;
	  if( prevPB != CRef_Undef ) cerr << "c previous constraint" << ca[prevPB] << endl;
	}
	prevPB = pbref;
      } else { // handle the case <= 0 -> enforce all literals to be mapped to false
	if( c.k < 0 ) {
	  if( opt_pb_semDebug ) cerr << "c inconsistent constraint detected" << endl;
	  return false; // we found a constraint that cannot be fulfilled
	}
	for( int j = 0 ; j < c.ll.size(); ++j ) {
	  if( value( c.ll[j] ) == l_True ) {
	    if( opt_pb_semDebug ) cerr << "c unsatisfiable formula by propagating units of revealed constraints" << endl;
	    ok = false;
	    return false;                      // the literal is already enqueued as being true -> unsatisfiable
	  }
	  else { 
	    if( value(c.ll[j]) == l_Undef ) uncheckedEnqueue( ~ c.ll[j] ); // enqueue the literal to be false
	  }
	}
      }
    }
    
    if( opt_pb_semDebug ) cerr << "c current trail: " << trail << endl;
    
    cerr << "c size of ca: " << ca.size() << endl;
    cerr << "c revealed constraints: " << foundConstraints << endl;
    
    // rerun propagatoin to make sure the PB constraints watch the right literals
    assert(decisionLevel() == 0 && "resetting qHead should only be done on the root level" );
    qhead = 0;                   // reset the literals that have already been propagated (so that PB constraints are watched with the right literals)
    CRef confl = propagate();    // propagate on the formula
    if( confl != CRef_Undef ) {  // handle UNSAT situation
      ok = false;
      if( opt_pb_semDebug ) cerr << "c unsatisfiable formula by final unit propagation" << endl;
      return false;
    }
    else return true;
  }
  
  return true;
}
