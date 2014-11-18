/***************************************************************************************[Solver.cc]
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

/**************************************************************************************************
This is a patched version of Minisat 2.2. [Marijn Heule, April 17, 2013]

The patch includes:
- The output of the solver is modified following to the SAT Competition 2013 output requirements
- The solver optionally emits a DRUP proof in the file speficied in argv[2]
**************************************************************************************************/

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"
#include "utils/Math.h"

using namespace std;
using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));

static IntOption     opt_learnt_max        (_cat, "learntMax",   "maximum number of learnt clauses", -1, IntRange(-1, INT32_MAX));

// options for PB reasoning
static BoolOption opt_gen_res_debug         ("GenResolution", "grdbg"  ,"print gen. resolution debug output", false);

static IntOption  opt_pb_to_clause_learning ("GenResolution", "grcls", "turn PB into clause on-the-fly (0=no,1=yes)", 0, IntRange(0, 1));
static BoolOption opt_recreate_cls_from_pb  ("GenResolution", "grlpbcls"  ,"turn learned PB into clause (if equiv)", false);
static BoolOption opt_turn_pb_to_cls        ("GenResolution", "grcpbcls"  ,"turn (interm.) conflict PB into clause (if equiv)", false);

// options for PB detection
static BoolOption opt_find_card      ("FindCard", "find-card"   ,"extract PB constraints from the CNF formula before search", true);
static BoolOption opt_exitAfterExtraction("FindCard", "exitAfterCard" ,"stop after found constraints have been extracted", false);
static IntOption opt_fm_debug_out    ("FindCard", "card-debug", "debug log level for finding card constraints", 0, IntRange(0, 4));
static Int64Option opt_fmSearchLimit ("FindCard", "card-Ylimit" ,"number of steps allowed for searching AMOs syntactically", 12000000, Int64Range(0, INT64_MAX));
static IntOption opt_fmMaxAMO        ("FindCard", "card-maxA"   ,"largest AMO that will be found during search", 200, IntRange(3, INT32_MAX));
static BoolOption opt_atMostTwo      ("FindCard", "card-amt"     ,"extract at-most-two", true);
static BoolOption opt_merge          ("FindCard", "card-merge"   ,"perform AMO merge", true);
static BoolOption opt_no_AMO_duplicates     ("FindCard", "card-no1Dup"    ,"avoid finding the same AMO multiple times", true);
static BoolOption opt_unlimited      ("FindCard", "card-noLim", "ignore search limits", false);
static BoolOption opt_multiVarAMO    ("FindCard", "card-vMul1"   ,"try to find multiple AMOs per variable", true);
static BoolOption opt_multiVarAMT    ("FindCard", "card-lMul2"   ,"try to find multiple AM2s per literals (expensive, can find many redundant ones)", false);
static BoolOption opt_rem_first      ("FindCard", "card-1st"     ,"extract first AMO candidate, or last AMO candidate", false);
static BoolOption opt_atMostOne      ("FindCard", "card-amo"     ,"extract amo approximately based on BIG", true);
static BoolOption opt_twoProduct     ("FindCard", "card-twoProd" ,"build an two-Product AMO out of the found AMOs", true);
static BoolOption opt_semCard        ("FindCard", "card-semCard" ,"use semantic analysis for finding cards", true);
static BoolOption opt_remDuplicates  ("FindCard", "card-sub",     "run substitution on AMOs", true);
static BoolOption opt_printCards     ("FindCard", "card-print",   "print found card constraints", false);
static BoolOption opt_printUnits     ("FindCard", "card-units",   "print unit clauses found so far", false);

// options for semantic search
static IntOption opt_minCardClauseSize ("FindCard", "card-minC"     ,"min clause size to find cards", 2, IntRange(2, INT32_MAX));
static IntOption opt_maxCardClauseSize ("FindCard", "card-maxC"     ,"max clause size to find cards", 16, IntRange(2, INT32_MAX));
static IntOption opt_maxCardSize       ("FindCard", "card-max"      ,"max card size that will be looked for", 24, IntRange(2, INT32_MAX));
static Int64Option opt_semSearchLimit  ("FindCard", "card-Elimit"   ,"number of steps allowed for searching AMOs semantically", 12000000, Int64Range(0, INT64_MAX));
static BoolOption opt_semDebug         ("FindCard", "card-sem-debug"    ,"print info during running semantic card find", false);
static BoolOption opt_noReduct         ("FindCard", "card-Units"  ,  "assume there are unit clauses inside the formula (more expensive)", true);


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  
  , nbReduceDB(0), nbReduceDBLnull(0), nbRemovedClauses(0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
  
  // Options for PB constraints
  //
  
  , pbwatches (WatcherDeleted(ca))
  
  , reasonPBs(0)
  , learnedPBs(0)
  , removedPBs(0)
  , resolvedPBs(0)
  , turnedLearnedPBintoCLS(0)
  , turnedIntermediatePBintoCLS(0)
  , pbResolves(0)
  , reasonPBsimplified(0)
  , globalPBsimplified(0)
  , gcdReduces(0)

  , ogrdbg( opt_gen_res_debug )
  , usePBtoClause( opt_pb_to_clause_learning )
  , oRecreateCls( opt_recreate_cls_from_pb )
  , oTurnIntermediatePBtoCLS( opt_turn_pb_to_cls )
  
   ,opt_pb_extractPB (opt_find_card)
   ,opt_pb_exitAfterExtraction(opt_exitAfterExtraction)
   ,fm_debug_out     (opt_fm_debug_out)
   ,opt_pb_fmSearchLimit (opt_fmSearchLimit)
   ,opt_pb_fmMaxAMO      (opt_fmMaxAMO )
   ,opt_pb_atMostTwo     (opt_atMostTwo )
   ,opt_pb_merge         (opt_merge          )
   ,opt_pb_no_AMO_duplicates (opt_no_AMO_duplicates )
   ,opt_pb_unlimited       (opt_unlimited        )
   ,opt_pb_multiVarAMO     (opt_multiVarAMO      )
   ,opt_pb_multiVarAMT     (opt_multiVarAMT      )
   ,opt_pb_rem_first       (opt_rem_first        )
   ,opt_pb_atMostOne       (opt_atMostOne        )
   ,opt_pb_twoProduct      (opt_twoProduct       )
   ,opt_pb_semCard         (opt_semCard          )
   ,opt_pb_remDuplicates   (opt_remDuplicates    )
   ,opt_pb_printCards      (opt_printCards       )
   ,opt_pb_printUnits      (opt_printUnits       )

// options for semantic search
   ,opt_pb_minCardClauseSize (opt_minCardClauseSize ) 
   ,opt_pb_maxCardClauseSize (opt_maxCardClauseSize  )
   ,opt_pb_maxCardSize      (opt_maxCardSize )      
   ,opt_pb_semSearchLimit   (opt_semSearchLimit    )
   ,opt_pb_semDebug ( opt_semDebug  )
   ,opt_pb_noReduct ( opt_noReduct )
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    
    // to perform conflict analysis with PB constraints
    levelSum. push(0);                    // add an element for the level calculation
    levelMaxWeight. push(0);              // add an element for the level calculation
    seenWeights .push(0);                 // add space for weight for PB variable
    
    // to perform unit propagation with PB constraints
    trailPosition .push(0);               // add space for the trail position of the variable
    pbwatches     .init(mkLit(v, false)); // init space in watch lists for pb constraints
    pbwatches     .init(mkLit(v, true )); // init space in watch lists for pb constraints
    
    return v;
}

bool Solver::addLEConstraint_( vec<Lit>& ps, vec<int64_t>& weights, int64_t k)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;
    
    cerr << "c add  constraint with " << ps << " and " << weights << " <= " << k << endl;
    
    // Check if clause is satisfied and remove false/duplicate literals:
    sortAccording(ps, weights);          // sort the first vector, and sort the elements of the later vector accordingly
    
    int keptLiterals = 0;
    Lit lastKeptLit = lit_Undef;
    
    // check for falsified and satisfied literals, check for complementary literals and for the same literals
    for (int i = 0; i < ps.size(); i++) {
      assert( ps[i] != lit_Undef && ps[i] != lit_Error && "the literals in the constraint must be real literals" );
      
      // first, make sure we are talking about positive weights only!
      if( weights[i] < 0 ) {
	weights[i] = -weights[i];
	ps[i]      = ~ps[i];
	k += weights[i];
      }
      assert( weights[i] >= 0 && "here we only have positive weights" );
      assert( ld64( abs64(k) ) < 64 && "we need to make sure that the degree of the constraint can be handled" );
      
      if (value(ps[i]) == l_True) {
	k -= weights[i]; // decrease the degree, and do not keep this literal
      } else if (value(ps[i]) == l_False) {
	continue;        // do not keep this literal
      } else {
	assert( value(ps[i]) == l_Undef && "the literal is unassigned" );

	if( ps[i] == lastKeptLit ) {
	  weights[keptLiterals] += weights[i]; // same literal like the last kept literal, hence, add the weight
	} else if ( ps[i] == ~lastKeptLit ) {  // complement literal as the last kept literal, hence, handle the weight
	  assert( lastKeptLit != lit_Undef && keptLiterals > 0 && "we already kept at least one literal" );
	  const int changePosition = keptLiterals - 1;          // position in the vectors that will be changed
	  int64_t commonMin = weights[changePosition] < weights[i] ? weights[changePosition] : weights[i];
	  k -= commonMin;                      // substract minimum from the degree
	  if( commonMin == weights[changePosition] ) {            // replace the other literal with the new literal
	    ps[changePosition] = ps[i];                           // because the new weight is bigger
	    weights[changePosition] = weights[i] - commonMin;     // replace the other weight
	    if( weights[changePosition] == 0 ) {                  // delete both literals
	      keptLiterals --; 
	      lastKeptLit = ( keptLiterals == 0 ? lit_Undef : ps[keptLiterals-1] );  // we just deleted the first pair
	    } else {
	      ps[changePosition] = ps[i];                         // keep the current literal, because it had a higher weight
	    }
	  } else {
	    weights[changePosition] -= commonMin;                 // just substract the minimum
	  }
	} else {
	  lastKeptLit = ps[i];                   // keep the current literal
	  ps[keptLiterals] = ps[i];
	  weights[keptLiterals++] = weights[i];
	}
      }
    }
    ps.shrink( ps.size() - keptLiterals );
    weights.shrink( ps.size() - keptLiterals );
    
    if( k < 0 ) {                           // the constraint is unsatisfiable
      ok = false; return false;             // hence return false
    } else if ( k == 0 ) {
      for (int i = 0; i < ps.size(); i++)   // the constraint results in units
	uncheckedEnqueue( ~ps[i] );         // hence enqueue all the complementary literals
    } else {

      // its a "usual" PB constraint
      if( ps.size() < 3 ) { // its a unit or binary

	if( ps.size() == 1 ) { // its a unit clause
	  if( weights[0] > k ) uncheckedEnqueue( ~ps[0] ); // enqueue the unit clause
	} else {               // its either two units, or a binary clause, or redundant
	  if( weights[0]  > k ) uncheckedEnqueue( ~ps[0] ); // enqueue the unit clause
	  if( weights[1]  > k ) uncheckedEnqueue( ~ps[1] ); // enqueue the unit clause
	  else if ( weights[0] + weights[1] > k && weights[0] <= k ) {
	    bool localOk = addClause( ~ps[0], ~ps[1] ); // add a clause that says the two literals cannot be set simultaneously
	    if( !localOk ) return false;                // adding this clause might fail. Still, we have to propagate all other literals
	  }
	} // its a constraint without literals, hence its redundant
	
      } else { // its a usual constraint
      
	// turn the constraint into a clause? check for weights that are greater than k!
	int64_t maximalSum = 0; 
	int64_t minimalWeight = -1, maximalWeight = 0; 
	keptLiterals = 0;                               // remove literals whose weight is too large
	for (int i = 0; i < ps.size(); i++) {
	  assert( value(ps[i]) == l_Undef && "we just removed all assigned literals in the previous loop" );
	  
	  // after finishing adapting k in the first loop, we can now check for literals
	  if( weights[i] > k ) { // do not keep literals whose weight is too large, but falsify them eagerly!
	    uncheckedEnqueue( ~ps[i] ); // the literal has to be set to false to not violate the current constraint
	    continue;  
	  }
	  
	  minimalWeight = (minimalWeight == -1 ? weights[i] : (weights[i] < minimalWeight ? weights[i] : minimalWeight ) ); // get smallest weight  
	  maximalWeight = ( weights[i] > maximalWeight ? weights[i] : maximalWeight );                                      // get greatest weight  
	  maximalSum += weights[i];                // collect the sum of all weights
	  ps[keptLiterals] = ps[i];              // keep the literal
	  weights[keptLiterals++] = weights[i];    // with its weight
	}
	ps.shrink( ps.size() - keptLiterals );
	weights.shrink( ps.size() - keptLiterals );
	
	// does the constraint constrain anything?
	if( maximalSum > k ) {
	  // turn constraint into a clause?
	  if( maximalSum - minimalWeight <= k ) { // can turn constraint into a clause
	    for( int i = 0; i < ps.size() ; ++ i ) ps[i] = ~ps[i];
	    return addClause_(ps);                // there could be a version without sorting, since ps is already sorted
	  }
	  // reduce the maximal weights
	  if( maximalSum - k < maximalWeight ) { // can reduce some weights in the GE world, hence reduce these weights here as well
	    const int64_t kPrime = maximalSum - k;
	    maximalSum = 0;
	    for( int i = 0; i < ps.size() ; ++ i ) {
	      weights[i] = weights[i] > kPrime ? kPrime : weights[i];
	      maximalSum += weights[i];
	    }
	    k = maximalSum - kPrime;
	  }
	  
	  // create the constraint, and add it to the data structures of the SAT solver
	  CRef pbref = ca.alloc( ps, weights, k, false ); 		// add the constraint as non-learnt clause
	  attachPB( pbref );					// add the current constraint to its watch lists
	  clauses.push( pbref );					// add the constraint to the clauses
	}
      }
    }
    
    // finally, check whether we had to propagate something
    return ok = (propagate() == CRef_Undef);
}

bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);

    vec<Lit>    oc;
    oc.clear();

    Lit p; int i, j, flag = 0;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++) {
        oc.push(ps[i]);
        if (value(ps[i]) == l_True || ps[i] == ~p || value(ps[i]) == l_False)
          flag = 1;
    }

    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (flag && (output != NULL)) {
      for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        fprintf(output, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
      fprintf(output, "0\n");

      fprintf(output, "d ");
      for (i = j = 0, p = lit_Undef; i < oc.size(); i++)
        fprintf(output, "%i ", (var(oc[i]) + 1) * (-2 * sign(oc[i]) + 1));
      fprintf(output, "0\n");
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert( !c.isPBconstraint() && "only add clauses with this method" );
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert( !c.isPBconstraint() && "only add clauses with this method" );
    assert( c.size() > 1 && "do not add simple cardinality constraints!");    
    
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    
    if( c.mark() != 0 ) return; // remove only, if not already removed (take care on the other places for DRUP and all that!)

    if (output != NULL) {
      fprintf(output, "d ");
      for (int i = 0; i < c.size(); i++)
        fprintf(output, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
      fprintf(output, "0\n");
    }

    if( !c.isPBconstraint() ) detachClause(cr);
    else detachPB(cr);
    
    // Don't leave pointers to free'd memory!
    if (!c.isPBconstraint() && locked(c)) {
      vardata[var(c[0])].reason = CRef_Undef;
      assert( decisionLevel() == 0 && "only remove reasons for literals on level 0!" );
    } else if ( c.isPBconstraint() ) {
      removedPBs ++;
      // check if the constraint would have been locked
      for( int i = 0 ; i < c.size(); ++ i ) { // check all variables of the constraint!
	const Var v = var(c.pbLit(i));
	if( value(c.pbLit(i)) == l_False && reason( v ) == cr ) { 
	  assert( (decisionLevel() == 0 || level(v) == 0 ) && "only remove reasons for literals on level 0!" );
	  vardata[v].reason = CRef_Undef;
	}
      }
    }
    
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
ClauseType Solver::analyze(CRef confl, vec< Lit >& out_learnt, vec< int64_t >& out_weights, int64_t& out_threshold, int& out_btlevel)
{
    if( ogrdbg ) cerr << "c analyze conflict " << ca[confl] << endl;
  
    // if any PB cnostraint should simply be turned into a clause during conflict analysis, use this method
    if( usePBtoClause ) return analyzePBtoClause( confl, out_learnt, out_weights, out_threshold, out_btlevel );
  
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    learnt_conflictLevelLits.clear(); // collect all literals that have been seen on the conflict level
    out_learnt.push();              // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];
	
	if(ogrdbg) cerr  << "c consider as next clause for analysis[" << confl << "]:  " << c << endl;
	
	if( c.isPBconstraint() ) { // perform PB learning
	  ClauseType learnedPBtyp = analyzePB( pathC, confl, p, index, out_learnt, learnt_conflictLevelLits, out_weights, out_threshold, out_btlevel );
	  if( learnedPBtyp != usualClause ) return pbConstraint;  // if a PB constraint was learned, return this constraint to the calling method (could be an empty clause)
	                                                          // otherwise, continue with the created clause
	  assert( learnedPBtyp == usualClause && "can continue only with a usual clause" );
	
	  
	} else {

	  if (c.learnt())
	      claBumpActivity(c);

	  for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
	      Lit q = c[j];

	      if (!seen[var(q)] && level(var(q)) > 0){
		  varBumpActivity(var(q));
		  seen[var(q)] = 1;
		  if (level(var(q)) >= decisionLevel()) {
		      pathC++;
		      learnt_conflictLevelLits.push( q ); // remember which literals have been used on the top level, so that the could be used for PB reconstruction // TODO: use push_ , because its faster!
		  } else
		      out_learnt.push(q);
	      }
	  }
        
	}
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
      
        if( opt_pb_semDebug ) cerr << "c minimize(2) clause " << out_learnt << " with trail: " << trail << endl;
      
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level)) // if decision literal, or not redundant
                out_learnt[j++] = out_learnt[i]; // keep literal
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

    return usualClause; // return the type of the clause

}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    
    if( opt_pb_semDebug ) {
      cerr << "c minimize literal " << p << " with stack " << analyze_toclear << endl;
    }
    
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
	const Lit currentRedundantLit = analyze_stack.last();
        Clause& c = ca[reason(var(currentRedundantLit))]; 
	analyze_stack.pop();

	if( !c.isPBconstraint() ) {	// use usual method, or use PB constraint

	  if( opt_pb_semDebug ) cerr << "c minimize literal " << currentRedundantLit << " with clause " << c << endl;

	  for (int i = 1; i < c.size(); i++){
	      const Lit q  = c[i];
	      if (!seen[var(q)] && level(var(q)) > 0){
		  if (reason(var(q)) != CRef_Undef && (abstractLevel(var(q)) & abstract_levels) != 0){
		      seen[var(q)] = 1;
		      analyze_stack.push(q);
		      analyze_toclear.push(q);
		  }else{
		      for (int j = top; j < analyze_toclear.size(); j++)
			  seen[var(analyze_toclear[j])] = 0;
		      analyze_toclear.shrink(analyze_toclear.size() - top);
		      return false;
		  }
	      }
	  }
	} else { // resolve with PB constraints

	  if( opt_pb_semDebug ) cerr << "c minimize literal " << currentRedundantLit << " with PB constraint " << c << endl;

	  for (int i = 0; i < c.size(); i++){	// iterate over all relevant literals of the constraint
	      const Lit pbp  = c.pbLit(i);
	      if( opt_pb_semDebug ) cerr << "check PB lit " << pbp << " s=" << (int)seen[var(pbp)] << " @=" << level(var(pbp)) << " tp=" << trailPosition[var(pbp)] << " true=" << (value(pbp) == l_True) << endl;
	      if (!seen[var(pbp)] 		// the variable is not yet in the resulting learned clause
		&& level(var(pbp)) > 0		// the variable is not assigned at decision level 0
		&& trailPosition[var(pbp)] < trailPosition[var(currentRedundantLit)] // the variable has been set before the the considered variable for resolution
		&& value(pbp) == l_True 	// the literal currently contributes to the sum (this excludes the literal that is used for resolution)
	      ){
		  const Lit q = ~pbp; // the literal in the reason clause is the complement!
		  if( opt_pb_semDebug ) cerr << "consider literal " << q << " coming from " << pbp << endl;
		  assert( value(q) == l_False && "value of all variables that are used here has to be false!" );
		  if (reason(var(q)) != CRef_Undef && (abstractLevel(var(q)) & abstract_levels) != 0){
		      seen[var(q)] = 1;
		      analyze_stack.push(q);
		      analyze_toclear.push(q);
		  }else{
		      for (int j = top; j < analyze_toclear.size(); j++)
			  seen[var(analyze_toclear[j])] = 0;
		      analyze_toclear.shrink(analyze_toclear.size() - top);
		      if( opt_pb_semDebug ) cerr << "c minimize literal " << q << " failed because of PB literal " << pbp << endl;
		      return false;
		  }
	      }
	  }
			  
	}	
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
            for (int j = ((c.size()==2) ? 0:1); j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    
    trailPosition[ var(p) ] = trail.size(); // store the position where the variable has been assigned
    
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()){
        const Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        num_props++;
        
	// propagate on usual clauses
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
	    assert( !c.isPBconstraint() && "in this list there should only be usual clauses" );
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
                uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);
	
	// TODO: could propagate all clauses first, and all PB constraints afterwards (rerun on the trail): would be more lazy, and more plain-CNF speed
	if( confl != CRef_Undef ) break;
	else { // propagate PB constraints only, if a conflict has not been found yet
	  // propagate PB constraint
	  vec<Watcher>&  pbws  = pbwatches[p];
	  Watcher        *pbws_element, *pbwsend;
	  for (pbws_element = (Watcher*)pbws, pbwsend = pbws_element + pbws.size();  pbws_element != pbwsend; ++pbws_element ){ // pointer arithmetic is faster than integer arithmetic
	     // Make sure the false literal is data[1]:
            CRef     cr = pbws_element->cref;
            const Clause&  c  = ca[cr];
	    
	    // assert( false && "implement time stamp based propagation here (PB constraint needs a field for satisfied time stamp with 64bits)" );
	    
	    if(ogrdbg) cerr  << "c propagate literal " << p << " on constraint " << c << endl;
	    
	    assert( c.isPBconstraint() && "in this list there should only be PB constraints" );
	    int64_t thisWeight = 0;
	    int64_t maxWeigth = -1; // maximum weight in the current constraint
	    for( int k = 0 ; k < c.size(); ++ k ) {
	      const int64_t& litWeight = c.pbWeight(k);
	      const Lit& thisLit = c.pbLit(k);
	      if( value( thisLit ) == l_True ) thisWeight = thisWeight + c.pbWeight(k); // TODO: could collect unassigned literals already
	      else if( value( thisLit ) == l_Undef ) maxWeigth = maxWeigth > litWeight ? maxWeigth : litWeight; // store the highest weight to check whether something has to be propagated
	    }
	    if( thisWeight > c.pbThreshold() ) { // constraint is falsified even before propagation
	      confl = cr;
	      break; // no need to copy the other watch list elements, because all literals of a consraint are watched
	    } else {
	      assert( thisWeight <= c.pbThreshold() && "here, there is no conflict yet" );
	      const int64_t weightDifference = c.pbThreshold() - thisWeight; // has to be positive, because of the above checks
	      if(ogrdbg) cerr  << "c maybe propagate. diff: " << weightDifference << " maxWeigth: " << maxWeigth << endl;
	      assert( maxWeigth != 0 && "the max weight cannot become 0" );
	      if ( maxWeigth > weightDifference && maxWeigth > 0) { // there are literals to be propagated
		for( int k = 0 ; k < c.size(); ++ k ) {
		  const Lit& thisLit = c.pbLit(k);
		  if( value( thisLit ) != l_Undef ) continue; // do not consider literals that have a value already
		  const int64_t& litWeight = c.pbWeight(k);
		  if( litWeight > weightDifference ) { // satisfying this literal will violate the constraint. so, enqueue the literal as false
		    if(ogrdbg) cerr  << "c use " << ca[cr] << " as reason for " << ~thisLit << " with weight "<< litWeight << " and diff: " << weightDifference << endl;
		    uncheckedEnqueue(~thisLit, cr); // assign the literal as false with this constraint as the reason
		    reasonPBs ++;                   // counter
		  } // any conflict would have been found above already, only undef literals are assigned
		}
	      }
	    }
	    // assert(false && "fix PB constraint propagation" );
	  }
	}
	// no need to shrink the watch list, because all elements stayed in the list
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
};
void Solver::reduceDB()
{
    nbReduceDB++; // statistics
    if( decisionLevel() == 0 ) nbReduceDBLnull++;
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2                                              // its not a binary clause
	    && !locked(c)                                             // its not locked
	    && (i < learnts.size() / 2 || c.activity() < extra_lim))  // its in the first half, or its not very active
	{
            removeClause(learnts[i]);
	    ++nbRemovedClauses;
	} else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    if(ogrdbg) cerr  << "c remove satisfied clauses" << endl;
    assert( decisionLevel() == 0 && "remove clauses only on top level?" );
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
	bool isSatisfied = false;
	if( c.isPBconstraint() ) {                  // check whether the PB constraint is satisfied
	  int64_t sum = 0, remainSum = 0;
	  for ( int k = 0 ; k < c.size(); ++ k ) {  // collect all weights of satisfied literals, and all undefined weights
	    sum       = (value(c.pbLit(k)) == l_True  ?       sum + c.pbWeight(k):       sum );
	    remainSum = (value(c.pbLit(k)) == l_Undef ? remainSum + c.pbWeight(k): remainSum );
	  } 
	  // if the remaining literals do not reach the total sum, then the constraint is satisfied
	  isSatisfied = (sum + remainSum <= c.pbThreshold());
	} else {
	  isSatisfied = satisfied(c); 
	}
	// if satisfied, then remove the clause/PB constraint
	if ( isSatisfied ) {
	  // cerr << "c remove the clause [" << cs[i] << " : " << ca[cs[i]] << endl;
	    removeClause( cs[i] );
	}
	else
	    cs[j++] = cs[i];
	
    }
    cs.shrink(i - j);
    if(ogrdbg) cerr  << "c removed " << i-j << " clauses" << endl;
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    int64_t     learnt_threshold;
    starts++;

    for (;;){
        CRef confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear(); learnt_weights.clear(); learnt_threshold = 0; // prepare analysis
            ClauseType learntClauseType = analyze(confl, learnt_clause, learnt_weights, learnt_threshold, backtrack_level);
            cancelUntil(backtrack_level);

	    if( learntClauseType == usualClause ) { // we learned a usual clause, proceed as usual
	      if (learnt_clause.size() == 1){
		  uncheckedEnqueue(learnt_clause[0]);
	      }else{
		  CRef cr = ca.alloc(learnt_clause, true);
		  if( ogrdbg ) cerr << "c learn clause [" << cr << "] " << ca[cr] << endl;
		  learnts.push(cr);
		  attachClause(cr);
		  claBumpActivity(ca[cr]);
		  uncheckedEnqueue(learnt_clause[0], cr);
	      }
	      if (output != NULL) {
		for (int i = 0; i < learnt_clause.size(); i++)
		  fprintf(output, "%i " , (var(learnt_clause[i]) + 1) *
				    (-2 * sign(learnt_clause[i]) + 1) );
		fprintf(output, "0\n");
	      }
	    } else if( learntClauseType == pbConstraint) { // currently there are only two types
	      learnedPBs ++;
	      static bool didIt = false;
	      if (output != NULL && !didIt ) {
		didIt = true; printf("c cannot output drup for learned PB constraint\n");
	      }
	      if( learnt_threshold == 0 ) {  // threhold == 0 -> assign all literals in the constraint to false!
		for( int i = 0 ; i < learnt_clause.size(); ++i ) {
// 		  assert( value( learnt_clause[i]) == l_Undef && "value of the learnt literal should not be set already" );
		  if( value( learnt_clause[i] ) == l_True ) { // learned a unit constraint that cannot be satisfied
		    ok = false; return l_False;
		  } else if ( value( learnt_clause[i] ) == l_Undef ) uncheckedEnqueue( ~learnt_clause[i] );
		  // FIXME check how assigned literals can end up in the vector!
		}
	      } else if( learnt_clause.size() == 1 ) { // the literal inside the pb constraint has to be falsified
		assert( value( learnt_clause[0]) == l_Undef && "value of the learnt literal should not be set already" );
		if( ogrdbg ) cerr << "c learn unit " << ~learnt_clause[0] << " from pb constraint " << endl;
		uncheckedEnqueue( ~learnt_clause[0] );
	      } else {
		CRef pbref = ca.alloc( learnt_clause, learnt_weights, learnt_threshold, true ); // add the constraint as non-learnt clause
		if( ogrdbg ) cerr << "c trail: " << trail << endl;
		if( ogrdbg ) cerr << "c learn pb constraint [" << pbref << "] " << ca[pbref] << endl;
		
		learnts.push( pbref );	    // add the constraint to the learned clauses, so that the constraint can be removed later on again
		attachPB( pbref );	    // add the current constraint to its watch lists
		claBumpActivity(ca[pbref]);// bump activity of the constraint
		
		// enqueue all literals of the constraint that have to be falsified (can be more than one, have to be at least one
		int64_t assignedSum = 0; // sumulate sum of satisfied literals
		for( int i = 0; i < learnt_clause.size(); ++ i ) {
		  if( value( learnt_clause[i] ) == l_True)  // if the literal is satisfied
		    assignedSum += learnt_weights[i];       // add its weight to the current sum
		}
		assert( assignedSum <= learnt_threshold && "after backtracking the learned constraint cannot be falsified" );
		int impliedLiterals = 0;                    // count the number of literals that are implied by this constraint
		for( int i = 0; i < learnt_clause.size(); ++ i ) {
		  if( value( learnt_clause[i] ) == l_Undef                   // if the literal is unassigned
		    && assignedSum + learnt_weights[i] > learnt_threshold ){ // and satisfying the literal violates the learned constraint
		      uncheckedEnqueue( ~learnt_clause[i], pbref );          // falsifiy the literal with the constraint as reason
		      impliedLiterals ++;                                    // count number of implied literals
		  }
		}
		assert( impliedLiterals > 0 && "at least one literal of the constraint has to be implied" );
		if( impliedLiterals <= 0 ) {
		  static bool didIt = false;
		  if( !didIt ) {
		    printf("c learned a PB constraint that does not imply any new unit\n");
		    exit(0);
		  }
		}
	      }
	      
// 	      assert( false && "continue implementation here" );
// 	      exit(-1); // TODO: continue here, handle how to insert learned clauses
	    } else {
	      // learned an unsatisfiable PB constraint
	      assert( learntClauseType == emptyClause && "for new constraints different methods would have to be developed" );	      
	      ok = false;
	      return l_False;
	    }

            varDecayActivity();
            claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

	    // for now, never remove formulas
//             if (learnts.size()-nAssigns() >= max_learnts)
	    if( (opt_learnt_max == -1 && learnts.size()-nAssigns() >= max_learnts) // have usual minisat dynamic removal
	        || learnts.size()-nAssigns() >= opt_learnt_max)                    // or have the static limit specified by the parameter
                // Reduce the set of learnt clauses:
                reduceDB();


            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    if( opt_pb_extractPB ) { // extract cardinality constraints from the CNF
      bool noUnsatFormula = findCards();
      if( opt_pb_semDebug ) cerr << "c find cardinalities exit code: " << noUnsatFormula << endl;
      if( !ok || !noUnsatFormula ) { 
	printf("c solved by cardinality detection\n");
	return l_False; // return that formula is unsatisfiable
      }
    }
    
    
    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("c ============================[ Search Statistics ]==============================\n");
        printf("c | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("c |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("c ===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("c ===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    for (int i = 0; i < 2; i++) { // consider all watch lists
      OccLists<Lit, vec<Watcher>, WatcherDeleted>& watchLists = (i==0 ? watches : pbwatches); 
      watchLists.cleanAll();
      for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watchLists[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }
    }

        
    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);
	if( level(v) > 0 ) {
	  if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))) {
	      ca.reloc(vardata[v].reason, to);
//	      cerr << "c new reason for " << v+1 << " is " << vardata[v].reason << endl;
	  }
	} else vardata[v].reason = CRef_Undef; // overwrite the reason on level 0
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}


void Solver::garbageCollect()
{
    cerr << "c preform garbage collection" << endl;
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    assert( ca.size() >= ca.wasted() && "something should be left in the garbage collector" );
    ClauseAllocator to(ca.size() - ca.wasted()); 

    // printf ( "c CORE collect garbage with extra field %d to extra field %d\n", to.extra_clause_field, ca.extra_clause_field );
    
    relocAll(to);
    
    cerr << "c old space: " << ca.size() << " new space: " << to.size() << endl;
    
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}


void Solver::attachPB     (CRef cr)
{
  // pbwatches
  const Clause& c = ca[cr];
  assert( c.isPBconstraint() && "only add pb constraints with this method" );
  assert( c.size() > 1 && "do not add simple cardinality constraints!");
  for( int i = 0 ; i < c.size(); ++ i ) // add constraints to all PB watch lists
    pbwatches[ c.pbLit(i) ].push( Watcher(cr,lit_Undef) ); 
  // TODO: yet no statistics on constraints inside solver
}

void Solver::detachPB     (CRef cr, bool strict)
{
    const Clause& c = ca[cr];
    assert( c.isPBconstraint() && "only add pb constraints with this method" );
    assert( c.size() > 1 && "do not add simple cardinality constraints!");    
    
    if (strict){
      for( int i = 0 ; i < c.size(); ++ i ) // remove constraint from all watch lists
        remove(pbwatches[ c.pbLit(i) ], Watcher(cr, lit_Undef));
    }else{
      // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
      for( int i = 0 ; i < c.size(); ++ i ) // remove constraint from all watch lists
        pbwatches.smudge( c.pbLit(i) );
    } 
}


// conflict analysis with turning PB constraints into clauses
ClauseType Solver::analyzePBtoClause(CRef confl, vec<Lit>& out_learnt, vec<int64_t>& out_weights, int64_t& out_threshold, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();              // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];
	
	if(ogrdbg) cerr  << "c consider as next clause for analysis[" << confl << "]:  " << c << endl;
	
	if (c.learnt())
	      claBumpActivity(c);
	
	if( !c.isPBconstraint() ) {
	  for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){ // iterate over the clause
	      const Lit q = c[j];
	      if (!seen[var(q)] && level(var(q)) > 0){ // if variable is not already in constraint (there is only one possible way for the polarity), then add the variable
		  varBumpActivity(var(q));
		  seen[var(q)] = 1;
		  if (level(var(q)) >= decisionLevel()) {
		      pathC++;
		  } else
		      out_learnt.push(q);
	      }
	  }
	} else {
	  resolvedPBs ++;  
	  for (int j = 0 ; j < c.size(); j++){ // constraints are not re-ordered, hence, scan the whole constraint
	      const Lit pbq = c.pbLit(j);
	      if (!seen[var(pbq)] && level(var(pbq)) > 0){ // if variable is not already in constraint (there is only one possible way for the polarity), then add the variable

		  if( trailPosition[var(pbq)] > index // has been assigned after the current literal that is used for resolution TODO: having later literals is fine for resolving constraints in general
		      || value(pbq) != l_True )          // is not set to true, and hence does not contribute to the sum
		    continue; // for now, ignore each literal that does not contribute to the current sum!
		    
		  const Lit q = ~pbq; // to construct the reason clause from the constraint, we simply use the complement of the literal
		  varBumpActivity(var(q));
		  seen[var(q)] = 1;
		  if (level(var(q)) >= decisionLevel()) {
		      pathC++;
		  } else
		      out_learnt.push(q);
	      }
	  }	  
	}
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        
        if( opt_pb_semDebug ) cerr << "c minimize(2) clause " << out_learnt << " with trail: " << trail << endl;
      
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{						// check whether the reason clause can strengthen the current learned clause
                Clause& c = ca[reason(var(out_learnt[i]))];
		if( !c.isPBconstraint() ) {
		  for (int k = 1; k < c.size(); k++)
		      if (!seen[var(c[k])] && level(var(c[k])) > 0){ // if there is another variable in the reason clause, then no strengthening is possible
			  out_learnt[j++] = out_learnt[i];
			  break; }
		} else { // simple minimize with PB constraints
		  for (int k = 0; k < c.size(); k++)
		  {
		      const Lit pbck = c.pbLit(k);
		      if (!seen[var(pbck)] 		// the variable is not yet in the learned clause
			  && level(var(pbck)) > 0	// the variable is not set on the top level
			  && trailPosition[var(pbck)] < trailPosition[var(out_learnt[i])] 	// the variable has been set before the the considered variable for resolution
		          && value(pbck) == l_True 	// the literal currently contributes to the sum
		      ){
			  out_learnt[j++] = out_learnt[i]; // keep the current literal, because its reason clause cannot strengthen the learned clause
			  break; 
		      }
		  }
		}
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

    return usualClause; // return the type of the clause 
}

/** perform conflict analysis with PB constraints
 * 
 * the procedure stores each weight of the variables in a single int64_t, no per literal. hence, during addition extra care is required
 *    (when adding to the global constraint weight, add if signs are the same, substract when the signs are different, and also substract max(0,this difference) from the global k
 * 
 * @param confl clause/constraint that is currently under conflict
 * @param p literal that has to be resolved on next
 * @param out_learnt literals of the learned constraint (with a level not on the conflict level)
 * @param conflictLevelLiterals literals of the learned constraints (with a level on the conflict level)
 * @param out_weights weights of the literals in the constraint
 * @param out_threshold degree of the constraint that is returned
 * @param out_btlevel backtracking level that makes the returned constraint unit
 * @return type of the learned constraint (PB or clause)
 * 
 * The implementation separates literals and weights of the current constraint. Literals are always variables, but the weights can be negative (to indicate that the literal is negative). This way, we only need a weight per variable.
 * The weights for each variable are stored in the single array seenWeights (reserving one weiht for each variable of the formula)
 * 
 */
ClauseType Solver::analyzePB(int& pathC, CRef& confl, Lit& p, int& index, vec< Lit >& out_learnt, vec<Lit>& conflictLevelLiterals, vec<int64_t>& out_weights, int64_t& out_threshold, int& out_btlevel)
{
  // setup the current learnt clause into a PB constraint
  int64_t threshold = 0;    // threshold of the current constraint
  int64_t globalDiff = 0;  // difference to be satisfied of the current constraint:  for satisfied x_i:  (sum_i w_i) - k
  for( Var v = 0 ; v < nVars(); ++v ) assert( seenWeights[v] == 0 && "should be cleared in this point" );
  
  // FIXME TODO improvements learned from the prototype
  // - keep all literals in the resulting constraint
  // - resolve only on variable that are satisfied (that make the constraint falsified)
  // - for the asserting level and the evaluation of being falsified, consider only the variable before the last resolve variable
  // - the asserting level is the level where only one variable is satisfied, and together with the satisfied variables on the previous level the constraint is falsified
  // assert( false && "collect all literals from all PB constraints. for checking asserting, or to select the next resolve-variable, consider only 'satisfied' literals that have been assigned before the previous resolve variable" );
  
  if(ogrdbg) cerr << endl << endl << "c next PB conflict analysis (" << conflicts << " ) with literal p=" << p << endl << endl << "c " << trail << endl << endl;

  /**
   *  Turn this current conflict clause into a PB constraint
   *  the revealed conflict has not been a PB constraint, so there exists a clause already. Therefore, there already a literal p to resolve on next. 
   */
  if( p != lit_Undef ) { // hence, turn this clause into an <= PB constraint
    if(ogrdbg) cerr  << "c current conflict with lit " << p << "  :  " << out_learnt << " and remainder " << conflictLevelLiterals << endl << "c current confl: " << ca[confl] << endl;
    assert( out_learnt.size() + conflictLevelLiterals.size() > 2 && "the passed clause to this procedure should not be a unit clause" );
    
    
    if(ogrdbg) cerr << "c turn current learned clause into PB constraint" << endl;
    // shape of the clause: out_learnt[1:] or ( l | conflictLevelLiterals, seen[var(l)] ) >= 1
    // turn into PB constraint ( k = n - 1, have weight -1 for all literals in the clause, extra care for literals in conflictLevelLiterals)
    for( int i = 1 ; i < out_learnt.size(); ++ i ) {
      assert( level( var( out_learnt[i] ) ) > 0 && "all literals in this vector have a higher level" ); // if the literal is not assigned on the top level, add the literal to the constraint
      if(ogrdbg) cerr  << "c add clause literal " << out_learnt[i] << " to the constraint" << endl;
      seenWeights[ var( out_learnt[i] ) ] = sign(out_learnt[i]) ? 1 : -1; // if negative, assign + 1 weight, otherwise, assign -1 weight
      seen[ var( out_learnt[i] ) ] = 0; // clear seen structure
      out_learnt[i-1] = mkLit( var(out_learnt[i]), false );  // compress vector, and store all literals positively
    }
    out_learnt.shrink_(1); // remove the last space
    for( int i = 0; i < conflictLevelLiterals.size(); ++ i ) {
      if( seen[ var( conflictLevelLiterals[i] ) ] ) { // consider the literals only if they are still in the clause
	assert( seenWeights[ var( conflictLevelLiterals[i] ) ] == 0 && "before initialization the weights have to be cleared" );
	if( level( var( conflictLevelLiterals[i] ) ) > 0 ) { // only add literals that are not assigned at the top level
	  seenWeights[ var( conflictLevelLiterals[i] ) ] = sign(conflictLevelLiterals[i]) ? 1 : -1; // if negative, assign + 1 weight, otherwise, assign -1 weight
	  seen[ var( conflictLevelLiterals[i] ) ] = 0; // clear seen structure
	  if(ogrdbg) cerr  << "c add clause literal " << conflictLevelLiterals[i] << " to the constraint" << endl;
	  out_learnt.push( mkLit( var(conflictLevelLiterals[i]), false ) ); // store positive literal
	} else {
	  assert( value( out_learnt[i] ) == l_False && "in the conflict clauses there can be only falsified literals" );
	}
      } else {
	// count redundant operations?
      }
    }
    // take care of the literal p
    assert( seen[var(p)] == 0 && "this literal has just been removed" );
    assert( seenWeights[ var( p ) ] == 0 && "the weights have to be cleared" );
    assert( level(var(p)) > 0 && "the decision level of the asserting literal cannot be the top level" );
    seenWeights[ var( p ) ] = sign(p) ? -1 : 1; // variable p has the opposite polarity
    out_learnt.push( mkLit(var(p),false) );
    if(ogrdbg) cerr  << "c add the current asserting literal " << ~p << endl;
    // take care of the threshold
    threshold = out_learnt.size() - 1; // <= threshold for clauses is n-1
    globalDiff = 1;                   // diff for a conflict clause is always +1!
  } else {                             // the PB constraint is the conflict
    out_learnt.clear();                // for now there are no literals in the new constraint
  }

  /**
   *  Initialize variables, check assertions
   */
  // continue analysis with passed clause with ref confl (confl has to be a PB constraint!)
  assert( ca[confl].isPBconstraint() && "the passed clause has to be a PB constraint" );
  for( Var v = 0 ; v < nVars(); ++v ) assert( seen[v] == 0 && "should be cleared in this point" );
  
  // independent of p the analyze loop can now be continued, but now handling PB constraints
  int64_t scaleConstraint = 1;                                 // scale factor for all weights of the current reason constraint
  int64_t scaleGlobal = 1;                                     // scale factor for the currently conflict constraint (the learned constraint)
  int maxLevel = -1, maxLevelLiterals = 0, maxLevelUnsats = 0; // count how many literals there are of the highest decision level
  Var maxLevelVar = var_Undef;                                 // asserting literal
  int64_t assertingLevel = -1;                                 // the level to be jumped back to
  int64_t minWeight = -1, maxWeigth = -1;                      // to check whether the current PB constraint is actually a clause 
  int64_t sumWeight = 0, assignedSum = 0;                      // to check whether the current PB constraint is actually a clause (sums)
  
  /**
   *  major resolve loop
   */
  do {
        assert(confl != CRef_Undef && "cannot resolve on a decision literal"); 
        Clause& c = ca[confl];                    // next constraint to be considered
	int64_t thisDiff = 0;                     // diff of the constraint to resolve with, is initialized in the first iteration for a PB constraint
	
	scaleConstraint = (p==lit_Undef ? 1 : seenWeights[ var(p) ]);                // factor with which to scale the currently learned constraint (is the weight of the variable to be resolved)
	scaleConstraint = scaleConstraint < 0 ? -scaleConstraint : scaleConstraint;  // the factor has to be positive
	assert( (p == lit_Undef || seenWeights[ var(p) ] != 0) && "if we want to do resolution, the variable should be in the global constraint" );
	
	maxLevel = -1, maxLevelLiterals = 0; // count how many literals there are of the highest decision level (does not need to be the conflict level!)
	maxLevelVar = var_Undef;             // if there is only one variable left, we have a UIP
	
	assert( (globalDiff > 0 || p== lit_Undef) && "if we currently see a conflict, then its diff has to be greater than 0!" );

	scaleGlobal = 1; // scale factor for a clause will always be 1
	
	/**
	 *  resolve with another PB constraint
	 */
	if( c.isPBconstraint() ) {
	  if(ogrdbg) cerr << endl << endl << "c resolve with PB constraint on " << p << endl;
	  // preprocess PB constraint so that has the properties of a reason clause (all literals falsified, two literals of the current level)
	  // if variables should be removed, then remove all variables that have a higher position in the trail then the current index
	  // This way the resulting constraint should keep the properties of a reason constraint
	  // TODO really necessary to modify the constraints in advance?

	  /**
	   *  select the weight of the curent variable to scale the other constraint
	   *  store the clashing variables
	   */
	  int64_t resolveWeight = 0;              // store weight to indicate whether the reason constraint has been simplified (cannot be 0 if a real clause is constructed)
	  int64_t simplifiedThreshold = 0;        // indicate whether the reason constraint has been simplified (cannot be 0 if a real clause is constructed)
	  if( p != lit_Undef ) {                  // only if we are currently not loading the conflict

	    // analyze the reason constraint
	    clashingPairs.clear();                  // initially, there are no clashing pairs of literals
	    for (int j =0; j < c.size(); j++){      // TODO: get this scale constant during running over the trail, or when initializing the constraint
	      const Lit cj = c.pbLit(j);
	      if( value(cj) == l_True && trailPosition[var(cj)] <= index ) thisDiff += c.pbWeight(j);  // sum up this weight, because the variable is satisfied and has been set before the current variable
	      assert( thisDiff >= 0 && "has to be positive (otherwise overflow!)" );
	      if( var(cj) == var(p) ) {                                                                // if this variable is the variable to resolve on
		scaleGlobal = c.pbWeight(j);                                                           // set the scale factor
		scaleGlobal = scaleGlobal < 0 ? -scaleGlobal : scaleGlobal;                            // the factor has to be positive
	      } else {
		if( seenWeights[ var(cj) ] != 0 ) {                                                                       // the variable is present in both constraints
		  if( ( seenWeights[ var(cj) ] > 0 && sign(cj) ) || ( seenWeights[ var(cj) ] < 0 && !sign(cj) ) ) {       // the polarities are complementary
		    clashingPairs.push( seenWeights[ var(cj) ] > 0 ? seenWeights[ var(cj) ] : - seenWeights[ var(cj) ] ); // put the weight of the first constraint
		    clashingPairs.push( c.pbWeight(j) );                                                                  // push the weight of the second constraint
		  }
		}
	      }
	    }
	    thisDiff -= c.pbThreshold(); // substract the threshold to obtain the final diff (before, thisDiff stored the sum of previously satisfied literals)
	    
	    assert( scaleGlobal > 0 && "constraints have to be scaled by a positive value" );
	    assert( (clashingPairs.size() & 1) == 0 && "the number of elements in the vector has to be even" );
	    assert( thisDiff <= 0 && "(the relevant part of) reason constraints cannot be falsified" );
	    assert( thisDiff + scaleGlobal > 0 && "the given constraint has to be a reason constraint for the selected literal p" );
	    
	    /**
	    *  scale factors
	    */
	    if( scaleGlobal == scaleConstraint ) {scaleGlobal = 1; scaleConstraint = 1; }  // very simple scaling
	    else {                                                                         // otherwise scale only, if the numbers are not equal
	      int64_t greatestCommonDivisor = gcd(scaleConstraint, scaleGlobal);           // use only, if numbers are bigger? TODO use the binary variant of the algorithm?
	      assert( greatestCommonDivisor > 0 && "the two numbers should not be 0" );
	      if( greatestCommonDivisor != 1 ) { 
		scaleGlobal /= greatestCommonDivisor;       // adopt the two constraints
		scaleConstraint /= greatestCommonDivisor;   // adopt the two constraints
		gcdReduces ++;                              // statistics
	      } // result is always an integer!
	    }

	    /**
	     *  check for number overflow of global constraint
	     */
	    const int64_t newThreshold = threshold * scaleGlobal + (simplifiedThreshold == 0 ? c.pbThreshold() : simplifiedThreshold ) * scaleConstraint; 
	    if( newThreshold < threshold          // during addition, we jumped over the 64bit boundary (63bit and sign bit)
	      || ld64( scaleGlobal ) + ld64( abs64(threshold) ) > 60 // scaled threshold would become too large
	      || ld64( scaleConstraint ) + ld64( abs64( simplifiedThreshold == 0 ? c.pbThreshold() : simplifiedThreshold ) ) > 60 // scaled threshold would become too large
	      || ld64( abs64(newThreshold) ) > 60 // we came too close to the precision limit
	      || newThreshold <= 0 )              // we turned the positive threshold into a negative one
	     {      // scale the global constraint, for now, turn it into a clause TODO turn it into some simplified constraint based on the clause, with a small weight for the resolution literal
	       
	       // TODO have extra method
	       globalPBsimplified++;
	       // simplifyGlobalConstraint( threshold, p, globalDiff );
	       int keptLiterals = 0;
	       const int resolutionPosition = index;                                   // here the literal for resolution has been added
	       for( int j = 0 ; j < out_learnt.size() ; ++ j ) {
		 const Lit cj = out_learnt[j];
		 if( trailPosition[ var(cj) ] <= index +1 &&                           // the literal has been assigned before the resolution literal 
		   (    (value( var(cj) ) == l_True  && seenWeights[ var(cj) ] > 0)    // the literal contributes to the current sum (and is positive)
		     || (value( var(cj) ) == l_False && seenWeights[ var(cj) ] < 0) )  // the literal contributes to the current sum (and is negative)
		 ) {
		   seenWeights[ var(cj) ] = seenWeights[ var(cj) ] < 0 ? -1 : 1;       // reduce the weight to 1 or -1
		   out_learnt[keptLiterals ++] = out_learnt[j];                        // count the number of kept literals
		 } else {
		   if( ogrdbg ) cerr << "c skip variable " << var(cj) + 1 << " with position " << trailPosition[ var(cj) ] << "/" << index << " and true= " << (value(var(cj)) == l_True) << " and weight " << seenWeights[ var(cj) ] << endl;
		   seenWeights[ var(cj) ] = 0;
		 }
	       }
	       assert( abs64(seenWeights[ var(p) ]) == 1 && "the variable is still in the constraint" );
	       
	       out_learnt.shrink_( out_learnt.size() - keptLiterals );                 // remove the redundant literals
	       threshold = out_learnt.size() - 1;                                      // reduce the threshold to fit the clause
	       globalDiff = 1;                                                         // determine the new globalDiff (for a conflict clause its always 1)
	       // END of extra method
	       
	       continue; // repeat the resolution loop with the same reason clause, but now the conflict constraint has been scaled
	    }
	    
	    /**
	     *  calculate the new diff for the linear combination of the constraints
	     */
	    int64_t clashDiff = 0;
	    for( int j = 0; j < clashingPairs.size(); j += 2 ) {
	      const int64_t clashFirst = clashingPairs[j] * scaleGlobal;         // scaled weight of clashing literal of first constraint
	      const int64_t clashSecond = clashingPairs[j+1] * scaleConstraint;  // scaled weight of clashing literal of second constraint
	      clashDiff += clashFirst <= clashSecond ? clashFirst : clashSecond; // the clash sum is the minimum of the two values
	    }

	    /**
	    *  modify reason constraint, if its diff is not small enough!
	    */
	    bool needToScale = ( scaleConstraint * c.pbThreshold() > (1ull << 60ull) );  // the current constraint reached the numerical limit
	    needToScale = needToScale  || ( scaleGlobal * threshold > (1ull << 60ull) ); // the global constraint reached the numerical limit
	    int64_t newDiff = scaleConstraint * thisDiff + scaleGlobal * globalDiff - clashDiff; // new difference is sum of old and new difference, regarding the clashing literals
	    if(ogrdbg) cerr << "c calculated new diff: " << newDiff << " ( reason: " << scaleConstraint << "x" << thisDiff << ", and global: " << scaleGlobal << "x" << globalDiff << " and clash: " << clashDiff << ")  needToScale: " << needToScale << endl;
	    if( newDiff <= 0 || needToScale ) {
	      reasonPBsimplified++;
	      simplifiedWeights.clear();               // simplification will add modified weights of the constraint
	      // BEGIN simplify by constructing a clause
	      // TODO have a better variant than transformation into clauses, for the prototype use this transformation
	      simplifiedThreshold = 0;
	      if( ogrdbg ) cerr << "c simplify " << c << ", because newDiff= " << newDiff << endl;
	      for (int j =0; j < c.size(); j++){      // TODO: get this scale constant during running over the trail, or when initializing the constraint
		const Lit cj = c.pbLit(j);
		if( var(cj) == var(p) ||                                          // the literal is the literal that is used for resolution
		  ( value(cj) == l_True && trailPosition[var(cj)] <= index ) ){   // or the literal was satisfied before the constraint became reason for the literal
		  simplifiedWeights.push( 1 );  // add this literal to the clause
		  simplifiedThreshold ++;       // increase the threshold by one
		  if( ogrdbg ) cerr << "c keep literal     " << cj << " with weight " << c.pbWeight(j) << " sat=" << (int)(value(cj) == l_True)  << " pos=" << trailPosition[var(cj)] << " ind=" << index << " resolve=" << p << endl;
		} else {
		  if( ogrdbg ) cerr << "c simplify literal " << cj << " with weight " << c.pbWeight(j) << " sat=" << (int)(value(cj) == l_True)  << " pos=" << trailPosition[var(cj)] << " ind=" << index << " resolve=" << p << endl;
		  simplifiedWeights.push( 0 );
		}
	      }
	      simplifiedThreshold --;
	      // adopt the new scaling factors
	      scaleGlobal = 1;
	      scaleConstraint = (p==lit_Undef ? 1 : seenWeights[ var(p) ]);                // factor with which to scale the currently learned constraint (is the weight of the variable to be resolved)
	      scaleConstraint = scaleConstraint < 0 ? -scaleConstraint : scaleConstraint;  // the weight of the literal in the clause is always 1, so that the reason has to be scaled with the weight of the variable in the global constraint
	      // END simplify by constructing a clause

	      if( ogrdbg ) {                                             // display the simplified constraint
		cerr << "c simplified " << c << " to "; 
		for( int j = 0 ; j < c.size(); ++ j ) {
		  if( simplifiedWeights[j] == 0 ) continue;              // ignore removed variables
		  cerr << " +"  << simplifiedWeights[j] << " " << c.pbLit(j); 
		}
		cerr << " <= " << simplifiedThreshold << endl;           // show new threshold
	      }
	      assert( simplifiedThreshold != 0 && "the simplified threshold has to be greater than 0" );
	    }
	    assert( (simplifiedThreshold == 0 || simplifiedWeights.size() == c.size()) && "either we do not have a simplified constraint, or its size matches the size of the actual reason constraint" );
	  } // END if (p != lit_Undef)
	  
	  /**
	   *  produce the resolvent of the two constraints!
	   * ( adopted learning loop for PB constraints )
	   */	  
	  // display the current two constraints and the scale factors
	  if( ogrdbg ) { 
	    cerr << "c to  " << scaleGlobal << " x " ; 
	    for( int j = 0 ; j < out_learnt.size(); ++ j ) 
	      cerr << " +"  << (seenWeights[ var(out_learnt[j]) ] < 0 ? - seenWeights[ var(out_learnt[j]) ] : seenWeights[ var(out_learnt[j]) ]) << " " << (seenWeights[ var(out_learnt[j]) ] < 0 ? ~out_learnt[j] : out_learnt[j] ); 
	    cerr << " <= " << threshold << endl; 
	    cerr << "c add " << scaleConstraint << " x " << c << endl; }

	  // calculate the new threshold and then perform the linear combination with the two factors
	  int64_t oldThreshold = threshold;
	  threshold = threshold * scaleGlobal + (simplifiedThreshold == 0 ? c.pbThreshold() : simplifiedThreshold ) * scaleConstraint; // scale the threshold in advance! // TODO add comment why this is done!
	  assert( oldThreshold < threshold && "threshold cannot increase" );
	  assert( ld64( abs64(threshold) ) < 61 && "ensure that the precision limit is kept" );
	  assert( threshold > 0 && "before the actual resolution (but after adding both thresholds) the threshold has to be greater than 0" );
	  
	  if(ogrdbg) cerr  << "c initial threshold: " << threshold << endl;
	  for (int j =0; j < c.size(); j++){ // process all literals of the current reason-constraint
	      const Lit q = c.pbLit(j);      // literal to be considered next
	      
	      /**
	       *  handle latter assigned literals special (e.g. avoid them?) larger constraints are usually better for \le-world
	       * // TODO: decide whether literals of higher levels could still be considered, because they would lead to a larger constraint
	       */
// 	      if(false && ( trailPosition[ var(q) ] > index + 1 || value(q) == l_Undef ) ){ // do not use variables that are not assigned or have been assigned after literal p, because
// 		if(ogrdbg) cerr  << "c skip the literal " << q << " at " << trailPosition[ var(q) ] << " vs " << index + 1 << endl;
// 		continue;                                // these variables took not part in being the reason for the current assignment, but are still helpful!
// 	      }

	      const int64_t& actualWeight = simplifiedThreshold == 0 ? c.pbWeight(j) : simplifiedWeights[j];                // choose the weight from the actual or the simplified constraint
	      if( actualWeight == 0 ) continue;                                                                             // do not use this variable, because it has been dropped during simplification

	      const int64_t thisWeight = sign(q) ? (-actualWeight * scaleConstraint) : (actualWeight * scaleConstraint);
	      const int64_t varWeight = seenWeights[ var( q ) ] * scaleGlobal;
      
	      if(ogrdbg) cerr  << "c use var " << var(q) + 1 << " with " << thisWeight << " , truth value " << value(var(q)) << " and global weight " << varWeight << endl;
	      
	      if( level(var(q)) == 0 ) { // handle top level literals specially, remove them from the constraint and adapt the threshold
		assert( seenWeights[ var(q) ] == 0 && "there should not be a top level literal inside the constraint" );
		if( value(q) == l_True ) threshold -= abs64(thisWeight); // substract current weight from threshold, because variable is already fixed
		if(ogrdbg) cerr  << "c handle top level variable " << var(q) + 1 << "  new threshold: " << threshold << endl;
		continue;                                              // nothing more to be done with this variable
	      }
	      
	      // update weight for var(q), adapt threshold, handle maxLevel infos
	      updateCurrentPBWithResolveVariable( q, threshold, out_learnt, thisWeight, varWeight, maxLevelLiterals, maxLevelVar, maxLevel );
	  }
	  resolvedPBs ++; 
	  // update activity here, because the loop might be re-executed several times due to scaling constraints
	  if (c.learnt()) claBumpActivity(c);       // if learned, increase the activity of the constraint
	  
	} 
	else
	{ 
	  /**
	   *  resolve the current PB constraint with the current clause!
	   */
	  if(ogrdbg) cerr  << "c resolve with clause on " << p << endl;

// adopted learning loop for PB constraints
	  const int64_t greatestCommonDivisor = 1; // this is always the case, since weights in clauses are always -1 // TODO inline by hand
	  const int64_t constraintWeight = -scaleConstraint; // all literals in the clause have weight -1
	  // display the current two constraints and the scale factors
	  if( ogrdbg ) {
	    cerr << "c to  " << scaleGlobal << " x " ;
	    for( int j = 0 ; j < out_learnt.size(); ++ j ) 
	      cerr << " +" << (seenWeights[ var(out_learnt[j]) ] < 0 ? - seenWeights[ var(out_learnt[j]) ] : seenWeights[ var(out_learnt[j]) ])  << " " << (seenWeights[ var(out_learnt[j]) ] < 0 ? ~out_learnt[j] : out_learnt[j] ); 
	    cerr << " <= " << threshold << endl << "c add " << scaleConstraint << " x " << c << endl;
	    cerr << "c which is " << scaleConstraint << " x ";
	    for( int j = 0 ; j < c.size(); ++j ) cerr << " +1 " << ~c[j];
	    cerr << " <= " << c.size() - 1 << endl;
	  }
	  
	  /**
	   *  check for number overflow of global constraint
	   */
	  const int64_t newThreshold = threshold * scaleGlobal + (c.size() - 1 ) * scaleConstraint; 
	  if( newThreshold < threshold          // during addition, we jumped over the 64bit boundary (63bit and sign bit)
	    || ld64( abs64(newThreshold) ) > 60 // we came too close to the precision limit
	    || newThreshold <= 0 )              // we turned the positive threshold into a negative one
	   {      // scale the global constraint, for now, turn it into a clause TODO turn it into some simplified constraint based on the clause, with a small weight for the resolution literal
	       
	       // TODO have extra method
	       globalPBsimplified++;
	       // simplifyGlobalConstraint( threshold, p, globalDiff );
	       int keptLiterals = 0;
	       const int resolutionPosition = index;                                   // here the literal for resolution has been added
	       for( int j = 0 ; j < out_learnt.size() ; ++ j ) {
		 const Lit cj = out_learnt[j];
		 if( trailPosition[ var(cj) ]  <= index + 1 &&                         // the literal has been assigned before the resolution literal 
		   (    (value( var(cj) ) == l_True  && seenWeights[ var(cj) ] > 0)    // the literal contributes to the current sum (and is positive)
		     || (value( var(cj) ) == l_False && seenWeights[ var(cj) ] < 0) )  // the literal contributes to the current sum (and is negative)
		 ) {
		   seenWeights[ var(cj) ] = seenWeights[ var(cj) ] < 0 ? -1 : 1;       // reduce the weight to 1 or -1
		   out_learnt[keptLiterals ++] = out_learnt[j];                        // count the number of kept literals
		 } else {
		   seenWeights[ var(cj) ] = 0;
		 }
	       }
	       assert( abs64(seenWeights[ var(p) ]) == 1 && "the variable is still in the constraint" );
	       
	       out_learnt.shrink_( out_learnt.size() - keptLiterals );                 // remove the redundant literals
	       threshold = out_learnt.size() - 1;                                      // reduce the threshold to fit the clause
	       globalDiff = 1;                                                         // determine the new globalDiff (for a conflict clause its always 1)
	       // END of extra method
	       
	       assert( seenWeights[ var(p) ] != 0 && "the variable is still in the constraint" );
	       continue; // repeat the resolution loop with the same reason clause, but now the conflict constraint has been scaled
	  }
	  
	  int64_t oldThreshold = threshold;
	  threshold = threshold * scaleGlobal + (c.size() - 1) * scaleConstraint; // scale the threshold in advance!
	  assert( oldThreshold < threshold && "threshold cannot increase" );
	  assert( ld64( abs64(threshold) ) < 61 && "ensure that the precision limit is kept" );
	  assert( threshold > 0 && "before the actual resolution (but after adding both thresholds) the threshold has to be greater than 0" );
	  if(ogrdbg) cerr  << "c initial threshold: " << threshold << endl;
	  
	  assert( scaleGlobal == 1 && "the constraint should not be scaled when being resolved with a clause" );
	  for (int j =0; j < c.size(); j++){ // process all literals of the current reason-constraint
	      const Lit q = c[j];
	      // a clause is a reason only, if all literals have been assigned before
	      // TODO check overflow and re-scale before continuing. Make sure that the resolution still removes a variable. Also check the threshold for overflow
	      const int64_t thisWeight = sign(q) ? scaleConstraint : - scaleConstraint; // for each literal the weight is -1!
	      const int64_t varWeight  = seenWeights[ var( q ) ];                       // scale factor is 1 for a clause!
      
	      if(ogrdbg) cerr  << "c use var " << var(q) + 1 << " with " << thisWeight << " and global weight " << varWeight << endl;
	      assert( value(q) != l_Undef && "in reason clauses all literals are assigned a truth value" );
	      assert( seen[var(q)] == 0 && "the weight should not have been scaled already");
	      
	      if( level(var(q)) == 0 ) { // handle top level literals specially
		assert( seenWeights[ var(q) ] == 0 && "there should not be a top level literal inside the constraint" );
		if(ogrdbg) cerr << "c level 0 variable with value " << value(q) << endl;
		if( value(q) == l_False ) {
		  threshold -= abs64(thisWeight); // substract current weight from threshold, because variable is already fixed (since its a clause, q is falsified)
		}
		if(ogrdbg) cerr << "c new threshold : " << threshold << endl;
		continue;                                          // nothing more to be done with this variable
	      }
	      
	      // update weight for var(q), adapt threshold, handle maxLevel infos
	      updateCurrentPBWithResolveVariable( q, threshold, out_learnt, thisWeight, varWeight, maxLevelLiterals, maxLevelVar, maxLevel );
	  }
	  
	}
	
	// update activity here, because the loop might be re-executed several times due to scaling constraints
	if (c.learnt()) claBumpActivity(c);       // if learned, increase the activity of the constraint

	pbResolves ++; // count that we performed resolution

	/**
	 *  early abort due to unsatisfiable constraint
	 */
	// processed the current reason constraint
	// next, scale the remaining weights, and update the literal vector of literals (out_learnt)
	if( threshold < 0 ) { // the current constraint notices that the current formula is unsatisfiable.
	  if( ogrdbg ) cerr << "c found unsatisfiable constraint during resolution" << endl;
	  for( int i = 0; i < out_learnt.size(); ++ i ){ 
	    const Var v = var(out_learnt[i]);
	    seen[v] = 0; seenWeights[v] = 0;
	  }
	  break;
	}
	
	assert( ld64( abs64(threshold) ) < 61 && "ensure that the precision limit is kept" );
	
	/**
	 *  post-process the current constraint
	 */
	  // scale the constraint
	  if( ogrdbg ) cerr << "c postprocess resolvent with " << out_learnt.size() << " candidate literals" << endl;
	  int keptLiterals = 0, satLits = 0, unsatLits = 0, unitLiterals = 0; // number of kept literals
	  maxLevel = -1, maxLevelLiterals = 0, maxLevelUnsats = 0;            // check for the literal with the highest level
	  globalDiff = 0;
	  presentLevels.clear();                        // store the levels that are present in the current constraint (with satisfied literals)
	  
	  sumWeight = 0;                                                            // sum of all weights
	  maxWeigth = seenWeights[var(out_learnt[0])]; minWeight = maxWeigth;       // max and min of all weights
	  pathC = 0;                                                                // number of literals on the highest level (not higher than index)
	  int compareLevel = (p == lit_Undef) ? decisionLevel() : level( var(p) );  // decision level of the literal that is currently resolved
	  
	  for( int i = 0; i < out_learnt.size(); ++ i ) // scale missing variables, removed weight-0 variables, remove literals that are mapped to false
	  { 
	    //TODO: collect info about downscaling to scale down lazily (e.g. in the next iteration that has to be done anyways, combine the lazy factor with the scale factor of the next round)
	    const Var& v = var( out_learnt[i] );
	    assert( level(v) > 0 && "there should not be top level variables in the learned constraint" );
	    
	    if( seenWeights[v] != 0) {                         // if the variable has a weight, then keep it and update the weight, otherwise the variable is removed lazily
	      bool varIsUnsat = false;
	      out_learnt[keptLiterals++] = out_learnt[i];                                           // keep the positive literal in the constraint
	      if( !seen[v] ) seenWeights[v] = seenWeights[v] * scaleGlobal;                         // scale the weight if not done above

	      assert( ld64( abs64(seenWeights[v]) ) < 61 && "ensure that the precision limit is kept" );

	      // update difference of the constraint
	      const int lv = level(v);
	      if(        value(v) == l_True  && seenWeights[v] > 0 && trailPosition[v] <= index ){ // the variable is assigned before the current resolution literal, and its satisfied
		satLits ++; globalDiff += seenWeights[v];   // add positive weight
		if( ogrdbg ) cerr << "c active variable " << v+1 << " with weight " << seenWeights[v] << " (new globalDiff: " << globalDiff << ")" << endl;
		presentLevels.push( lv );                                                                                // store this level;
		levelSum[ lv ] += seenWeights[v];                                                                        // add the weight to the current level
		levelMaxWeight[ lv ] = levelMaxWeight[ lv ] >= seenWeights[v] ? levelMaxWeight[ lv ] : seenWeights[v];   // store the maximum weight on this level
		assert( globalDiff >= seenWeights[v] && "has to increase with each step" );
		assert( levelMaxWeight[ lv ] > 0 && "the maximum of this level has to be positive" );
	      } else if( value(v) == l_False && seenWeights[v] < 0 && trailPosition[v] <= index ){ // the variable is assigned before the current resolution literal, and its satisfied
		satLits ++; globalDiff -= seenWeights[v];   // substract negative weight (which essentially adds the absolute value)
		if( ogrdbg ) cerr << "c active variable " << v+1 << " with weight " << -seenWeights[v] << " (new globalDiff: " << globalDiff << ")" << endl;
		presentLevels.push( lv );                                                                                      // store this level;
		levelSum[ lv ] -= seenWeights[v];                                                                              // add the weight to the current level		
		levelMaxWeight[ lv ] = levelMaxWeight[ lv ] >= (-seenWeights[v]) ? levelMaxWeight[ lv ] : (-seenWeights[v]);   // store the maximum weight on this level
		assert( globalDiff >= abs64(seenWeights[v]) && "has to increase with each step" );
		assert( levelMaxWeight[ lv ] > 0 && "the maximum of this level has to be positive" );
	      } else { 
		varIsUnsat = true; unsatLits ++;
		if( ogrdbg ) cerr << "c inactive variable " << v+1 << " with weight " << seenWeights[v] << " (globalDiff: " << globalDiff << ")" << endl;
	      } 
	      
	      if( trailPosition[v] + 1 <= index ) { // literals that have been added to the constraint before the resolution literal, to check for clause
		sumWeight += abs64( seenWeights[v] ); // sum of all weights
		minWeight =  abs64( seenWeights[v] ) < minWeight ? abs64( seenWeights[v] ) : minWeight; // minimal weight
		maxWeigth =  abs64( seenWeights[v] ) < maxWeigth ? abs64( seenWeights[v] ) : maxWeigth; // maximal weight
		pathC = (level(v) == compareLevel) ? pathC + 1 : pathC;                                 // found a literal on the current decision level
	      }

	      // look for 1st UIP, backtrack level, and unit literals
	      if( abs64(seenWeights[v]) > threshold ) unitLiterals ++;          // there is a literal that always has to be falsified to satisfy the current constraint
	      else {                                                          // still collect infos about the remaining literals // TODO check whether necessary
		if( !varIsUnsat && level( v ) > maxLevel ) { 
		  maxLevel = level(v); maxLevelLiterals = 1; 
		  maxLevelVar = varIsUnsat ? var_Undef : v; // only set the variable, if the current variable is not falsified. otherwise state there there is no variable yet (var_Undef)
		  maxLevelUnsats = varIsUnsat ? maxLevelUnsats + 1 : maxLevelUnsats; // count number of falsified literals on the highest level
		} // set the new level
		else if ( level(v) == maxLevel )  { 
		  maxLevelLiterals ++;    // increase variables for the current level 
		  if(! varIsUnsat ) maxLevelVar = (maxLevelVar == var_Undef ? v : var_Error); // if there has been a variable, there is a clash now, otherwise set the current variable
		  else ++ maxLevelUnsats;                                                     // count number of falsified literals on the highest level
		}
	      }

	    } else {
	      if( ogrdbg ) cerr << "c variable " << v + 1 << " is dropped, because its weight has been reduced to 0" << endl;
	    }
	    seen[v] = 0; // remember that the weight has been scaled
	  }
	  if(ogrdbg) cerr << "c literals before shrink: " << out_learnt << endl;
	  out_learnt.shrink( out_learnt.size() - keptLiterals ); // remove the literals that have been removed // TODO: stats when more than one literal is removed
	  if(ogrdbg) cerr << "c active sum: " << globalDiff << " and threshold: " << threshold << "  kept literals: " << out_learnt << endl;
	  globalDiff -= threshold;                               // substract the threshold from the difference

	  if(ogrdbg) cerr << "c maxLevelLiterals: " << maxLevelLiterals << " with level " << maxLevel << " and unsats " << maxLevelUnsats << endl;
	  // handle special cases (where the constraint actually would turn into a unit constraint)
	  assert( threshold >= 0 && "the inconsistence case should have been handled above already" ); 
	  assert( (p != lit_Undef || !unitLiterals) && "there should not be unit literals in the initial conflict constraint");
	  
	  /**
	   *  check whether intermediate constraint is a clause
	   */
	  if( oTurnIntermediatePBtoCLS ) {
	    if( sumWeight - minWeight <= threshold ) { // assigning a single literal (the one with the smallest weight) to false satisfies the constraint, hence we have a clause
	      assert( p != lit_Undef && "a PB constraint can only be a clause after at least one resolution step" );
	      turnedIntermediatePBintoCLS ++;          // statistic counter
	      int keptLiterals = 0;                    // to remove all literals from the current literal
	      for( int j = 0 ; j < out_learnt.size(); ++ j ) {
		seen[ var(out_learnt[j]) ] = 1;               // setup seen vector again
		if( level(var(out_learnt[j])) == level( var(p) ) )        // keep the literals
		  out_learnt[keptLiterals++] = out_learnt[j]; // keep literal, because its on another level
	      }
	      out_learnt.push();                                   // have space for dummy element
	      out_learnt[ out_learnt.size() - 1 ] = out_learnt[0]; // have space for dummy element
	      out_learnt[0] = lit_Undef;                           // free first element
	      return usualClause;                                  // tell the analyze method, that learning could be continued
	    }
	  }
	  
	  /**
	   *  handle the special case that unit clauses are entailed
	   */
	  if( p != lit_Undef ) // check for asserting level only when the constraint is not the initial conflict constraint
	  {
	    
	    if( unitLiterals  ) { // turn constraint into a unit only constraint // TODO: could collect unit literals next to usual literals, might be better to collect a larger constraint that includes yet falsified literals?
	      if(ogrdbg) cerr  << "c turned constraint into unit constraint" << endl;
	      assertingLevel = 0; // 
	      int keptLiterals = 0 ;
	      for( int i = 0; i < out_learnt.size(); ++ i ) { // keep only the literals that are unit
		const Var v = var( out_learnt[i] );
		if( abs64(seenWeights[v]) > threshold ) out_learnt[ keptLiterals ++ ] = out_learnt[i];
		else seenWeights[v] = 0;
	      }
	      out_learnt.shrink( out_learnt.size() - keptLiterals ); // remove redundant literals
	      threshold = 0; // turn the current constraint into unit clauses
	    } else {
	      // checks for the default case, there are no units inside the constraint
	      assert( maxLevelLiterals > 0 && "on the highest level there should be a variable that is currently satisfied" );  
	      
	      /**
	      *  postprocess asserting information (check whether the constraint is a UIP constraint)
	      */
	      if(ogrdbg) { cerr << "unsorted levels " << presentLevels.size() << " with values "; for( int j = 0 ; j < presentLevels.size(); ++ j ) cerr << " " << presentLevels[j] << "=" << levelSum[ presentLevels[j]];cerr << endl;}
	      sort( presentLevels ); // sort levels that are present in the constraint
	      int64_t previousLevelSum = 0;
	      for( int j = 0; j < presentLevels.size(); ++ j ) {
		if( j > 0 && presentLevels[j] == presentLevels[j-1] ) continue;   // do not work on the same level twice
		const int64_t lastLevel = levelSum[ presentLevels[j] ];           // temporarily memorize the value of this level
		levelSum[ presentLevels[j] ] = previousLevelSum ;                 // store the weight of the constraint before the current level is reached
		if(ogrdbg) { cerr << "set sum before level " << presentLevels[j] << " to " << levelSum[ presentLevels[j] ] << endl; }
		previousLevelSum += lastLevel;                                    // add the previous value of this level for the next iteration
		assert( previousLevelSum >= levelSum[ presentLevels[j] ] && "if the value got smaller, an overflow occurred" );
	      }
	      if(ogrdbg) { cerr << "sorted levels " << presentLevels.size() << " with level sums: "; for( int j = 0 ; j < presentLevels.size(); ++ j ) cerr << " " << presentLevels[j] << "=" << levelSum[ presentLevels[j]];cerr << endl;}
	      if(ogrdbg) {
		cerr << "c actual constraint (resolved on " << p << " ):";
		for( int j = 0 ; j < out_learnt.size(); ++ j ) {
		  if( 
		    ( (   (value( out_learnt[j] ) == l_True  && seenWeights[ var(out_learnt[j]) ] > 0 ) 
		       || (value( out_learnt[j] ) == l_False && seenWeights[ var(out_learnt[j]) ] < 0 ) 
		    ) && trailPosition[ var(out_learnt[j] ) ] <= index )
		    || var(p) == var(out_learnt[j] )
		  )
		  {
		    cerr << " +"; // print each literal in normal form with weight, level, position and whether its true
		    if ( seenWeights[ var(out_learnt[j]) ] < 0 ) cerr << -seenWeights[ var(out_learnt[j]) ] << " " << ~out_learnt[j] << "@" << level(var(out_learnt[j])) << "|" << trailPosition[ var(out_learnt[j]) ] << "t" << (l_True == value(~out_learnt[j]));
		    else cerr << seenWeights[ var(out_learnt[j]) ] << " " << out_learnt[j] << "@" << level(var(out_learnt[j])) << "|" << trailPosition[ var(out_learnt[j]) ] << "t" << (l_True == value(out_learnt[j]));
		  }
		}
		cerr << "  <= " << threshold << "        current globalDiff: " << globalDiff << " index: " << index << " level(" << p << "): " << level(var(p)) << endl;
		// further debug output
		cerr << "c additionally (inactive) present: ";
		for( int j = 0 ; j < out_learnt.size(); ++ j ) {
		    if( !( 
		      ( (   (value( out_learnt[j] ) == l_True  && seenWeights[ var(out_learnt[j]) ] > 0 ) 
			|| (value( out_learnt[j] ) == l_False && seenWeights[ var(out_learnt[j]) ] < 0 ) 
		      ) && trailPosition[ var(out_learnt[j] ) ] <= index )
		      || var(p) == var(out_learnt[j] ) )
		    )
		    {
		      cerr << " +"; // print each literal in normal form with weight, level, position and whether its true
		      if ( seenWeights[ var(out_learnt[j]) ] < 0 ) cerr << -seenWeights[ var(out_learnt[j]) ] << " " << ~out_learnt[j] << "@" << level(var(out_learnt[j])) << "|" << trailPosition[ var(out_learnt[j]) ] << "t" << (l_True == value(~out_learnt[j]));
		      else cerr << seenWeights[ var(out_learnt[j]) ] << " " << out_learnt[j] << "@" << level(var(out_learnt[j])) << "|" << trailPosition[ var(out_learnt[j]) ] << "t" << (l_True == value(out_learnt[j]));
		    }
		}
		cerr << endl;
	      }
	      assert( previousLevelSum == globalDiff + threshold && "literals on highest level have to result in full sum" );
	      
	      // check whether there is an asserting level
	      assertingLevel = -1;                                                                  // initially, the constraint is not asserting
	      
	      // scan for the asserting level per level
	      int64_t maxAvailableWeight = levelMaxWeight[ presentLevels[ presentLevels.size() - 1] ];  // the maximum weight that is available after backtracking to the currently processed level
	      assert( maxAvailableWeight > 0 && "the weights in the constraint have to be positive, hence, the maximum has to be positive" );
	      for( int j = presentLevels.size() - 1; j >= 0; -- j ) {                               // from highest level to lowest level use the maximum weight that would become available while backtracking
		const int& plj = presentLevels[j];  // level that is currently analyzed
		if( j > 0 && plj == presentLevels[j-1] ) continue;                                  // do not work on the same level twice
		if( j + 1  < presentLevels.size() ){                                                 // update maximal available weight for backtracking
		  maxAvailableWeight = maxAvailableWeight >= levelMaxWeight[ plj ] ? maxAvailableWeight : levelMaxWeight[ plj ];
		  assert( maxAvailableWeight > 0 && "the weights in the constraint have to be positive, hence, the maximum has to be positive" );
		}
		if( levelSum[plj] > threshold ) { 
		  // the new constrant is falsified at this level already -> adopt resolution and continue with the lower variable
		  // there have to be at least two active literals of this level in the constraint
		  if( ogrdbg ) cerr << "c constraint falsified at a level lower than " << plj << " already: previousSum= " << levelSum[plj] << " vs threshold: " << threshold << endl;
		  assert( plj > 0 && "the constraint should not be unsatisfiable here");
		  assert( j > 0   && "there is still a smaller level" );
		  assert( trail_lim.size() > presentLevels[j-1] && "the level we want to jump to has to exist" );
		  if( ogrdbg ) cerr << "c continue resolution at " << trail_lim[ presentLevels[j-1] ] << " (instead of " << index << "), which is the start of level " << presentLevels[j-1] + 1 << endl;
		  index = trail_lim[ presentLevels[j-1] ];
		 // assert( false && "implement when the current learned constraint is falsified at a lower level already" );
		} else {
		  if( levelSum[plj] + maxAvailableWeight  > threshold ) {                              // if on this level the current learned constraint is asserting
		    assertingLevel = plj;                                                             // store this asserting level
		    if( ogrdbg ) cerr << "c asserting at " << assertingLevel << " because previousSum= " << levelSum[plj] << " and maximal following: " << maxAvailableWeight << "   vs threshold: " << threshold << endl;
		  } else {
		    if( ogrdbg ) cerr << "c not level " << plj << " because previousSum= " << levelSum[plj] << " and maximal following: " << maxAvailableWeight << "   vs threshold: " << threshold << endl;
		  }
		}
	      }

	      if(ogrdbg) cerr << "c found asserting level: " << assertingLevel << endl;
	    }
	  } // END if p != lit_Undef
	  // clean up level information independently of current literal!
	  for( int j = 0; j < presentLevels.size(); ++ j ) {
	    levelSum[ presentLevels[j] ] = 0ull;       // clean up level sums again
	    levelMaxWeight[ presentLevels[j] ] = 0ull; // clean up maxWeight per level again
	  }	  

	  
	/**
	 *  debug information
	 */
	if( ogrdbg ) { // display the current two constraints and the scale factors
	  cerr << endl << "c final constraint  " << scaleGlobal << " x " ;
	  for( int j = 0 ; j < out_learnt.size(); ++ j ) 
	    cerr << " +" 
	    << (seenWeights[ var(out_learnt[j]) ] < 0 ? - seenWeights[ var(out_learnt[j]) ] : seenWeights[ var(out_learnt[j]) ])
	    << " " 
	    << (seenWeights[ var(out_learnt[j]) ] < 0 ? ~out_learnt[j] : out_learnt[j] )
	    << " "
	    << "@" << level( var(out_learnt[j]) )
	    << "T" << (seenWeights[ var(out_learnt[j]) ] < 0 ? value(~out_learnt[j]) : value(out_learnt[j]) );
	  cerr << " <= " << threshold << endl;
	  cerr << "c currentWeightSum: " << globalDiff + threshold << " satLits: " << satLits << " unsatLits: " << unsatLits << endl;
	  cerr << "c falsified: " << (globalDiff > 0) << endl;

	  // build an expensive assertion that the obtained constraint is still falsified. satisfied literals should be ok
	  // cerr << "c current trail: " << trail << endl;
	  cerr << "c decisionLevel: " << decisionLevel() << endl;
	  cerr << "c decisions: ";
	  for( int j = 0 ; j < trail_lim.size(); ++ j ) cerr << " @" <<  j + 1 << ":" << trail[ trail_lim[j] ] <<  "[" << trail_lim[j] << "]";
	  cerr << endl;
	}
	assert( globalDiff > 0 && "the obtained constraint has to be an asserting constraint, which is falsified during conflict analysis" );
	  
	/**
	 *  determine next literal to resolve with
	 */
	if(ogrdbg) cerr << "c next literal " << p << " at position " << index << ", assertingLevel=" << assertingLevel << " and threshold= " << threshold << endl;
	if( assertingLevel == -1 && threshold > 0 )       // if the constraint is asserting, or the threshold is <= 0, do not continue analysis
	{ 
	  while (true){
	    const Var nextVar = var(trail[index--]);                       // select next variable, decrease index, so that the variable already points to the next literal in the trail
	    if(  (seenWeights[nextVar] > 0 && value(nextVar) == l_True)    // if the variable is satisfied and has a positive weight,
	      || (seenWeights[nextVar] < 0 && value(nextVar) == l_False)   // or the variable is falsified and has a negative weight,
	    ) break;                                                       // use the variable for resolution next
	  }
	  p = trail[index+1];                                                // select literal to be resolved with next
	  confl = reason(var(p));                                            // select next reason constraint
	  if(ogrdbg) cerr << "c new literal " << p << " at position " << index << " with reason " << ca[confl] << endl;
	}
	if(ogrdbg) cerr  << "c next literal to be selected: " << p << endl << "c max level lits: " << maxLevelLiterals << endl; 

    // continue resolution, until:
    //   - its a first UIP constraint (one conflicting literal at the highest decision level)
    //   - the constraint is not satisfiable

  } 
  while ( assertingLevel == -1 && threshold > 0 ); // continue resolution, if we do not have a UIP, and no unit literals or an unsatisfiable constraint
  
  /**
   * construct the PB constraint for the calling function
   */
  out_weights.clear(); 
  if( threshold < 0 ) {                                   // such a constraint can never be satisfied, hence return the according type
    return emptyClause;                                   // no need to do clean up, just indicate unsatisfiability
  } else if ( threshold == 0 ) {                          // if the threshold is 0, no care has to be taken for the weights because we have unit clauses
    for( int i = 0 ; i < out_learnt.size(); ++ i ){
      if( seenWeights[ var(out_learnt[i]) ] < 0 ) out_learnt[i] = ~out_learnt[i]; // flip literals with negative weight
      out_weights.push( 1 );                                                      // have a pseudo weight
      seenWeights[ var(out_learnt[i]) ] = 0;                                      // clean up the weights
    }
    out_btlevel = 0;                                                              // always backtrack to level 0 with unit literals
    return pbConstraint;                                                          // tell calling method that the returned type is a PB constraint
  }
  assert( (out_learnt.size() > 0 || threshold < 0 ) && "an empty PB constraint can only be learned if the threshold is negative (empty clause)" );
  
  /**
   *  construct the output constraint, find backtracking level
   */
  out_btlevel = 0;            // backjumping level is determined while looping over the constraint
  out_threshold = threshold;  // threshold is already fixed
  assert( threshold > 0 && "the two other special cases are handled above already" );
  // from the current global PB constraint construct the vectors for the constraint
  Lit maxLit = lit_Undef;
  for( int i = 0 ; i < out_learnt.size(); ++ i ) {
    // rewrite inner representation into the two vectors in normal form (positive weights, arbitrary literals)
    const int64_t thisWeight = seenWeights[ var(out_learnt[i]) ];    // copy the weight
    seenWeights[var(out_learnt[i])] = 0;                             // clean the weights of the internal representation
    int64_t finalWeight = 0;
    if( thisWeight < 0 ) {                  // if negative weight,
      out_learnt[i] = ~out_learnt[i];       // then flip the polarity
      finalWeight = -thisWeight;            // and negate the weight
    } else {
      finalWeight = thisWeight;             // otherwise just use the weight
    }
    // reason about weights to identify the type of the constraint
    assert( finalWeight > 0 && "the output constraint can contain only positive weights" );
    out_weights.push( finalWeight );        // add the weight to the constraint

    if( value(out_learnt[i]) == l_True ) { 
      assignedSum += finalWeight;
      const int vl = level( var(out_learnt[i]) );
      if( vl < assertingLevel ) out_btlevel = out_btlevel >= vl ? out_btlevel : vl; // the backtracking level is the maximum level of a satisfied literal, but which is smaller than the asserting level
    }
    
    // stats
    minWeight = (minWeight == -1 ? finalWeight : (finalWeight < minWeight ? finalWeight : minWeight ) );
    maxWeigth = (finalWeight > maxWeigth ? finalWeight : maxWeigth );
    sumWeight += finalWeight;
    // cumulate sum and look for backjumping level
    if( value(out_learnt[i]) == l_True ) { 
      assignedSum += finalWeight;
    }
  }
  if(ogrdbg) cerr  << "c jump back to level " << out_btlevel << endl;
  assert( assertingLevel >= 0 && "should not jump above top level" );
  
  
  /**
   * by default output type PB constraint. However, some PB constraints might be easily turned into clauses again. 
   * TODO if constraint can be turned into a single clause, do it! (full sum minus any of the weights is less equal than the threshold)
   * In this case, even clause minimization should be executed again!
   */
  if( oRecreateCls && sumWeight - minWeight <= threshold ) {
    // assert( false && "convert learnt PB constraint back into a clause" );
    if(ogrdbg) cerr  << "c convert learnt constraint back into a clause! " << out_weights << " <= " << threshold << endl;
    
    int assertingPos = 0; // asserting literal
    for( int j = 0 ; j < out_learnt.size(); ++ j ) {
      assertingPos = ( level(var(out_learnt[assertingPos])) > level(var(out_learnt[j])) ) ? assertingPos : j;
      seen[var(out_learnt[j])] = 1;   // enable seen flags again
      out_learnt[j] = ~out_learnt[j]; // invert all literals for a clause
    }
    // swap asserting lit to first position
    const Lit tmpLit = out_learnt[0]; out_learnt[0] = out_learnt[assertingPos]; out_learnt[assertingPos] = tmpLit;
    
    // set number of literals on highest level, and set current resolve literal right (asserting literal)
    p = out_learnt[0]; // the asserting literal is the literal in the first position
    pathC = 1;         // we have only one literal remaining in the first position
    turnedLearnedPBintoCLS ++;
    return usualClause;
  }
  
  // TODO: in general try to merge loops that are running over the global constraint
  return pbConstraint; // return that the current learned constraint is a PB constraint
}



/** update the weight of literal q during resolving the current conflict PB constraint with another constraint/clause
 * @param q literal, whose weight has to be updates
 * @param threhold threshold of the current constraint
 * @param out_learnt literals in the current/next conflict constraint
 * @param thisWeight weight of the variable var(q) in the constraint to resolve with
 * @param varWeight weight of the variable var(q) in the current conflict constraint
 * @param maxLevelLiterals number of literals in the highest decision level of the constraint
 * @param maxLevelVar variable on the maximum decision level (var_Undef, if none so far, or if more than one)
 * @param maxLevel maximum decision level in the constraint
 */
void Solver::updateCurrentPBWithResolveVariable( const Lit q, int64_t& threshold, vec<Lit>& out_learnt, const int64_t thisWeight, const int64_t varWeight, int& maxLevelLiterals, Var& maxLevelVar, int& maxLevel )
{
  assert( seen[var(q)] == 0 && "the weight should not have been scaled already");
  seen[ var(q) ] = 1; // remember that this variable has been scaled in this round
  if( varWeight == 0 ) { // variable not yet in the constraint, hence add the variable and its weight
    seenWeights[ var( q ) ] = thisWeight;   // set the scaled weight (varWeight == 0 )
    out_learnt .push( mkLit( var(q),false ) );  // add the positive literal
    varBumpActivity(var(q)); // TODO take care that a variable is not bumped twice, but that all variables are scaled everywhere
    if(ogrdbg) cerr  << "c add variable " << var(q) + 1 << " with weight " << thisWeight << " to new set of literals" << endl;
  } else { // the variable is already present
    if ( (varWeight < 0 && thisWeight < 0) || (varWeight > 0 && thisWeight > 0) ) { // simply increase the value
      if(ogrdbg) cerr  << "c varWeight: " << varWeight << " thisWeight " << thisWeight << endl;
      seenWeights[ var( q ) ] =  varWeight + thisWeight; // addition takes care of the sign, nothing happens to the threshold
    } else if( varWeight > 0 && thisWeight < 0 ) {
      if(ogrdbg) cerr  << "c varWeight: " << varWeight << " thisWeight " << thisWeight << endl;
      const int64_t weightDiff = (varWeight + thisWeight);                             // the diff between the two values
      if( varWeight + thisWeight == 0 ) {                                              // update the threshold
	threshold += thisWeight;                                                       // add the negative value from the threshold
      } else 
	threshold = weightDiff < 0 ? threshold - varWeight : threshold + thisWeight;  // substract the common (absolute) value from the treshold
      if(ogrdbg) cerr  << "c new threshold = " << threshold << endl;
      seenWeights[ var( q ) ] =  varWeight + thisWeight;
      // addition takes care of the sign
    } else { // the weights are have different signs or the weights are equal
      if(ogrdbg) cerr  << "c varWeight: " << varWeight << " thisWeight " << thisWeight << endl;
      // only one case left
      assert( varWeight < 0 && thisWeight > 0 && "all cases should have been covered" );
      const int64_t weightDiff = (thisWeight + varWeight);                             // the diff between the two values
      if( varWeight + thisWeight == 0 )                                                // update the threshold
	threshold += varWeight;                                                        // add the negative value from the threshold
      else
	threshold = weightDiff < 0 ? threshold - thisWeight : threshold + varWeight;  // substract the diff from the treshold
      seenWeights[ var( q ) ] =  varWeight + thisWeight;                               // addition takes care of the sign
    }
    if( seenWeights[ var(q) ] != 0 ) {                                                    // trace variables that stayed inside the constraint
      if( level( var(q) ) > maxLevel ) { maxLevel = level(var(q)); maxLevelLiterals = 1; maxLevelVar = var(q); } // set the new level
      else if ( level(var(q)) == maxLevel ) { maxLevelLiterals ++; maxLevelVar = var_Undef; }                    // increase variables for the current level
    }

    if(ogrdbg) cerr  << "c new weight: " << seenWeights[ var( q ) ] << " new threshold: " << threshold << endl;
  }
}