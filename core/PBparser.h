/**************************************************************************************[PBparser.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson
Copyright (c) 2014, Norbert Manthey

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

#ifndef Minisat_PBparser_h
#define Minisat_PBparser_h

#include <stdio.h>

#include "utils/ParseUtils.h"
#include "utils/Math.h"
#include "core/SolverTypes.h"

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template<class B, class Solver>
static void readConstraint(B& in, Solver& S, vec<Lit>& lits, vec<int64_t>& weights, int64_t& degree, bool minimization = false) {
    int64_t parsed_weight, old_degree, weightSum = 0;
    int parsed_lit,  var;
    bool negated = false, lessEqual;
    lits.clear();
    weights.clear();
    degree = 0;                                 // be prepared to negate literals based on negative weights
    for (;;){
	std::cerr << "c continue with " << (char) *in << std::endl;
	skipWhitespace(in);                     // skip white spaces
        if( *in == '>' || *in == '<' ) {        // handle comparison
	  lessEqual = (*in == '<');             // check type of constraint
	  ++in;
	  assert( *in == '=' && "the other symbol has to be an equal sign" );
	  ++in;
	  
	  skipWhitespace(in);
	  std::cerr << "c parse degree starting with " << (char) *in << std::endl;
	  
	  old_degree = degree;
	  parsed_weight = parseInt64(in);       // parse the degree 
	  degree += parsed_weight;              // and add the value to whatever we already collected during negating weights
	  if( (parsed_weight > 0 && degree < old_degree)   // check for overflow 
	    ||(parsed_weight < 0 && degree > old_degree)){ // in the two possible directions
	    fprintf(stderr, "PARSE ERROR (6)! Parsed too large integer\n");
	    exit(3);                            // make sure we stay in 64 bits!
	  }
	  
	  skipWhitespace(in);                   // reach end of the line
	  if( *in != ';' ) printf("PARSE ERROR (2)! Unexpected char: %c  expected ';' \n", *in), exit(3);
	  ++in; 
	  
	  // normalize constraint (less equal), positive weights have een ensured before already
	  if(!lessEqual) {
	    for( int i = 0 ; i < lits.size(); ++i ) lits[i] = ~lits[i]; // negate all literals
	    assert( weightSum >= 0 && "the sum of weights cannot be negative, since only positive weights have been added" );
	    degree = (degree > weightSum) ? -1 : (weightSum - degree);    // is the constraint unsatisfiable already? handles overflow nicely
	    std::cerr << "c was less equal, new degree: " << degree << std::endl;
	  }
	  
	  break;
	}

	// we found the terminating symbol for the minimization constraint, and we do not have to parse a degree
	if( minimization && *in == ';' ) {
	  ++in;
	  break;
	}
	
	// another weight literal pair
	
        parsed_weight = parseInt64(in);  // skip whitespace, considers negation

	skipWhitespace(in);              // skip white spaces
	negated = false;
	if( *in == '~' ) { negated = true; ++in; } // negation in PB files uses '~' instead of '-'
	while( (*in >= 'a' && *in <= 'z') 
	    || (*in >= 'A' && *in <= 'Z') 
	    || *in == '_' ) ++in;                  // skip the humand readable variable name
	parsed_lit = parseInt(in);                 // read the literal
	
	std::cerr << "c parsed pair " << parsed_weight << " " << parsed_lit << std::endl;
	
	if( parsed_weight != 0 ) {
	  var = abs(parsed_lit)-1;
	  while (var >= S.nVars()) S.newVar(); // get enough variables in the solver
	  if( parsed_weight < 0 ) {            // handle negative weights
	    negated = !negated;                // negate the literal
	    parsed_weight = -parsed_weight;    // negate the weight (so that it is positive now)
	    old_degree = degree;
	    degree += parsed_weight;           // add the weight to the degree
	    if( old_degree > degree ) {
	      fprintf(stderr, "PARSE ERROR (6)! Parsed too large integer\n");
	      exit(3);                            // make sure we stay in 64 bits!
	    }
	  }
	  lits.push( mkLit(var, negated) );
	  weights.push( parsed_weight );
	  old_degree = weightSum;
	  weightSum += parsed_weight ;
	  
	  if( old_degree > weightSum ) {    // handle overflow
	    fprintf(stderr, "PARSE ERROR (7)! Too large integer during normalizing constraint\n");
	    exit(3);  
	  }
	}
    }
}

template<class B, class Solver>
static bool parse_PBfile_main(B& in, Solver& S, vec<Lit>& minimizeLits, vec<int64_t>& minimizeWeights) {
    vec<Lit> lits; vec<int64_t> weights; int64_t degree;
    bool foundMinimization = false;
    int vars    = 0;
    int clauses = 0;
    int cnt     = 0;
    for (;;){
        skipWhitespace(in);                      // skip white spaces
	std::cerr << "c proceed with " << (char)*in << std::endl;
        if (*in == EOF) break;                   // reached end of file
        else if (*in == '*'){                    // skip comments
            if (eagerMatch(in, "* #variable= ")){ // parse number of variables
                vars    = parseInt(in);
		std::cerr << "c found header: v=" << vars << std::endl;
	    }
	    if (eagerMatch(in," #constraint= ")) { // parse number of constraints
                clauses = parseInt(in);
		std::cerr << "c found header: c=" << clauses << std::endl;
	    }
	    skipLine(in);                         // skip remainder of the line
        } else if (*in == 'm') {                  // minimization function
	    if (eagerMatch(in,"min: ")) {
	      readConstraint(in, S, minimizeLits, minimizeWeights, degree, true); // parse the actual constraint
	      std::cerr << "found minimization function with lits: " << minimizeLits << " and weights: " << minimizeWeights << std::endl;
// 	      skipLine(in);
	    } else {
	      printf("PARSE ERROR! Unexpected char: %c\n", *in);
	      while( *in != '\n' && *in != EOF ) { std::cerr << (char)*in; ++in ; }
	      std::cerr << std::endl;
	      
	      exit(3);
	    }
            
	} else if (*in == '*') {                  // skip comments
            skipLine(in);
	} else {                                  // read the constraint
	    std::cerr << "c parseConstraint " << (char)*in << std::endl;
            cnt++;
            readConstraint(in, S, lits, weights, degree); // parse the actual constraint
            S.addLEConstraint_(lits,weights,degree);      // add the constraint to the solver
	}
    }
    if (vars != S.nVars())
        fprintf(stderr, "WARNING! PB header mismatch: wrong number of variables.\n");
    if (cnt  != clauses)
        fprintf(stderr, "WARNING! PB header mismatch: wrong number of constraints.\n");
    
    // tell the calling function whether there has been a minimization constraint
    return foundMinimization;
}

/** Inserts problem into PB solver.
 *
 * might return a minimization function
 * @return true, if a minimization function has been found
 **/
template<class Solver>
static inline bool parse_PBfile(gzFile input_stream, Solver& S, vec<Lit>& minimizeLits, vec<int64_t>& minimizeWeights) {
    StreamBuffer in(input_stream);
    parse_PBfile_main(in, S, minimizeLits, minimizeWeights); }

//=================================================================================================
}

#endif
