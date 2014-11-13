/******************************************************************************************[Math.h]
Copyright (c) 2014-2006, Norbert Manthey

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Math_h
#define Minisat_Math_h


/** return the log2 of an unsigned 64bit integer
 *  is calculated with an assembler instruction
 */
inline const int ld64 (const uint64_t x){
  return (sizeof(uint64_t) << 3) - __builtin_clzll (x); // build in assembler instruction to return the most significant bit of the integer (as to be non-zero)
}

/** return the absolute value of an 64bit integer
 */
inline int64_t abs64( const int64_t& value )
{
  return value >= 0 ? value : -value;
}


/** eucledian greatest common divisor algorithm (iterative version)
 */
inline const int64_t gcd(int64_t a, int64_t b) {
  if( b > a ) { int64_t t = b; b = a; a = b;} // avoid the first iteration and division, if possible
  while (b != 0)  {
    int64_t t = b;
    b = a % b;
    a = t;
  }
  return a;
}

#endif