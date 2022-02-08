/*
 * compile with gcc/g++ with commands:  -O3 -mpc64 -march=native
 */

#include <array>
#include <bitset>
#include <cstdint>


template<int LOG_D=5>
class aaaSum
{
public:  // public functions for using main functionality

    aaaSum() { reset(); }
    ~aaaSum() { }
    
    // adds all entries of input array into accumulator
    void AddArray( double *input, int n );
    
    // return a faithfully rounded approximation of the real number represented by the accumulator
    double IntermediateSum( void );
    
    // re-initialize accumulator entries
    void reset( void );
    
    // accumulates the entries of input array and returns a faithfully rounded approximation of the sum
    double Sum( double *input, int n );
    
    // indicates writing into overflow buckets
    // have to be set 'true' before summation to check status (not reset by class)
    bool isFaithful = false;

public:
    static_assert( ( LOG_D >= 1 ) && ( LOG_D <= 5 ));
    
    static constexpr int d() { return ( 1 << LOG_D ); }
    static constexpr int n_buckets() { return ( 1 << ( 11 - LOG_D ) ); }
    static constexpr int precision() { return std::numeric_limits<double>::digits; }
    static constexpr int eta() { return ( ( precision() + d() - 2 ) / 2 ); }
    static constexpr int ell() { return ( std::numeric_limits<double>::max_exponent - std::numeric_limits<double>::min_exponent + 1 - precision() + eta() ) / d() - 1; }
    static constexpr int kmax2() { return ( 2 << std::min(precision() - eta() - 1, eta() - d() + 1 ) ); }
    
    // for problem dimension n <= n_flagging_switch() accumulator flagging is applied (only for LOG_D=5)
    static constexpr int n_flagging_switch() { return 160; }
    
private:
    // union for applying bit operations on 
    union uint64double
    {
        double dval;
        uint64_t bm64;
    };
    // a structure for IEEE754 double precision
    struct st_aaasum_double
    {
        unsigned int m_low : 32;
        unsigned int m_high : 20;
        unsigned int exp_low : LOG_D;
        unsigned int exp_high : ( 11 - LOG_D );
        unsigned int sign : 1;
    };
    
    // initialization constants
    static constexpr std::uint64_t exp_diff()
    {
        uint64double entry0, entry1;
        entry0.dval = 1.L;
        entry1.dval = 2.L;
        return ( entry1.bm64 - entry0.bm64 );
    }
    static constexpr std::uint64_t mask_zero()
    {
        uint64double umask;
        umask.dval = .75 * static_cast<double>( 1LL << ( precision() - eta() + d() ) ) * std::numeric_limits<double>::min();
        return umask.bm64;
    }
    
    // initialization entry for bucket i
    inline double mask_entry( std::uint64_t i )
    {
        uint64double entry;
        entry.bm64 = i * ( d() * exp_diff() ) + mask_zero();
        return entry.dval;
    }
    
    inline double acc_thresh_entry( std::uint64_t i )
    {
        uint64double entry;
        entry.bm64 = i * ( d() * exp_diff() ) + ( mask_zero() + exp_diff() * 2 * precision() );
        return entry.dval;
    }

    static constexpr int acc_thresh_max_index() { return ( std::numeric_limits<double>::max_exponent - std::numeric_limits<double>::min_exponent + 1 - 3 * precision() + eta() ) / d() - 1; }

    
private:
    // summation variable
    double _s;
    // number of addends till next tidy-call
    int _nt;
    // flag for reinitialization
    int _re_init;

    // accumulators
    std::array<double, n_buckets()> a1, a2, e1, e2;
    // position flags for modified accumulator entries
    std::bitset<n_buckets()> pflags, pflags2;
    
    // tidy up accumulation array
    void tidy( void );
    
    // implements a special version of shift-32 summation,
    // designed for vectors of small dimension
    double sumSmallVec( double *input, int n );

};


////
/// re-initialize buckets
////
template<int LOG_D>
inline void aaaSum<LOG_D>::reset( void )
{
    // reset status variables
    _s = .0;
    _nt = kmax2();
    _re_init = 0;

    // re-initialize bucket entries
    for (std::uint64_t i = 0; i < n_buckets(); i++)
        a1[ i ] = mask_entry( i );
    for (std::uint64_t i = 0; i < n_buckets(); i++)
        a2[ i ] = mask_entry( i );
    e1.fill( .0L );
    e2.fill( .0L );
}


////
// special version of shift32 summation algorithm, designed for small vectors
////
template<int LOG_D>
inline double aaaSum<LOG_D>::sumSmallVec( double *input, int n )
{
    // reset position flags for 'modified' accumulator buckets
    pflags.reset();
    pflags2.reset();
    
    // treat first addend in case of odd number of addends
    if ( n & 1 )
    {
        // extract exponent from floating-point number
        unsigned int pos1 = ( reinterpret_cast<st_aaasum_double&>( input[ 0 ] ) ).exp_high;
        // using error-free transformation to sum value into a1, e1
        double t1 = a1[ pos1 ] + input[ 0 ];
        e1[ pos1 ] += ( a1[ pos1 ] - t1 ) + input[ 0 ];
        a1[ pos1 ] = t1;
        // set position flag
        pflags.set( pos1 );
        // update input pointer and number of addends
        input++;
        n--;
        _nt -= 2;
    }
    
    // fast loop over even numbers of addends -> add into 2 accumulators
    for ( int i = 0; i < n; i += 2 )
    {
        // extract exponents from floating-point numbers
        unsigned int pos1 = ( reinterpret_cast<st_aaasum_double&>( input[ i ] ) ).exp_high;
        unsigned int pos2 = ( reinterpret_cast<st_aaasum_double&>( input[ i + 1 ] ) ).exp_high;
        // using error-free transformation to sum input data into _ax, _ex
        double t1 = a1[ pos1 ] + input[ i ];
        double t2 = a2[ pos2 ] - input[ i + 1 ];
        e1[ pos1 ] += ( a1[ pos1 ] - t1 ) + input[ i ];
        e2[ pos2 ] += ( a2[ pos2 ] - t2 ) - input[ i + 1 ];
        a1[ pos1 ] = t1;
        a2[ pos2 ] = t2;
        // set position flags
        pflags.set( pos1 );
        pflags2.set( pos2 );
    }
    
    // posflags contains all position flags 
    pflags |= pflags2;
  
    // local sum variable
    long double s = .0;
    
    // first/next position to check
    int pos = n_buckets();

    // check overflow
    if ( pflags.test( n_buckets() - 1 ) )
    {
        isFaithful = false;
        pflags <<= 1;
        pos--;
    }
    
    while ( pflags.any() )
    {
        // find next bucket position, encoded in posflags
        int shift = __builtin_clzl( pflags.to_ulong() ) + 1;
        pos -= shift;
        pflags <<= shift;
        // add entries of buckets
        s += ( a1[ pos ] - a2[ pos ] );
        // reset _a buckets
        double mask_pos = mask_entry( pos );
        a1[ pos ] = mask_pos;
        a2[ pos ] = mask_pos;
        // loop through row of 'filled' buckets
        while ( pflags.test( n_buckets() - 1 ) )
        {
            // update flags for next position
            pflags <<= 1;
            // add accumulator entries
            s += ( a1[ pos - 1 ] - a2[ pos - 1 ] );
            // reset corresponding buckets
            double mask_pos1 = mask_entry( pos - 1 );
            a1[ pos - 1 ] = mask_pos1;
            a2[ pos - 1 ] = mask_pos1;
            // add error fields
            s += ( e1[ pos ] - e2[ pos ] );
            // and reset the corresponding entries
            e1[ pos ] = .0L;
            e2[ pos ] = .0L;
            // next position in row
            pos--;
        }
        // add & reset error buckets at the end of the row
        s += ( e1[ pos ] - e2[ pos ] );
        e1[ pos ] = .0L;
        e2[ pos ] = .0L;
    }

    return static_cast<double>( s );
}


////
// tidy up accumulation array
////
template<int LOG_D>
inline void aaaSum<LOG_D>::tidy( void )
{
    // add content of signifcant buckets to sum _s
    double c_ell = a1[ ell() ] - a2[ ell() ];
    _s += c_ell;
    if ( ( isFaithful == true ) &&
         ( ( std::abs( c_ell ) > mask_entry( ell() ) ) ||
           ( std::abs( _s ) > mask_entry( ell() ) ) ) )
        isFaithful = false;

    // condense entries to a1 and e1
    for ( std::uint64_t i = ell(); i > 0; i-- )
    {
        double mask_i = mask_entry( i );
        double t1 = e1[ i ] - e2[ i ];
        double t2 = a1[ i - 1 ] - a2[ i - 1 ];
        a1[ i ] = mask_i + t2;
        a2[ i ] = mask_i - t1;
        e1[ i ] = ( mask_i - a1[ i ] ) + t2;
        e2[ i ] = ( mask_i - a2[ i ] ) - t1;
    }
    // treat underflow error
    double mask_0 = mask_entry( 0 );
    double t = e1[ 0 ] - e2[ 0 ];
    a1[ 0 ] = mask_0 + t;
    a2[ 0 ] = mask_0;
    e1[ 0 ] = ( mask_0 - a1[ 0 ] ) + t;
    e2[ 0 ] = .0L;
    
    // number of addends till next tidy-up
    _nt = kmax2() - 2;
    if ( eta() >= 2 * d() )
        _nt -= 2 * ( kmax2() >> d() );
}


////
// add entries of input into accumulator
////
template<int LOG_D>
void aaaSum<LOG_D>::AddArray( double *input, int n )
{  
    // are there any entries to add
    if ( n < 1 )
        return;

    // there is something to re-initialize
    _re_init = 1;

    // treat first addend in case of odd number of addends
    if ( n & 1 )
    {
        // extract exponent from floating-point number
        unsigned int pos1 = ( reinterpret_cast<st_aaasum_double&>( input[ 0 ] ) ).exp_high;
        // using error-free transformation to sum value into a1, e1
        double t1 = a1[ pos1 ] + input[ 0 ];
        e1[ pos1 ] += ( a1[ pos1 ] - t1 ) + input[ 0 ];
        a1[ pos1 ] = t1;
        // update input pointer and number of addends
        input++;
        n--;
        _nt -= 2;
    }

    // main loop for accumulation
    while ( 1 )
    {
        // number of addend till end of input array or next tidy-up
        int num = n > _nt ? _nt : n;

        // fast loop over even numbers of addends -> add into 2 accumulators
        for ( int i = 0; i < num; i += 2 )
        {
            // extract exponents from floating-point numbers
            unsigned int pos1 = ( reinterpret_cast<st_aaasum_double&>( input[ i ] ) ).exp_high;
            unsigned int pos2 = ( reinterpret_cast<st_aaasum_double&>( input[ i + 1 ] ) ).exp_high;
            // using error-free transformation to sum input data into _ax, _ex
            double t1 = a1[ pos1 ] + input[ i ];
            double t2 = a2[ pos2 ] - input[ i + 1 ];
            e1[ pos1 ] += ( a1[ pos1 ] - t1 ) + input[ i ];
            e2[ pos2 ] += ( a2[ pos2 ] - t2 ) - input[ i + 1 ];
            a1[ pos1 ] = t1;
            a2[ pos2 ] = t2;
        }
        
        // leave loop if no input entries left
        if ( num == n )
            break;
        
        // update input position and number of remaining addends
        input += num;
        n -= num;

        // tidy up accumulation array
        tidy();
    }

    // number of addends that can be accumulated till next tidy-up
    _nt -= n;
}


////
// calculate intermediate sum of addends already in accumulator
////
template<int LOG_D>
double aaaSum<LOG_D>::IntermediateSum( void )
{
    constexpr int m = 1 + ( precision() - eta() - 2 ) / d();
    
    if ( isFaithful == true )
    {
        for ( int i = ell() + 1; i < n_buckets(); i++ )
            isFaithful = ( isFaithful && ( a1[ i ] == mask_entry( i ) ) );
        for ( int i = ell() + 1; i < n_buckets(); i++)
            isFaithful = ( isFaithful && ( a2[ i ] == mask_entry( i ) ) );
    }
    
    // search for first non-zero entry
    int start = ell();
    while ( ( a1[ start ] == a2[ start ] ) && ( start >~ 0 ) )
        --start;
    int itemp = ell();
    while ( ( e1[ itemp ] == e2[ itemp ] ) && ( itemp >~ start + m ) )
        --itemp;
    start = std::max( start, itemp - m );
    
    // local sum variable
    long double s = _s;
    
    // sum-up of accumulator entries
    int i = start;
    
    while ( ( i >= 0 ) && ( ( std::abs( s ) < acc_thresh_entry( i ) ) || ( i > acc_thresh_max_index() ) ) )
    {
        s += ( a1[ i ] - a2[ i ] );
        s += ( e1[ i + m ] - e2[ i + m ]);
        --i;
    }
    for ( int j = i + m; j > i; j-- )
        s += ( e1[ j ] - e2[ j ] );

    return static_cast<double>( s );
}

////
// compute sum of values in input array
////
template<int LOG_D>
double aaaSum<LOG_D>::Sum( double *input, int n )
{  
    // no addends
    if ( n < 1 )
        return .0;

    // re-initialize accumulator array
    if ( _re_init )
        reset();

    // special treatment of small input vectors
    if ( ( LOG_D == 5 ) && ( n < n_flagging_switch() ) )
        return sumSmallVec( input, n );

    // add new addend to accumulator
    AddArray( input, n );

    // compute accumulator sum
    double s = IntermediateSum();
  
    // reinitialize summation-buckets before returning sum
    reset();

    return s;
}

