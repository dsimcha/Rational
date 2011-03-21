/**
This module contains an implementation of rational numbers that is templated
on the underlying integer type.  It can be used with either builtin fixed
width integers or arbitrary precision integers.  All relevant operators are
overloaded for both rational-rational and rational-integer operations.

Synopsis:
---
// Compute pi using the generalized continued fraction approximation.
import std.bigint;

enum maxTerm = 30;

Rational!(BigInt) getTerm(int termNumber) {
    auto addFactor = 2 * termNumber - 1;

    if(termNumber == maxTerm) {
        return rational(BigInt(addFactor));
    }

    auto termNumberSquared = BigInt(termNumber * termNumber);
    auto continued = termNumberSquared / getTerm(termNumber + 1);

    continued += addFactor;
    return continued;
}

void main() {

    auto pi = rational(BigInt(4)) / getTerm(1);

    // Display the result in rational form.
    writeln(pi);

    // Display the decimal equivalent, which is accurate to 18 decimal places.
    writefln("%.18f", cast(real) pi);
}
---


Author:  David Simcha
Copyright:  Copyright (c) 2009-2011, David Simcha.
License:    $(WEB boost.org/LICENSE_1_0.txt, Boost License 1.0)
 */
module std.rational;

import std.algorithm, std.stdio, std.bigint, std.conv, std.math, std.exception,
       std.conv, std.traits;

alias std.math.abs abs;  // Allow cross-module overloading.

/**
Checks whether $(D T) is structurally an integer, i.e. whether it supports
all of the operations an integer type should support.  Does not check the
nominal type of $(D T).  In particular, the following must compile:

---
T num;
num = 2;
num <<= 1;
num >>= 1;
num += num;
num *= num;
num /= num;
num -= num;
num %= 2;
num %= num;
bool foo = num < 2;
bool bar = num == 2;
---

All builtin D integers and $(D std.bigint.BigInt) are integer-like by this
definition.
*/
template isIntegerLike(T) {
    enum bool isIntegerLike = is(typeof({
        T num;
        num = 2;
        num <<= 1;
        num >>= 1;
        num += num;
        num *= num;
        num /= num;
        num -= num;
        num %= 2;
        num %= num;
        bool foo = num < 2;
        bool bar = num == 2;

        return num;
    }));
}

unittest {
    static assert(isIntegerLike!BigInt);
    static assert(isIntegerLike!int);
    static assert(isIntegerLike!byte);
    static assert(!isIntegerLike!real);
}

private template isRational(T) {
    enum bool isRational =
        is(typeof(T.init.denom)) && is(typeof(T.init.num));
}

private template CommonRational(R1, R2) {
    static if(isRational!R1) {
        alias CommonRational!(typeof(R1.num), R2) CommonRational;
    } else static if(isRational!R2) {
        alias CommonRational!(R1, typeof(R2.num)) CommonRational;
    } else static if(is(CommonInteger!(R1, R2))) {
        alias Rational!(CommonInteger!(R1, R2)) CommonRational;
    }
}

/**
Returns $(D true) iff a value of type $(D U) can be assigned to a variable of
type $(D T).

Examples:
---
static assert(isAssignable!(long, int));
static assert(!isAssignable!(int, long));
static assert(isAssignable!(const(char)[], string));
static assert(!isAssignable!(string, char[]));
---
*/
template isAssignable(T, U) {
    enum bool isAssignable = is(typeof({
        T t;
        U u;
        t = u;
        return t;
    }));
}

unittest {
    static assert(isAssignable!(long, int));
    static assert(!isAssignable!(int, long));
    static assert(isAssignable!(const(char)[], string));
    static assert(!isAssignable!(string, char[]));
}

/**
Returns a common integral type between $(D I1) and $(D I2).  This is defined
as the type returned by I1.init * I2.init.
 */
template CommonInteger(I1, I2) if(isIntegerLike!I1 && isIntegerLike!I2) {
    alias typeof(I1.init * I2.init) CommonInteger;
}

unittest {
    static assert(is(CommonInteger!(BigInt, int) == BigInt));
    static assert(is(CommonInteger!(byte, int) == int));
}

/**
Implements rational numbers on top of whatever integer type is specified
by the user.  The integer type used may be any type that behaves as an integer.
Specifically, $(D isIntegerLike) must return true, the integer type must
have value semantics, and the semantics of all integer operations must follow
the normal rules of integer arithmetic.

Examples:
---
auto r1 = rational( BigInt("314159265"), BigInt("27182818"));
auto r2 = rational( BigInt("8675309"), BigInt("362436"));
r1 += r2;
assert(r1 == rational( BigInt("174840986505151"),
    BigInt("4926015912324")));

// Print result.  Prints:
// "174840986505151 / 4926015912324"
writeln(f1);

// Print result in decimal form.  Prints:
// "35.4934"
writeln(cast(real) result);
---
 */
Rational!(CommonInteger!(I1, I2)) rational(I1, I2)(I1 i1, I2 i2)
if(isIntegerLike!I1 && isIntegerLike!I2) {
    static if(is(typeof(typeof(return)(i1, i2)))) {
        // Avoid initializing and then reassigning.
        auto ret = typeof(return)(i1, i2);
    } else {
        // Don't want to use void initialization b/c BigInts probably use
        // assignment operator, copy c'tor, etc.
        typeof(return) ret;
        ret.numerator = i1;
        ret.denominator = i2;
    }
    ret.simplify();
    return ret;
}

/**Overload for creating a rational that initially has an integer value.*/
Rational!(I) rational(I)(I val)
if(isIntegerLike!I) {
     return rational(val, 1);
}

/**
The struct that implements rational numbers.  All relevant operators
(addition, subtraction, multiplication, division, exponentiation by a
 non-negative integer, equality and comparison) are overloaded.  The second
 operand for all binary operators except exponentiation may be either another
 $(D Rational) or another integer type.
 */
struct Rational(Int) if(isIntegerLike!Int) {
public:

// ----------------Multiplication operators----------------------------------
    auto opBinary(string op, Rhs)(Rhs rhs)
    if(op == "*" && is(CommonRational!(Int, Rhs)) && isRational!Rhs) {
        auto ret = CommonRational!(Int, Rhs)(this.num, this.denom);
        return ret *= rhs;
    }

    auto opBinary(string op, Rhs)(Rhs rhs)
    if(op == "*" && is(CommonRational!(Int, Rhs)) && isIntegerLike!Rhs) {
        auto ret = this;
        return ret *= rhs;
    }

    auto opBinaryRight(string op, Rhs)(Rhs rhs)
    if(op == "*" && is(CommonRational!(Int, Rhs)) && isIntegerLike!Rhs) {
        return opBinary!(op, Rhs)(rhs);
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "*" && isRational!Rhs) {
        // Cancel common factors first, then multiply.  This prevents
        // overflows and is much more efficient when using BigInts.
        auto divisor = gcf(this.numerator, rhs.denominator);
        this.numerator /= divisor;
        rhs.denominator /= divisor;

        divisor = gcf(this.denominator, rhs.numerator);
        this.denominator /= divisor;
        rhs.numerator /= divisor;

        this.numerator *= rhs.numerator;
        this.denominator *= rhs.denominator;

        // Don't need to simplify.  Already cancelled common factors before
        // multiplying.
        fixSigns();
        return this;
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "*" && isIntegerLike!Rhs) {
        auto divisor = gcf(this.denominator, rhs);
        this.denominator /= divisor;
        rhs /= divisor;
        this.numerator *= rhs;

        // Don't need to simplify.  Already cancelled common factors before
        // multiplying.
        fixSigns();
        return this;
    }

// --------------------Division operators--------------------------------------

    auto opBinary(string op, Rhs)(Rhs rhs)
    if(op == "/" && is(CommonRational!(Int, Rhs)) && isRational!Rhs) {
        // Division = multiply by inverse.
        swap(rhs.numerator, rhs.denominator);
        return this *= rhs;
    }

    typeof(this) opBinary(string op, Rhs)(Rhs rhs)
    if(op == "/" && is(CommonRational!(Int, Rhs)) && isIntegerLike!(Rhs)) {
        auto ret = CommonRational!(Int, Rhs)(this.num, this.denom);
        return ret /= rhs;
    }

    typeof(this) opBinaryRight(string op, Rhs)(Rhs rhs)
    if(op == "/" && is(CommonRational!(Int, Rhs)) && isIntegerLike!Rhs) {
        auto ret = CommonRational!(Int, Rhs)(this.denom, this.num);
        return ret *= rhs;
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "/" && isIntegerLike!Rhs) {
        auto divisor = gcf(this.numerator, rhs);
        this.numerator /= divisor;
        rhs /= divisor;
        this.denominator *= rhs;

        // Don't need to simplify.  Already cancelled common factors before
        // multiplying.
        fixSigns();
        return this;
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "/" && isRational!Rhs) {
        // Division = multiply by inverse.
        swap(rhs.numerator, rhs.denominator);
        return this *= rhs;
    }

// ---------------------Addition operators-------------------------------------
    auto opBinary(string op, Rhs)(Rhs rhs)
    if(op == "+" && (isRational!Rhs || isIntegerLike!Rhs)) {
        auto ret = CommonRational!(typeof(this), Rhs)(this.num, this.denom);
        return ret += rhs;
    }

    auto opBinaryRight(string op, Rhs)(Rhs rhs)
    if(op == "+" && is(CommonRational!(Int, Rhs)) && isIntegerLike!Rhs) {
        return opBinary!(op, Rhs)(rhs);
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "+" && isRational!Rhs) {
        if(this.denominator == rhs.denominator) {
            this.numerator += rhs.numerator;
            simplify();
            return this;
        }

        Int commonDenom = lcm(this.denominator, rhs.denominator);
        this.numerator *= commonDenom / this.denominator;
        this.numerator += (commonDenom / rhs.denominator) * rhs.numerator;
        this.denominator = commonDenom;

        simplify();
        return this;
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "+" && isIntegerLike!Rhs) {
        this.numerator += rhs * this.denominator;

        simplify();
        return this;
    }

// -----------------------Subtraction operators-------------------------------

    auto opBinary(string op, Rhs)(Rhs rhs)
    if(op == "-" && is(CommonRational!(Int, Rhs))) {
        auto ret = CommonRational!(typeof(this), Rhs)(this.num, this.denom);
        return ret -= rhs;
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "-" && isRational!Rhs) {
        if(this.denominator == rhs.denominator) {
            this.numerator -= rhs.numerator;
            simplify();
            return this;
        }

        auto commonDenom = lcm(this.denominator, rhs.denominator);
        this.numerator *= commonDenom / this.denominator;
        this.numerator -= (commonDenom / rhs.denominator) * rhs.numerator;
        this.denominator = commonDenom;

        simplify();
        return this;
    }

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "-" && isIntegerLike!Rhs) {
        this.numerator -= rhs * this.denominator;

        simplify();
        return this;
    }

    typeof(this) opBinaryRight(string op, Rhs)(Rhs rhs)
    if(op == "-" && is(CommonInteger!(Int, Rhs)) && isIntegerLike!Rhs) {
        typeof(this) ret;
        ret.denominator = this.denominator;
        ret.numerator = (rhs * this.denominator) - this.numerator;

        simplify();
        return ret;
    }

// ----------------------Unary operators---------------------------------------

    typeof(this) opUnary(string op)() if(op == "-" || op == "+") {
        mixin("return typeof(this)(" ~ op ~ "numerator, denominator);");
    }

// ---------------------Exponentiation operator---------------------------------

    // Can only handle integer powers if the result has to also be
    // rational.

    typeof(this) opOpAssign(string op, Rhs)(Rhs rhs)
    if(op == "^^" && isIntegerLike!Rhs) {
        if(rhs < 0) {
            this.invert();
            rhs *= -1;
        }

        /* Don't need to simplify here.  this is already simplified, meaning
           the numerator and denominator don't have any common factors.  Raising
           both to a positive integer power won't create any.
         */
         numerator ^^= rhs;
         denominator ^^= rhs;
         return this;
    }

    auto opBinary(string op, Rhs)(Rhs rhs)
    if(op == "^^" && isIntegerLike!Rhs && is(CommonRational!(Int, Rhs))) {
        auto ret = CommonRational!(Int, Rhs)(this.num, this.denom);
        ret ^^= rhs;
        return ret;
    }

// ---------------------Assignment operators------------------------------------
    typeof(this) opAssign(Rhs)(Rhs rhs)
    if(isIntegerLike!Rhs && isAssignable!(Int, Rhs)) {
        this.numerator = rhs;
        this.denominator = 1;
        return this;
    }

    typeof(this) opAssign(Rhs)(Rhs rhs)
    if(isRational!Rhs && isAssignable!(Int, typeof(Rhs.num))) {
        this.numerator = rhs.num;
        this.denominator = rhs.denom;
        return this;
    }

// --------------------Comparison/Equality Operators---------------------------

    bool opEquals(Rhs)(Rhs rhs) if(isRational!Rhs || isIntegerLike!Rhs) {
        static if(isRational!Rhs) {
            return rhs.numerator == this.numerator &&
                rhs.denominator == this.denominator;
        } else {
            static assert(isIntegerLike!Rhs);
            return rhs == this.numerator && this.denominator == 1;
        }
    }

    int opCmp(Rhs)(Rhs rhs) if(isRational!Rhs) {
        if( opEquals(rhs)) {
            return 0;
        }

        // Check a few obvious cases first, see if we can avoid having to use a
        // common denominator.  These are basically speed hacks.

        // Assumption:  When simplify() is called, rational will be written in
        // canonical form, with any negative signs being only in the numerator.
        if(this.numerator < 0 && rhs.numerator > 0) {
            return -1;
        } else if(this.numerator > 0 && rhs.numerator < 0) {
            return 1;
        } else if(this.numerator >= rhs.numerator &&
            this.denominator <= rhs.denominator) {
            // We've already ruled out equality, so this must be > rhs.
            return 1;
        } else if(rhs.numerator >= this.numerator &&
            rhs.denominator <= this.denominator) {
            return -1;
        }

        // Can't do it without common denominator.  Argh.
        auto commonDenom = lcm(this.denominator, rhs.denominator);
        auto lhsNum = this.numerator * (commonDenom / this.denominator);
        auto rhsNum = rhs.numerator * (commonDenom / rhs.denominator);

        if(lhsNum > rhsNum) {
            return 1;
        } else if(lhsNum < rhsNum) {
            return -1;
        }

        // We've checked for equality already.  If we get to this point,
        // there's clearly something wrong.
        assert(0);
    }

    int opCmp(Rhs)(Rhs rhs) if(isIntegerLike!Rhs) {
        if( opEquals(rhs)) {
            return 0;
        }

        // Again, check the obvious cases first.
        if(rhs >= this.numerator) {
            return -1;
        }

        rhs *= this.denominator;
        if(rhs > this.numerator) {
            return -1;
        } else if(rhs < this.numerator) {
            return 1;
        }

        // Already checked for equality.  If we get here, something's wrong.
        assert(0);
    }

///////////////////////////////////////////////////////////////////////////////

    /**Fast inversion, equivalent to 1 / rational.*/
    typeof(this) invert() {
        swap(numerator, denominator);
        return this;
    }

    /**Convert to floating point representation.*/
    F opCast(F)() if(isFloatingPoint!F) {
        // Do everything in real precision, then convert to F at the end.

        static if(isIntegral!(Int)) {
            return cast(real) numerator / denominator;
        } else {
            auto temp = this;
            real expon = 1.0;
            real ans = 0;
            byte sign = 1;
            if(temp.numerator < 0) {
                temp.numerator *= -1;
                sign = -1;
            }

            while(temp.numerator > 0) {
                while(temp.numerator < temp.denominator) {

                    assert(temp.denominator > 0);

                    static if(is(typeof(temp.denominator & 1))) {
                        // Try to make numbers smaller instead of bigger.
                        if((temp.denominator & 1) == 0) {
                            temp.denominator >>= 1;
                        } else {
                            temp.numerator <<= 1;
                        }
                    } else {
                        temp.numerator <<= 1;
                    }

                    expon *= 0.5;

                    // This checks for overflow in case we're working with a
                    // user-defined fixed-precision integer.
                    enforce(temp.numerator > 0, text(
                        "Overflow while converting ", typeof(this).stringof,
                        " to ", F.stringof, "."));

                }

                auto intPart = temp.numerator / temp.denominator;

                static if(is(Int == std.bigint.BigInt)) {
                    // This should really be a cast, but BigInt still has a few
                    // issues.
                    long lIntPart = intPart.toLong();
                } else {
                    long lIntPart = cast(long) intPart;
                }

                // Test for changes.
                real oldAns = ans;
                ans += lIntPart * expon;
                if(ans == oldAns) {  // Smaller than epsilon.
                    return ans * sign;
                }

                // Subtract out int part.
                temp.numerator -= intPart * temp.denominator;
            }

            return ans * sign;
        }
    }

    /**
    Casts $(D this) to an integer by truncating the fractional part.
    Equivalent to $(D integerPart), and then casting it to type $(D I).
     */
    I opCast(I)() if(isIntegerLike!I && is(typeof(cast(I) Int.init))) {
        return cast(I) integerPart;
    }

    /**Returns the numerator.*/
    @property Int num() {
        return numerator;
    }

    /**Returns the denominator.*/
    @property Int denom() {
        return denominator;
    }

    /**
    Returns the integer part of this rational, with any remainder truncated.
     */
    @property Int integerPart() {
        return num / denom;
    }

    /**
    Returns the fractional part of this rational.
    */
    @property typeof(this) fractionPart() {
        return this - integerPart;
    }

    /**
    Returns a string representation of $(D this) in the form this.num /
    this.denom.
    */
    string toString() {
        static if(is(Int == std.bigint.BigInt)) {
            // Special case it for now.  This should be fixed later.
            return toDecimalString(numerator) ~ " / " ~
                toDecimalString(denominator);
        } else {
            return to!string(numerator) ~ " / " ~ to!string(denominator);
        }
    }

private :
    Int numerator;
    Int denominator;

    void simplify() {
        if(numerator == 0) {
            denominator = 1;
            return;
        }

        auto divisor = gcf(numerator, denominator);
        numerator /= divisor;
        denominator /= divisor;

        fixSigns();
    }

    void fixSigns() {
        static if( !is(Int == ulong) && !is(Int == uint) &&
            !is(Int == ushort) && !is(Int == ubyte)) {
            // Write in canonical form w.r.t. signs.
            if(denominator < 0) {
                denominator *= -1;
                numerator *= -1;
            }
        }
    }
}

unittest {
    // All reference values from the Maxima computer algebra system.

    // Test c'tor and simplification first.
    auto num = BigInt("295147905179352825852");
    auto den = BigInt("147573952589676412920");
    auto simpNum = BigInt("24595658764946068821");
    auto simpDen = BigInt("12297829382473034410");
    auto f1 = rational(num, den);
    auto f2 = rational(simpNum, simpDen);
    assert(f1 == f2);

    // Test multiplication.
    assert( rational(8, 42) * rational(cast(byte) 7, cast(byte) 68)
        == rational(1, 51));
    assert(rational(20_000L, 3_486_784_401U) * rational(3_486_784_401U, 1_000U)
        == rational(20, 1));
    auto f3 = rational(7, 57);
    f3 *= rational(2, 78);
    assert(f3 == rational(7, 2223));
    f3 = 5 * f3;
    assert(f3 == rational(35, 2223));
    assert(f3 * 5UL == 5 * f3);

    // Test division.  Since it's implemented in terms of multiplication,
    // quick and dirty tests should be good enough.
    assert( rational(7, 38) / rational(8, 79) == rational(553, 304));
    assert( rational(7, 38) / rational(8, 79) == rational(553, 304));
    auto f4 = rational(7, 38);
    f4 /= rational(8UL, 79);
    assert(f4 == rational(553, 304));
    f4 = f4 / 2;
    assert(f4 == rational(553, 608));
    f4 = 2 / f4;
    assert(f4 == rational(1216, 553));
    assert(f4 * 2 == f4 * rational(2));
    f4 = 2;
    assert(f4 == 2);

    // Test addition.
    assert( rational(1, 3) + rational(cast(byte) 2, cast(byte) 3) == rational(1, 1));
    assert( rational(1, 3) + rational(1, 2L) == rational(5, 6));
    auto f5 = rational( BigInt("314159265"), BigInt("27182818"));
    auto f6 = rational( BigInt("8675309"), BigInt("362436"));
    f5 += f6;
    assert(f5 == rational( BigInt("174840986505151"), BigInt("4926015912324")));
    assert( rational(1, 3) + 2UL == rational(7, 3));
    assert( 5UL + rational(1, 5) == rational(26, 5));

    // Test subtraction.
    assert( rational(2, 3) - rational(1, 3) == rational(1, 3UL));
    assert( rational(1UL, 2) - rational(1, 3) == rational(1, 6));
    f5 = rational( BigInt("314159265"), BigInt("27182818"));
    f5 -= f6;
    assert(f5 == rational( BigInt("-60978359135611"), BigInt("4926015912324")));
    assert( rational(4, 3) - 1 == rational(1, 3));
    assert(1 - rational(1, 4) == rational(3, 4));

    // Test unary operators.
    auto fExp = rational(2, 5);
    assert(-fExp == rational(-2, 5));
    assert(+fExp == rational(2, 5));

    // Test exponentiation.
    fExp ^^= 3;
    assert(fExp == rational(8, 125));
    fExp = fExp ^^ 2;
    assert(fExp == rational(64, 125 * 125));
    assert(rational(2, 5) ^^ -2 == rational(25, 4));

    // Test decimal conversion.
    assert(approxEqual(cast(real) f5, -12.37883925284411L));

    // Test comparison.
    assert(rational(1UL, 6) < rational(1, 2));
    assert(rational(cast(byte) 1, cast(byte) 2) > rational(1, 6));
    assert(rational(-1, 7) < rational(7, 2));
    assert(rational(7, 2) > rational(-1, 7));
    assert(rational(7, 9) > rational(8, 11));
    assert(rational(8, 11) < rational(7, 9));

    assert(rational(9, 10) < 1UL);
    assert(1UL > rational(9, 10));
    assert(10 > rational(9L, 10));
    assert(2 > rational(5, 4));
    assert(1 < rational(5U, 4));

    // Test creating rationals of value zero.
    auto zero = rational(0, 8);
    assert(zero == 0);
    assert(zero == rational(0, 16));
    assert(zero.num == 0);
    assert(zero.denom == 1);
    auto one = zero + 1;
    one -= one;
    assert(one == zero);

    // Test integerPart, fraction part.
    auto intFract = rational(5, 4);
    assert(intFract.integerPart == 1);
    assert(intFract.fractionPart == rational(1, 4));
    assert(cast(long) intFract == 1);

    // Test whether CTFE works for primitive types.  Doesn't work yet.
//    enum myRational = (((rational(1, 2) + rational(1, 4)) * 2 - rational(1, 4))
//        / 2 + 1 * rational(1, 2) - 1) / rational(2, 5);
//    writeln(myRational);
//    static assert(myRational == rational(-15, 32));
}

/**
Convert a floating point number to a Rational based on integer type Int.
Allows an error tolerance of epsilon.  (Default epsilon = 1e-8.)

epsilon must be greater than 1.0L / long.max.

Throws:  Exception on infinities, NaNs, numbers with absolute value
larger than long.max and epsilons smaller than 1.0L / long.max.

Examples:
---
// Prints "22 / 7".
writeln( toRational!int( PI, 1e-1));
---
 */
Rational!(Int) toRational(Int)(real floatNum, real epsilon = 1e-8) {
    enforce(floatNum != real.infinity && floatNum != -real.infinity
        && !isNaN(floatNum), "Can't convert NaNs and infinities to rational.");
    enforce(floatNum < long.max && floatNum > -long.max,
        "Rational conversions of very large numbers not yet implemented.");
    enforce(1.0L / epsilon < long.max,
        "Can't handle very small epsilons < long.max in toRational.");

    // Handle this as a special case to make the rest of the code less
    // complicated:
    if( abs(floatNum) < epsilon) {
        Rational!Int ret;
        ret.numerator = 0;
        ret.denominator = 1;
        return ret;
    }

    return toRationalImpl!(Int)(floatNum, epsilon);
}

private Rational!Int toRationalImpl(Int)(real floatNum, real epsilon) {
    real actualEpsilon;
    Rational!Int ret;

    if( abs(floatNum) < 1) {
        real invFloatNum = 1.0L / floatNum;
        long intPart = roundTo!long(invFloatNum);
        actualEpsilon = floatNum - 1.0L / intPart;

        static if(isIntegral!(Int)) {
            ret.denominator = cast(Int) intPart;
            ret.numerator = cast(Int) 1;
        } else {
            ret.denominator = intPart;
            ret.numerator = 1;
        }
    } else {
        long intPart = roundTo!long(floatNum);
        actualEpsilon = floatNum - intPart;

        static if(isIntegral!(Int)) {
            ret.denominator = cast(Int) 1;
            ret.numerator = cast(Int) intPart;
        } else {
            ret.denominator = 1;
            ret.numerator = intPart;
        }
    }

    if(abs(actualEpsilon) <= epsilon) {
        return ret;
    }

    // Else get results from downstream recursions, add them to this result.
    return ret + toRationalImpl!(Int)(actualEpsilon, epsilon);
}

unittest {
    // Start with simple cases.
    assert( toRational!int(0.5) == rational(1, 2));
    assert( toRational!BigInt(0.333333333333333L) ==
        rational( BigInt(1), BigInt(3)));
    assert( toRational!int(2.470588235294118) ==
        rational( cast(int) 42, cast(int) 17));
    assert( toRational!long(2.007874015748032) == rational(255L, 127L));
    assert( toRational!int( 3.0L / 7.0L) == rational(3, 7));
    assert( toRational!int( 7.0L / 3.0L) == rational(7, 3));

    // Now for some fun.
    real myEpsilon = 1e-8;
    auto piRational = toRational!long(PI, myEpsilon);
    assert( abs( cast(real) piRational - PI) < myEpsilon);

    auto eRational = toRational!long(E, myEpsilon);
    assert( abs( cast(real) eRational - E) < myEpsilon);
}


/**
Find the greatest common factor of num1 and num2 using Euclid's Algorithm.
*/
CommonInteger!(I1, I2) gcf(I1, I2)(I1 num1, I2 num2)
if(isIntegerLike!I1 && isIntegerLike!I2) {
    num1 = iAbs(num1);
    num2 = iAbs(num2);
    if(num2 > num1) {
        return gcf(num2, num1);
    } else if(num2 == num1) {
        typeof(return) ret = num1;
        return ret;
    }

    // Work around Bug 4742.
    static if(is(I1 == I2)) {
        auto remainder = num1 % num2;
    } else {
        typeof(return) workaround1 = num1;
        typeof(return) workaround2 = num2;
        auto remainder = workaround1 % workaround2;
    }

    if(remainder == 0) {
        typeof(return) ret = num2;
        return ret;
    } else {
        return gcf(num2, remainder);
    }
    assert(0);
}

unittest {
    // Values from the Maxima computer algebra system.
    assert(gcf( BigInt(314_156_535UL), BigInt(27_182_818_284UL)) == BigInt(3));
    assert(gcf(8675309, 362436) == 1);
    assert(gcf( BigInt("8589934596"), BigInt("295147905179352825852")) ==
        12);
}

/**
Find the least common multiple of num1, num2.
*/
CommonInteger!(I1, I2) lcm(I1, I2)(I1 num1, I2 num2)
if(isIntegerLike!I1 && isIntegerLike!I2) {
    num1 = iAbs(num1);
    num2 = iAbs(num2);
    if(num1 == num2) {
        return num1;
    }
    return (num1 / gcf(num1, num2)) * num2;
}

/**
Absolute value function that should gracefully handle any reasonable
BigInt implementation.
*/
Int iAbs(Int)(Int num1)
if(isIntegerLike!Int) {
    static if(isUnsigned!Int) {
        return num1;
    } else {
        // For some reason DMD insists that a byte multipled by -1 is an int
        // not a byte.
        return cast(Int) ((num1 < 0) ? -1 * num1 : num1);
    }
}

/**
Returns the largest integer less than or equal to $(D r).
*/
Int floor(Int)(Rational!Int r) {
    auto intPart = r.integerPart;
    if(r > 0 || intPart == r) {
        return intPart;
    } else {
        intPart -= 1;
        return intPart;
    }
}

unittest {
    assert(floor(rational(1, 2)) == 0);
    assert(floor(rational(-1, 2)) == -1);
    assert(floor(rational(2)) == 2);
    assert(floor(rational(-2)) == -2);
    assert(floor(rational(-1, 2)) == -1);
}

/**
Returns the smallest integer greater than or equal to $(D r).
*/
Int ceil(Int)(Rational!Int r) {
    auto intPart = r.integerPart;
    if(intPart == r || r < 0) {
        return intPart;
    } else {
        intPart += 1;
        return intPart;
    }
}

unittest {
    assert(ceil(rational(1, 2)) == 1);
    assert(ceil(rational(0)) == 0);
    assert(ceil(rational(-1, 2)) == 0);
    assert(ceil(rational(1)) == 1);
    assert(ceil(rational(-2)) == -2);
}

/**
Round $(D r) to the nearest integer.  If the fractional part is exactly
1 / 2, $(D r) will be rounded such that the absolute value is increased by
rounding.
 */
Int round(Int)(Rational!Int r) {
    auto intPart = r.integerPart;
    auto fractPart = r.fractionPart;

    bool added;
    if(fractPart >= rational(1, 2)) {
        added = true;
        intPart += 1;
    }

    static if(!isUnsigned!Int) {
        if(!added && fractPart <= rational(-1, 2)) {
            intPart -= 1;
        }
    }

    return intPart;
}

unittest {
    assert(round(rational(1, 3)) == 0);
    assert(round(rational(7, 2)) == 4);
    assert(round(rational(-3, 4)) == -1);
    assert(round(rational(8U, 15U)) == 1);
}
