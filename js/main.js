"use strict";
// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof F) {
            f = E(B(f));
        }
        if(f instanceof PAP) {
            // f is a partial application
            if(args.length == f.arity) {
                // Saturated application
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                // Application is still unsaturated
                return new PAP(f.f, f.args.concat(args));
            } else {
                // Application is oversaturated; 
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else if(f instanceof Function) {
            if(args.length == f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,str.charCodeAt(i),new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1]));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(I_getBits(i,0)) + popCnt(I_getBits(i,1));
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return [0,1,0,0,0];
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return [0,1,0,0,0];
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1]));
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, ks[i], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as[0] === 1; as = as[2]) {
        arr.push(as[1]);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem],new T(function(){return __arr2lst(elem+1,arr);})]
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs[0] === 1; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=[0,_],_1=function(_2,_3){return E(_2)==E(_3);},_4=function(_5,_6){while(1){var _7=E(_5);if(!_7[0]){return (E(_6)[0]==0)?true:false;}else{var _8=E(_6);if(!_8[0]){return false;}else{if(E(_7[1])!=E(_8[1])){return false;}else{_5=_7[2];_6=_8[2];continue;}}}}},_9=function(_a,_b){return (!B(_4(_a,_b)))?true:false;},_c=[0,_4,_9],_d="deltaZ",_e="deltaY",_f="deltaX",_g=function(_h,_i){var _j=E(_h);return (_j[0]==0)?E(_i):[1,_j[1],new T(function(){return B(_g(_j[2],_i));})];},_k=function(_l,_m){var _n=jsShowI(_l);return new F(function(){return _g(fromJSStr(_n),_m);});},_o=41,_p=40,_q=function(_r,_s,_t){if(_s>=0){return new F(function(){return _k(_s,_t);});}else{if(_r<=6){return new F(function(){return _k(_s,_t);});}else{return [1,_p,new T(function(){var _u=jsShowI(_s);return B(_g(fromJSStr(_u),[1,_o,_t]));})];}}},_v=new T(function(){return B(unCStr(")"));}),_w=new T(function(){return B(_q(0,2,_v));}),_x=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_w));}),_y=function(_z){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_q(0,_z,_x));}))));});},_A=function(_B,_){return new T(function(){var _C=Number(E(_B)),_D=jsTrunc(_C);if(_D<0){return B(_y(_D));}else{if(_D>2){return B(_y(_D));}else{return _D;}}});},_E=0,_F=[0,_E,_E,_E],_G="button",_H=new T(function(){return jsGetMouseCoords;}),_I=[0],_J=function(_K,_){var _L=E(_K);if(!_L[0]){return _I;}else{var _M=B(_J(_L[2],_));return [1,new T(function(){var _N=Number(E(_L[1]));return jsTrunc(_N);}),_M];}},_O=function(_P,_){var _Q=__arr2lst(0,_P);return new F(function(){return _J(_Q,_);});},_R=function(_S,_){return new F(function(){return _O(E(_S),_);});},_T=function(_U,_){return new T(function(){var _V=Number(E(_U));return jsTrunc(_V);});},_W=[0,_T,_R],_X=function(_Y,_){var _Z=E(_Y);if(!_Z[0]){return _I;}else{var _10=B(_X(_Z[2],_));return [1,_Z[1],_10];}},_11=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_12=new T(function(){return B(unCStr("base"));}),_13=new T(function(){return B(unCStr("IOException"));}),_14=new T(function(){var _15=hs_wordToWord64(4053623282),_16=hs_wordToWord64(3693590983);return [0,_15,_16,[0,_15,_16,_12,_11,_13],_I,_I];}),_17=function(_18){return E(_14);},_19=function(_1a){return E(E(_1a)[1]);},_1b=function(_1c,_1d,_1e){var _1f=B(A(_1c,[_])),_1g=B(A(_1d,[_])),_1h=hs_eqWord64(_1f[1],_1g[1]);if(!_1h){return [0];}else{var _1i=hs_eqWord64(_1f[2],_1g[2]);return (!_1i)?[0]:[1,_1e];}},_1j=function(_1k){var _1l=E(_1k);return new F(function(){return _1b(B(_19(_1l[1])),_17,_1l[2]);});},_1m=new T(function(){return B(unCStr(": "));}),_1n=new T(function(){return B(unCStr(")"));}),_1o=new T(function(){return B(unCStr(" ("));}),_1p=new T(function(){return B(unCStr("interrupted"));}),_1q=new T(function(){return B(unCStr("system error"));}),_1r=new T(function(){return B(unCStr("unsatisified constraints"));}),_1s=new T(function(){return B(unCStr("user error"));}),_1t=new T(function(){return B(unCStr("permission denied"));}),_1u=new T(function(){return B(unCStr("illegal operation"));}),_1v=new T(function(){return B(unCStr("end of file"));}),_1w=new T(function(){return B(unCStr("resource exhausted"));}),_1x=new T(function(){return B(unCStr("resource busy"));}),_1y=new T(function(){return B(unCStr("does not exist"));}),_1z=new T(function(){return B(unCStr("already exists"));}),_1A=new T(function(){return B(unCStr("resource vanished"));}),_1B=new T(function(){return B(unCStr("timeout"));}),_1C=new T(function(){return B(unCStr("unsupported operation"));}),_1D=new T(function(){return B(unCStr("hardware fault"));}),_1E=new T(function(){return B(unCStr("inappropriate type"));}),_1F=new T(function(){return B(unCStr("invalid argument"));}),_1G=new T(function(){return B(unCStr("failed"));}),_1H=new T(function(){return B(unCStr("protocol error"));}),_1I=function(_1J,_1K){switch(E(_1J)){case 0:return new F(function(){return _g(_1z,_1K);});break;case 1:return new F(function(){return _g(_1y,_1K);});break;case 2:return new F(function(){return _g(_1x,_1K);});break;case 3:return new F(function(){return _g(_1w,_1K);});break;case 4:return new F(function(){return _g(_1v,_1K);});break;case 5:return new F(function(){return _g(_1u,_1K);});break;case 6:return new F(function(){return _g(_1t,_1K);});break;case 7:return new F(function(){return _g(_1s,_1K);});break;case 8:return new F(function(){return _g(_1r,_1K);});break;case 9:return new F(function(){return _g(_1q,_1K);});break;case 10:return new F(function(){return _g(_1H,_1K);});break;case 11:return new F(function(){return _g(_1G,_1K);});break;case 12:return new F(function(){return _g(_1F,_1K);});break;case 13:return new F(function(){return _g(_1E,_1K);});break;case 14:return new F(function(){return _g(_1D,_1K);});break;case 15:return new F(function(){return _g(_1C,_1K);});break;case 16:return new F(function(){return _g(_1B,_1K);});break;case 17:return new F(function(){return _g(_1A,_1K);});break;default:return new F(function(){return _g(_1p,_1K);});}},_1L=new T(function(){return B(unCStr("}"));}),_1M=new T(function(){return B(unCStr("{handle: "));}),_1N=function(_1O,_1P,_1Q,_1R,_1S,_1T){var _1U=new T(function(){var _1V=new T(function(){var _1W=new T(function(){var _1X=E(_1R);if(!_1X[0]){return E(_1T);}else{var _1Y=new T(function(){return B(_g(_1X,new T(function(){return B(_g(_1n,_1T));},1)));},1);return B(_g(_1o,_1Y));}},1);return B(_1I(_1P,_1W));}),_1Z=E(_1Q);if(!_1Z[0]){return E(_1V);}else{return B(_g(_1Z,new T(function(){return B(_g(_1m,_1V));},1)));}}),_20=E(_1S);if(!_20[0]){var _21=E(_1O);if(!_21[0]){return E(_1U);}else{var _22=E(_21[1]);if(!_22[0]){var _23=new T(function(){var _24=new T(function(){return B(_g(_1L,new T(function(){return B(_g(_1m,_1U));},1)));},1);return B(_g(_22[1],_24));},1);return new F(function(){return _g(_1M,_23);});}else{var _25=new T(function(){var _26=new T(function(){return B(_g(_1L,new T(function(){return B(_g(_1m,_1U));},1)));},1);return B(_g(_22[1],_26));},1);return new F(function(){return _g(_1M,_25);});}}}else{return new F(function(){return _g(_20[1],new T(function(){return B(_g(_1m,_1U));},1));});}},_27=function(_28){var _29=E(_28);return new F(function(){return _1N(_29[1],_29[2],_29[3],_29[4],_29[6],_I);});},_2a=function(_2b,_2c,_2d){var _2e=E(_2c);return new F(function(){return _1N(_2e[1],_2e[2],_2e[3],_2e[4],_2e[6],_2d);});},_2f=function(_2g,_2h){var _2i=E(_2g);return new F(function(){return _1N(_2i[1],_2i[2],_2i[3],_2i[4],_2i[6],_2h);});},_2j=44,_2k=93,_2l=91,_2m=function(_2n,_2o,_2p){var _2q=E(_2o);if(!_2q[0]){return new F(function(){return unAppCStr("[]",_2p);});}else{var _2r=new T(function(){var _2s=new T(function(){var _2t=function(_2u){var _2v=E(_2u);if(!_2v[0]){return [1,_2k,_2p];}else{var _2w=new T(function(){return B(A(_2n,[_2v[1],new T(function(){return B(_2t(_2v[2]));})]));});return [1,_2j,_2w];}};return B(_2t(_2q[2]));});return B(A(_2n,[_2q[1],_2s]));});return [1,_2l,_2r];}},_2x=function(_2y,_2z){return new F(function(){return _2m(_2f,_2y,_2z);});},_2A=[0,_2a,_27,_2x],_2B=new T(function(){return [0,_17,_2A,_2C,_1j,_27];}),_2C=function(_2D){return [0,_2B,_2D];},_2E=[0],_2F=7,_2G=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_2H=[0,_2E,_2F,_I,_2G,_2E,_2E],_2I=new T(function(){return B(_2C(_2H));}),_2J=function(_){return new F(function(){return die(_2I);});},_2K=function(_2L){return E(E(_2L)[1]);},_2M=function(_2N,_2O,_2P,_){var _2Q=__arr2lst(0,_2P),_2R=B(_X(_2Q,_)),_2S=E(_2R);if(!_2S[0]){return new F(function(){return _2J(_);});}else{var _2T=E(_2S[2]);if(!_2T[0]){return new F(function(){return _2J(_);});}else{if(!E(_2T[2])[0]){var _2U=B(A(_2K,[_2N,_2S[1],_])),_2V=B(A(_2K,[_2O,_2T[1],_]));return [0,_2U,_2V];}else{return new F(function(){return _2J(_);});}}}},_2W=function(_){return new F(function(){return __jsNull();});},_2X=function(_2Y){var _2Z=B(A(_2Y,[_]));return E(_2Z);},_30=new T(function(){return B(_2X(_2W));}),_31=new T(function(){return E(_30);}),_32=function(_33,_34,_){if(E(_33)==7){var _35=E(_H)(_34),_36=B(_2M(_W,_W,_35,_)),_37=_34[E(_f)],_38=_34[E(_e)],_39=_34[E(_d)];return new T(function(){return [0,E(_36),E(_2E),[0,_37,_38,_39]];});}else{var _3a=E(_H)(_34),_3b=B(_2M(_W,_W,_3a,_)),_3c=_34[E(_G)],_3d=__eq(_3c,E(_31));if(!E(_3d)){var _3e=B(_A(_3c,_));return new T(function(){return [0,E(_3b),[1,_3e],E(_F)];});}else{return new T(function(){return [0,E(_3b),E(_2E),E(_F)];});}}},_3f=function(_3g,_3h,_){return new F(function(){return _32(_3g,E(_3h),_);});},_3i="mouseout",_3j="mouseover",_3k="mousemove",_3l="mouseup",_3m="mousedown",_3n="dblclick",_3o="click",_3p="wheel",_3q=function(_3r){switch(E(_3r)){case 0:return E(_3o);case 1:return E(_3n);case 2:return E(_3m);case 3:return E(_3l);case 4:return E(_3k);case 5:return E(_3j);case 6:return E(_3i);default:return E(_3p);}},_3s=[0,_3q,_3f],_3t=0,_3u=function(_){return _3t;},_3v=function(_3w,_){return [1,_3w];},_3x=function(_3y){return E(_3y);},_3z=[0,_3x,_3v],_3A=function(_3B,_3C,_){var _3D=B(A(_3B,[_])),_3E=B(A(_3C,[_]));return _3D;},_3F=function(_3G,_3H,_){var _3I=B(A(_3G,[_])),_3J=B(A(_3H,[_]));return new T(function(){return B(A(_3I,[_3J]));});},_3K=function(_3L,_3M,_){var _3N=B(A(_3M,[_]));return _3L;},_3O=function(_3P,_3Q,_){var _3R=B(A(_3Q,[_]));return new T(function(){return B(A(_3P,[_3R]));});},_3S=[0,_3O,_3K],_3T=function(_3U,_){return _3U;},_3V=function(_3W,_3X,_){var _3Y=B(A(_3W,[_]));return new F(function(){return A(_3X,[_]);});},_3Z=[0,_3S,_3T,_3F,_3V,_3A],_40=function(_41,_42,_){var _43=B(A(_41,[_]));return new F(function(){return A(_42,[_43,_]);});},_44=function(_45){return [0,_2E,_2F,_I,_45,_2E,_2E];},_46=function(_47,_){var _48=new T(function(){return B(_2C(new T(function(){return B(_44(_47));})));});return new F(function(){return die(_48);});},_49=[0,_3Z,_40,_3V,_3T,_46],_4a=[0,_49,_3x],_4b=[0,_4a,_3T],_4c=function(_4d,_4e){while(1){var _4f=E(_4d);if(!_4f[0]){return (E(_4e)[0]==0)?1:0;}else{var _4g=E(_4e);if(!_4g[0]){return 2;}else{var _4h=E(_4f[1]),_4i=E(_4g[1]);if(_4h!=_4i){return (_4h>_4i)?2:0;}else{_4d=_4f[2];_4e=_4g[2];continue;}}}}},_4j=function(_4k,_4l){return (B(_4c(_4k,_4l))==0)?true:false;},_4m=function(_4n,_4o){return (B(_4c(_4n,_4o))==2)?false:true;},_4p=function(_4q,_4r){return (B(_4c(_4q,_4r))==2)?true:false;},_4s=function(_4t,_4u){return (B(_4c(_4t,_4u))==0)?false:true;},_4v=function(_4w,_4x){return (B(_4c(_4w,_4x))==2)?E(_4w):E(_4x);},_4y=function(_4z,_4A){return (B(_4c(_4z,_4A))==2)?E(_4A):E(_4z);},_4B=[0,_c,_4c,_4j,_4m,_4p,_4s,_4v,_4y],_4C=[1,_I],_4D=new T(function(){return B(unCStr("Tried to deserialie a non-array to a list!"));}),_4E=[0,_4D],_4F=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4G=new T(function(){return B(unCStr("base"));}),_4H=new T(function(){return B(unCStr("PatternMatchFail"));}),_4I=new T(function(){var _4J=hs_wordToWord64(18445595),_4K=hs_wordToWord64(52003073);return [0,_4J,_4K,[0,_4J,_4K,_4G,_4F,_4H],_I,_I];}),_4L=function(_4M){return E(_4I);},_4N=function(_4O){var _4P=E(_4O);return new F(function(){return _1b(B(_19(_4P[1])),_4L,_4P[2]);});},_4Q=function(_4R){return E(E(_4R)[1]);},_4S=function(_4T){return [0,_4U,_4T];},_4V=function(_4W,_4X){return new F(function(){return _g(E(_4W)[1],_4X);});},_4Y=function(_4Z,_50){return new F(function(){return _2m(_4V,_4Z,_50);});},_51=function(_52,_53,_54){return new F(function(){return _g(E(_53)[1],_54);});},_55=[0,_51,_4Q,_4Y],_4U=new T(function(){return [0,_4L,_55,_4S,_4N,_4Q];}),_56=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_57=function(_58){return E(E(_58)[3]);},_59=function(_5a,_5b){return new F(function(){return die(new T(function(){return B(A(_57,[_5b,_5a]));}));});},_5c=function(_5d,_5e){return new F(function(){return _59(_5d,_5e);});},_5f=function(_5g,_5h){var _5i=E(_5h);if(!_5i[0]){return [0,_I,_I];}else{var _5j=_5i[1];if(!B(A(_5g,[_5j]))){return [0,_I,_5i];}else{var _5k=new T(function(){var _5l=B(_5f(_5g,_5i[2]));return [0,_5l[1],_5l[2]];});return [0,[1,_5j,new T(function(){return E(E(_5k)[1]);})],new T(function(){return E(E(_5k)[2]);})];}}},_5m=32,_5n=new T(function(){return B(unCStr("\n"));}),_5o=function(_5p){return (E(_5p)==124)?false:true;},_5q=function(_5r,_5s){var _5t=B(_5f(_5o,B(unCStr(_5r)))),_5u=_5t[1],_5v=function(_5w,_5x){var _5y=new T(function(){var _5z=new T(function(){return B(_g(_5s,new T(function(){return B(_g(_5x,_5n));},1)));});return B(unAppCStr(": ",_5z));},1);return new F(function(){return _g(_5w,_5y);});},_5A=E(_5t[2]);if(!_5A[0]){return new F(function(){return _5v(_5u,_I);});}else{if(E(_5A[1])==124){return new F(function(){return _5v(_5u,[1,_5m,_5A[2]]);});}else{return new F(function(){return _5v(_5u,_I);});}}},_5B=function(_5C){return new F(function(){return _5c([0,new T(function(){return B(_5q(_5C,_56));})],_4U);});},_5D=function(_5E){return new F(function(){return _5B("Main.hs:45:3-81|function parseJSON");});},_5F=new T(function(){return B(_5D(_));}),_5G=function(_5H){return E(E(_5H)[3]);},_5I=function(_5J,_5K,_5L,_5M){var _5N=E(_5M);if(_5N[0]==3){var _5O=E(_5N[1]);if(!_5O[0]){return E(_5F);}else{var _5P=E(_5O[2]);if(!_5P[0]){return E(_5F);}else{var _5Q=E(_5P[2]);if(!_5Q[0]){return E(_5F);}else{if(!E(_5Q[2])[0]){var _5R=B(A(_5G,[_5J,_5O[1]]));if(!_5R[0]){return [0,_5R[1]];}else{var _5S=B(A(_5G,[_5K,_5P[1]]));if(!_5S[0]){return [0,_5S[1]];}else{var _5T=B(A(_5G,[_5L,_5Q[1]]));return (_5T[0]==0)?[0,_5T[1]]:[1,[0,_5R[1],_5S[1],_5T[1]]];}}}else{return E(_5F);}}}}}else{return E(_5F);}},_5U=function(_5V,_5W,_5X,_5Y){var _5Z=E(_5Y);if(_5Z[0]==3){var _60=function(_61){var _62=E(_61);if(!_62[0]){return E(_4C);}else{var _63=B(_5I(_5V,_5W,_5X,_62[1]));if(!_63[0]){return [0,_63[1]];}else{var _64=B(_60(_62[2]));return (_64[0]==0)?[0,_64[1]]:[1,[1,_63[1],_64[1]]];}}};return new F(function(){return _60(_5Z[1]);});}else{return E(_4E);}},_65=function(_66){return [1,toJSStr(E(_66))];},_67=new T(function(){return B(unCStr("Tried to deserialize long string to a Char"));}),_68=[0,_67],_69=new T(function(){return B(unCStr("Tried to deserialize a non-string to a Char"));}),_6a=[0,_69],_6b=function(_6c){var _6d=E(_6c);if(_6d[0]==1){var _6e=fromJSStr(_6d[1]);return (_6e[0]==0)?E(_68):(E(_6e[2])[0]==0)?[1,_6e[1]]:E(_68);}else{return E(_6a);}},_6f=new T(function(){return B(unCStr("Tried to deserialize a non-JSString to a JSString"));}),_6g=[0,_6f],_6h=function(_6i){var _6j=E(_6i);return (_6j[0]==1)?[1,new T(function(){return fromJSStr(_6j[1]);})]:E(_6g);},_6k=function(_6l){return [1,toJSStr([1,_6l,_I])];},_6m=[0,_6k,_65,_6b,_6h],_6n=function(_6o){return new F(function(){return _5B("Main.hs:63:3-45|function jsonToUnion");});},_6p=new T(function(){return B(_6n(_));}),_6q=function(_6r){return new F(function(){return _5B("Main.hs:(67,3)-(70,33)|function jsonToUnion");});},_6s=new T(function(){return B(_6q(_));}),_6t=function(_6u){return E(E(_6u)[1]);},_6v=function(_6w){return new F(function(){return toJSStr(E(_6w));});},_6x=function(_6y,_6z,_6A){return [4,[1,[0,new T(function(){return B(_6v(_6z));}),new T(function(){return B(A(_6t,[_6y,E(_6A)[1]]));})],_I]];},_6B=function(_6C,_6D){var _6E=E(_6D);return (_6E[0]==0)?[0]:[1,new T(function(){return B(A(_6C,[_6E[1]]));}),new T(function(){return B(_6B(_6C,_6E[2]));})];},_6F=function(_6G,_6H,_6I){return [3,E(B(_6B(function(_6J){return new F(function(){return _6x(_6G,_6H,_6J);});},_6I)))];},_6K=function(_6L){return new F(function(){return _5B("Main.hs:49:3-73|function parseJSON");});},_6M=new T(function(){return B(_6K(_));}),_6N=function(_6O,_6P){var _6Q=E(_6P);if(_6Q[0]==4){var _6R=E(_6Q[1]);if(!_6R[0]){return E(_6M);}else{if(!E(_6R[2])[0]){var _6S=B(A(_5G,[_6O,E(_6R[1])[2]]));return (_6S[0]==0)?[0,_6S[1]]:[1,[0,_6S[1]]];}else{return E(_6M);}}}else{return E(_6M);}},_6T=[1,_I],_6U=[0,_4D],_6V=function(_6W,_6X){var _6Y=E(_6X);if(_6Y[0]==3){var _6Z=function(_70){var _71=E(_70);if(!_71[0]){return E(_6T);}else{var _72=E(_71[1]);if(_72[0]==4){var _73=E(_72[1]);if(!_73[0]){return E(_6M);}else{if(!E(_73[2])[0]){var _74=B(A(_5G,[_6W,E(_73[1])[2]]));if(!_74[0]){return [0,_74[1]];}else{var _75=B(_6Z(_71[2]));return (_75[0]==0)?[0,_75[1]]:[1,[1,[0,_74[1]],_75[1]]];}}else{return E(_6M);}}}else{return E(_6M);}}};return new F(function(){return _6Z(_6Y[1]);});}else{return E(_6U);}},_76=function(_77,_78){return [0,function(_6J){return new F(function(){return _6x(_77,_78,_6J);});},function(_6J){return new F(function(){return _6F(_77,_78,_6J);});},function(_79){return new F(function(){return _6N(_77,_79);});},function(_7a){return new F(function(){return _6V(_77,_7a);});}];},_7b=new T(function(){return B(unCStr("final"));}),_7c=function(_7d){return [3,E(B(_6B(_65,_7d)))];},_7e=function(_7f){return [3,E(B(_6B(_7c,_7f)))];},_7g=[1,_I],_7h=new T(function(){return B(unCStr("Tried to deserialie a non-array to a list!"));}),_7i=[0,_7h],_7j=function(_7k){return E(E(_7k)[4]);},_7l=function(_7m,_7n){var _7o=E(_7n);if(_7o[0]==3){var _7p=new T(function(){return B(_7j(_7m));}),_7q=function(_7r){var _7s=E(_7r);if(!_7s[0]){return E(_7g);}else{var _7t=B(A(_7p,[_7s[1]]));if(!_7t[0]){return [0,_7t[1]];}else{var _7u=B(_7q(_7s[2]));return (_7u[0]==0)?[0,_7u[1]]:[1,[1,_7t[1],_7u[1]]];}}};return new F(function(){return _7q(_7o[1]);});}else{return E(_7i);}},_7v=function(_6J){return new F(function(){return _7l(_6m,_6J);});},_7w=[0,_65,_7c,_6h,_7v],_7x=function(_6J){return new F(function(){return _7l(_7w,_6J);});},_7y=[0,_7c,_7e,_7v,_7x],_7z=new T(function(){return B(_76(_7y,_7b));}),_7A=new T(function(){return B(unCStr("initial"));}),_7B=new T(function(){return B(_76(_7w,_7A));}),_7C=new T(function(){return B(unCStr("transition"));}),_7D=function(_6J){return new F(function(){return _5U(_7w,_6m,_7w,_6J);});},_7E=function(_7F){var _7G=E(_7F);return [3,[1,new T(function(){return B(_65(_7G[1]));}),[1,new T(function(){return B(_6k(_7G[2]));}),[1,new T(function(){return B(_65(_7G[3]));}),_I]]]];},_7H=function(_7I){return [3,E(B(_6B(_7E,_7I)))];},_7J=function(_7K){return [3,E(B(_6B(_7E,_7K)))];},_7L=function(_7M){return [3,E(B(_6B(_7J,_7M)))];},_7N=function(_7O,_7P,_7Q,_7R){var _7S=E(_7R);return [3,[1,new T(function(){return B(A(_6t,[_7O,_7S[1]]));}),[1,new T(function(){return B(A(_6t,[_7P,_7S[2]]));}),[1,new T(function(){return B(A(_6t,[_7Q,_7S[3]]));}),_I]]]];},_7T=function(_7U,_7V,_7W,_7X){return [3,E(B(_6B(function(_6J){return new F(function(){return _7N(_7U,_7V,_7W,_6J);});},_7X)))];},_7Y=function(_7Z,_80,_81){return [0,function(_6J){return new F(function(){return _7N(_7Z,_80,_81,_6J);});},function(_6J){return new F(function(){return _7T(_7Z,_80,_81,_6J);});},function(_6J){return new F(function(){return _5I(_7Z,_80,_81,_6J);});},function(_6J){return new F(function(){return _5U(_7Z,_80,_81,_6J);});}];},_82=new T(function(){return B(_7Y(_7w,_6m,_7w));}),_83=function(_6J){return new F(function(){return _7l(_82,_6J);});},_84=[0,_7H,_7L,_7D,_83],_85=new T(function(){return B(_76(_84,_7C));}),_86=new T(function(){return B(unCStr("alphabet"));}),_87=new T(function(){return B(_76(_7w,_86));}),_88=function(_89){var _8a=E(_89);if(_8a[0]==4){var _8b=E(_8a[1]);if(!_8b[0]){return E(_6s);}else{var _8c=B(_7l(_6m,E(_8b[1])[2]));return (_8c[0]==0)?[0,_8c[1]]:(E(_8b[2])[0]==0)?[1,[0,[1,_,[0,_8c[1]],_0]]]:E(_6p);}}else{return E(_6s);}},_8d=new T(function(){return B(unCStr("state"));}),_8e=new T(function(){return toJSStr(E(_8d));}),_8f=function(_8g){var _8h=E(_8g),_8i=E(_8h[3]);return new F(function(){return _g([1,[0,_8e,new T(function(){return [3,E(B(_6B(_65,E(_8h[2])[1])))];})],_I],_I);});},_8j=function(_8k){return [4,E(B(_8f(E(_8k)[1])))];},_8l=[0,_8j,_88],_8m=function(_8n,_8o){return [1,_,_8n,_8o];},_8p=function(_8q){return new F(function(){return _5B("Main.hs:(67,3)-(70,33)|function jsonToUnion");});},_8r=new T(function(){return B(_8p(_));}),_8s=function(_8t){return E(E(_8t)[2]);},_8u=function(_8v,_8w,_8x){var _8y=E(_8x);if(_8y[0]==4){var _8z=E(_8y[1]);if(!_8z[0]){return E(_8r);}else{var _8A=B(A(_5G,[_8w,[4,[1,_8z[1],_I]]]));if(!_8A[0]){return [0,_8A[1]];}else{var _8B=B(A(_8s,[_8v,new T(function(){return [4,E(_8z[2])];})]));return (_8B[0]==0)?[0,_8B[1]]:[1,[0,new T(function(){return B(_8m(_8A[1],E(_8B[1])[1]));})]];}}}else{return E(_8r);}},_8C=new T(function(){return B(unCStr("Monoid JSON: out of domain"));}),_8D=function(_8E){return new F(function(){return err(_8C);});},_8F=new T(function(){return B(_8D(_));}),_8G=function(_8H){return E(E(_8H)[1]);},_8I=function(_8J,_8K,_8L){var _8M=E(_8L),_8N=B(A(_6t,[_8K,_8M[2]]));if(_8N[0]==4){var _8O=B(A(_8G,[_8J,[0,_8M[3]]]));if(_8O[0]==4){return new F(function(){return _g(_8N[1],_8O[1]);});}else{return E(_8F);}}else{return E(_8F);}},_8P=function(_8Q,_8R,_8S){return [4,E(B(_8I(_8Q,_8R,E(_8S)[1])))];},_8T=function(_8U,_8V){return [0,function(_6J){return new F(function(){return _8P(_8U,_8V,_6J);});},function(_6J){return new F(function(){return _8u(_8U,_8V,_6J);});}];},_8W=new T(function(){return B(_8T(_8l,_87));}),_8X=new T(function(){return B(_8T(_8W,_85));}),_8Y=new T(function(){return B(_8T(_8X,_7B));}),_8Z=function(_90,_91){while(1){var _92=E(_90);if(!_92[0]){return (E(_91)[0]==0)?true:false;}else{var _93=E(_91);if(!_93[0]){return false;}else{if(!B(_4(_92[1],_93[1]))){return false;}else{_90=_92[2];_91=_93[2];continue;}}}}},_94=function(_95,_96){while(1){var _97=E(_95);if(!_97[0]){return (E(_96)[0]==0)?true:false;}else{var _98=E(_96);if(!_98[0]){return false;}else{if(E(_97[1])!=E(_98[1])){return false;}else{_95=_97[2];_96=_98[2];continue;}}}}},_99=function(_9a,_9b,_9c,_9d,_9e,_9f){return (!B(_94(_9a,_9d)))?true:(E(_9b)!=E(_9e))?true:(!B(_94(_9c,_9f)))?true:false;},_9g=function(_9h,_9i){var _9j=E(_9h),_9k=E(_9i);return new F(function(){return _99(_9j[1],_9j[2],_9j[3],_9k[1],_9k[2],_9k[3]);});},_9l=function(_9m,_9n,_9o,_9p,_9q,_9r){if(!B(_94(_9m,_9p))){return false;}else{if(E(_9n)!=E(_9q)){return false;}else{return new F(function(){return _94(_9o,_9r);});}}},_9s=function(_9t,_9u){var _9v=E(_9t),_9w=E(_9u);return new F(function(){return _9l(_9v[1],_9v[2],_9v[3],_9w[1],_9w[2],_9w[3]);});},_9x=[0,_9s,_9g],_9y=function(_9z,_9A){while(1){var _9B=E(_9A);if(!_9B[0]){return false;}else{if(!B(A(_9z,[_9B[1]]))){_9A=_9B[2];continue;}else{return true;}}}},_9C=function(_9D){return E(E(_9D)[1]);},_9E=function(_9F,_9G,_9H){while(1){var _9I=E(_9H);if(!_9I[0]){return false;}else{if(!B(A(_9C,[_9F,_9G,_9I[1]]))){_9H=_9I[2];continue;}else{return true;}}}},_9J=new T(function(){return B(_8Z(_I,_I));}),_9K=function(_9L,_9M){var _9N=new T(function(){return E(E(E(E(E(E(_9L)[1])[3])[3])[2])[1]);}),_9O=new T(function(){return E(E(E(E(E(E(E(E(_9L)[1])[3])[3])[3])[3])[2])[1]);}),_9P=function(_9Q,_9R){while(1){var _9S=B((function(_9T,_9U){var _9V=E(_9U);if(!_9V[0]){return E(_9T);}else{var _9W=new T(function(){var _9X=function(_9Y){var _9Z=E(_9Y);if(!_9Z[0]){return [0];}else{var _a0=_9Z[1],_a1=new T(function(){return B(_9X(_9Z[2]));}),_a2=function(_a3){while(1){var _a4=B((function(_a5){var _a6=E(_a5);if(!_a6[0]){return E(_a1);}else{var _a7=_a6[2];if(!B(_9E(_9x,[0,_a6[1],_9V[1],_a0],_9N))){_a3=_a7;return null;}else{return [1,_a0,new T(function(){return B(_a2(_a7));})];}}})(_a3));if(_a4!=null){return _a4;}}};return new F(function(){return _a2(_9T);});}};return B(_9X(_9O));});_9Q=_9W;_9R=_9V[2];return null;}})(_9Q,_9R));if(_9S!=null){return _9S;}}},_a8=B(_9P([1,new T(function(){return E(E(E(E(E(_9L)[1])[3])[2])[1]);}),_I],_9M));if(!_a8[0]){return (!E(_9J))?true:false;}else{var _a9=E(E(E(E(_9L)[1])[2])[1]);if(!_a9[0]){return (!E(_9J))?true:false;}else{var _aa=function(_ab){while(1){var _ac=B((function(_ad){var _ae=E(_ad);if(!_ae[0]){return [0];}else{var _af=_ae[1],_ag=_ae[2];if(!B(_9y(function(_6J){return new F(function(){return _94(_af,_6J);});},_a9))){_ab=_ag;return null;}else{return [1,_af,new T(function(){return B(_aa(_ag));})];}}})(_ab));if(_ac!=null){return _ac;}}},_ah=function(_ai,_aj){if(!B(_9y(function(_6J){return new F(function(){return _94(_ai,_6J);});},_a9))){return new F(function(){return _aa(_aj);});}else{return [1,_ai,new T(function(){return B(_aa(_aj));})];}};return (!B(_8Z(B(_ah(_a8[1],_a8[2])),_I)))?true:false;}}},_ak=new T(function(){return B(unCStr("</td>"));}),_al=new T(function(){return B(unCStr("</tr>"));}),_am=function(_an){var _ao=E(_an);if(!_ao[0]){return E(_al);}else{return new F(function(){return _g(B(unAppCStr("<td>",new T(function(){return B(_g(_ao[1],_ak));}))),new T(function(){return B(_am(_ao[2]));},1));});}},_ap=function(_aq,_ar){return new F(function(){return _g(B(unAppCStr("<td>",new T(function(){return B(_g(_aq,_ak));}))),new T(function(){return B(_am(_ar));},1));});},_as=function(_at){while(1){var _au=E(_at);if(!_au[0]){_at=[1,I_fromInt(_au[1])];continue;}else{return new F(function(){return I_toString(_au[1]);});}}},_av=function(_aw,_ax){return new F(function(){return _g(fromJSStr(B(_as(_aw))),_ax);});},_ay=function(_az,_aA){var _aB=E(_az);if(!_aB[0]){var _aC=_aB[1],_aD=E(_aA);return (_aD[0]==0)?_aC<_aD[1]:I_compareInt(_aD[1],_aC)>0;}else{var _aE=_aB[1],_aF=E(_aA);return (_aF[0]==0)?I_compareInt(_aE,_aF[1])<0:I_compare(_aE,_aF[1])<0;}},_aG=[0,0],_aH=function(_aI,_aJ,_aK){if(_aI<=6){return new F(function(){return _av(_aJ,_aK);});}else{if(!B(_ay(_aJ,_aG))){return new F(function(){return _av(_aJ,_aK);});}else{return [1,_p,new T(function(){return B(_g(fromJSStr(B(_as(_aJ))),[1,_o,_aK]));})];}}},_aL=[1,_I,_I],_aM=function(_aN){var _aO=E(_aN);if(!_aO[0]){return E(_aL);}else{var _aP=new T(function(){return B(_aM(_aO[2]));}),_aQ=function(_aR){var _aS=E(_aR);if(!_aS[0]){return [0];}else{var _aT=new T(function(){return B(_aQ(_aS[2]));}),_aU=function(_aV){var _aW=E(_aV);return (_aW[0]==0)?E(_aT):[1,[1,_aS[1],_aW[1]],new T(function(){return B(_aU(_aW[2]));})];};return new F(function(){return _aU(_aP);});}};return new F(function(){return _aQ(_aO[1]);});}},_aX=function(_aY,_aZ){if(0>=_aY){return E(_aL);}else{var _b0=function(_b1){var _b2=E(_b1);return (_b2==1)?[1,_aZ,_I]:[1,_aZ,new T(function(){return B(_b0(_b2-1|0));})];};return new F(function(){return _aM(B(_b0(_aY)));});}},_b3=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:255:7-14"));}),_b4=[0,_2E,_2F,_I,_b3,_2E,_2E],_b5=new T(function(){return B(_2C(_b4));}),_b6=function(_){return new F(function(){return die(_b5);});},_b7=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:276:7-14"));}),_b8=[0,_2E,_2F,_I,_b7,_2E,_2E],_b9=new T(function(){return B(_2C(_b8));}),_ba=function(_){return new F(function(){return die(_b9);});},_bb=",",_bc="[",_bd="]",_be="{",_bf="}",_bg=":",_bh="\"",_bi="true",_bj="false",_bk="null",_bl=new T(function(){return JSON.stringify;}),_bm=function(_bn,_bo){var _bp=E(_bo);switch(_bp[0]){case 0:return [0,new T(function(){return jsShow(_bp[1]);}),_bn];case 1:return [0,new T(function(){var _bq=E(_bl)(_bp[1]);return String(_bq);}),_bn];case 2:return (!E(_bp[1]))?[0,_bj,_bn]:[0,_bi,_bn];case 3:var _br=E(_bp[1]);if(!_br[0]){return [0,_bc,[1,_bd,_bn]];}else{var _bs=new T(function(){var _bt=new T(function(){var _bu=function(_bv){var _bw=E(_bv);if(!_bw[0]){return [1,_bd,_bn];}else{var _bx=new T(function(){var _by=B(_bm(new T(function(){return B(_bu(_bw[2]));}),_bw[1]));return [1,_by[1],_by[2]];});return [1,_bb,_bx];}};return B(_bu(_br[2]));}),_bz=B(_bm(_bt,_br[1]));return [1,_bz[1],_bz[2]];});return [0,_bc,_bs];}break;case 4:var _bA=E(_bp[1]);if(!_bA[0]){return [0,_be,[1,_bf,_bn]];}else{var _bB=E(_bA[1]),_bC=new T(function(){var _bD=new T(function(){var _bE=function(_bF){var _bG=E(_bF);if(!_bG[0]){return [1,_bf,_bn];}else{var _bH=E(_bG[1]),_bI=new T(function(){var _bJ=B(_bm(new T(function(){return B(_bE(_bG[2]));}),_bH[2]));return [1,_bJ[1],_bJ[2]];});return [1,_bb,[1,_bh,[1,_bH[1],[1,_bh,[1,_bg,_bI]]]]];}};return B(_bE(_bA[2]));}),_bK=B(_bm(_bD,_bB[2]));return [1,_bK[1],_bK[2]];});return [0,_be,[1,new T(function(){var _bL=E(_bl)(E(_bB[1]));return String(_bL);}),[1,_bg,_bC]]];}break;default:return [0,_bk,_bn];}},_bM=new T(function(){return toJSStr(_I);}),_bN=function(_bO){var _bP=B(_bm(_I,_bO)),_bQ=jsCat([1,_bP[1],_bP[2]],E(_bM));return E(_bQ);},_bR=0,_bS="state-table-tbody",_bT="add-state",_bU="word-table-tbody",_bV="example-table-tbody",_bW="conversion-table-tbody",_bX="alphabet-table-tbody",_bY="add-alphabet",_bZ="transition-table-tbody",_c0=new T(function(){return B(unCStr("] },  layout: {    name: \'cose\',    directed: true,    roots: \'#a\'  }  });   "));}),_c1="add-transition",_c2="export-button",_c3="import-button",_c4="accept-check-button",_c5="accept-check-result",_c6=function(_c7,_c8,_c9){var _ca=E(_c9);if(!_ca[0]){return [0];}else{var _cb=_ca[1],_cc=_ca[2];return (!B(A(_c7,[_c8,_cb])))?[1,_cb,new T(function(){return B(_c6(_c7,_c8,_cc));})]:E(_cc);}},_cd=(function(s){var x = eval(s);return (typeof x === 'undefined') ? 'undefined' : x.toString();}),_ce="value",_cf=(function(e,p){return e[p].toString();}),_cg=function(_ch){return E(E(_ch)[1]);},_ci=function(_cj){return E(E(_cj)[2]);},_ck=function(_cl){return new F(function(){return fromJSStr(E(_cl));});},_cm=function(_cn){return E(E(_cn)[1]);},_co=function(_cp){return E(E(_cp)[2]);},_cq=function(_cr,_cs,_ct,_cu){var _cv=new T(function(){var _cw=function(_){var _cx=E(_cf)(B(A(_cm,[_cr,_ct])),E(_cu));return new T(function(){return String(_cx);});};return E(_cw);});return new F(function(){return A(_co,[_cs,_cv]);});},_cy=function(_cz){return E(E(_cz)[4]);},_cA=function(_cB,_cC,_cD,_cE){var _cF=B(_cg(_cC)),_cG=new T(function(){return B(_cy(_cF));}),_cH=function(_cI){return new F(function(){return A(_cG,[new T(function(){return B(_ck(_cI));})]);});},_cJ=new T(function(){return B(_cq(_cB,_cC,_cD,new T(function(){return toJSStr(E(_cE));},1)));});return new F(function(){return A(_ci,[_cF,_cJ,_cH]);});},_cK=function(_cL){var _cM=E(_cL);if(!_cM[0]){return [0];}else{return new F(function(){return _g(_cM[1],new T(function(){return B(_cK(_cM[2]));},1));});}},_cN=(function(e,p,v){e[p] = v;}),_cO=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-transition\">\u8ffd\u52a0</button>"));}),_cP=[1,_cO,_I],_cQ=new T(function(){return B(unCStr("</select>"));}),_cR=new T(function(){return B(unCStr("</option>"));}),_cS=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:254:7-15"));}),_cT=[0,_2E,_2F,_I,_cS,_2E,_2E],_cU=new T(function(){return B(_2C(_cT));}),_cV=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:235:7-15"));}),_cW=[0,_2E,_2F,_I,_cV,_2E,_2E],_cX=new T(function(){return B(_2C(_cW));}),_cY=(function(id){return document.getElementById(id);}),_cZ=function(_d0,_d1){var _d2=function(_){var _d3=E(_cY)(E(_d1)),_d4=__eq(_d3,E(_31));return (E(_d4)==0)?[1,_d3]:_2E;};return new F(function(){return A(_co,[_d0,_d2]);});},_d5="accept-check-text",_d6=new T(function(){return B(_cZ(_4a,_d5));}),_d7=new T(function(){return B(unCStr(">"));}),_d8=new T(function(){return B(unCStr(" checked=\"checked\""));}),_d9=new T(function(){return B(_g(_d8,_d7));}),_da=new T(function(){return B(unCStr("\'#494\'}}"));}),_db=new T(function(){return B(unCStr("\'#c4f\'}}"));}),_dc=new T(function(){return B(unCStr("\'#f94\'}}"));}),_dd=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_de=function(_df){return new F(function(){return _5c([0,new T(function(){return B(_5q(_df,_dd));})],_4U);});},_dg=new T(function(){return B(_de("Main.hs:293:11-64|Right auto"));}),_dh="import-text",_di=new T(function(){return B(_cZ(_4a,_dh));}),_dj=new T(function(){return B(unCStr("innerText"));}),_dk=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:286:7-12"));}),_dl="export-text",_dm=new T(function(){return B(_cZ(_4a,_dl));}),_dn="select-target",_do=new T(function(){return B(_cZ(_4a,_dn));}),_dp="select-alphabet",_dq=new T(function(){return B(_cZ(_4a,_dp));}),_dr="select-source",_ds=new T(function(){return B(_cZ(_4a,_dr));}),_dt=function(_du,_dv){while(1){var _dw=E(_du);if(!_dw[0]){var _dx=_dw[1],_dy=E(_dv);if(!_dy[0]){var _dz=_dy[1],_dA=addC(_dx,_dz);if(!E(_dA[2])){return [0,_dA[1]];}else{_du=[1,I_fromInt(_dx)];_dv=[1,I_fromInt(_dz)];continue;}}else{_du=[1,I_fromInt(_dx)];_dv=_dy;continue;}}else{var _dB=E(_dv);if(!_dB[0]){_du=_dw;_dv=[1,I_fromInt(_dB[1])];continue;}else{return [1,I_add(_dw[1],_dB[1])];}}}},_dC=function(_dD,_dE){var _dF=E(_dD);return [0,_dF,new T(function(){var _dG=B(_dC(B(_dt(_dF,_dE)),_dE));return [1,_dG[1],_dG[2]];})];},_dH=[0,1],_dI=new T(function(){var _dJ=B(_dC(_dH,_dH));return [1,_dJ[1],_dJ[2]];}),_dK=new T(function(){return B(unCStr("\">\u524a\u9664</button>"));}),_dL=new T(function(){return B(unCStr("select-target"));}),_dM=new T(function(){return B(unCStr("select-source"));}),_dN="new-alphabet",_dO=new T(function(){return B(_cZ(_4a,_dN));}),_dP="new-state",_dQ=new T(function(){return B(_cZ(_4a,_dP));}),_dR=new T(function(){return B(_5B("Main.hs:(228,9)-(230,58)|case"));}),_dS=new T(function(){return B(unCStr("true"));}),_dT=new T(function(){return B(unCStr("false"));}),_dU=new T(function(){return B(unCStr("checked"));}),_dV=new T(function(){return B(unCStr(","));}),_dW=34,_dX=[1,_dW,_I],_dY=new T(function(){return B(unCStr("!!: negative index"));}),_dZ=new T(function(){return B(unCStr("Prelude."));}),_e0=new T(function(){return B(_g(_dZ,_dY));}),_e1=new T(function(){return B(err(_e0));}),_e2=new T(function(){return B(unCStr("!!: index too large"));}),_e3=new T(function(){return B(_g(_dZ,_e2));}),_e4=new T(function(){return B(err(_e3));}),_e5=function(_e6,_e7){while(1){var _e8=E(_e6);if(!_e8[0]){return E(_e4);}else{var _e9=E(_e7);if(!_e9){return E(_e8[1]);}else{_e6=_e8[2];_e7=_e9-1|0;continue;}}}},_ea=function(_eb,_ec){if(_ec>=0){return new F(function(){return _e5(_eb,_ec);});}else{return E(_e1);}},_ed=new T(function(){return B(unCStr("ACK"));}),_ee=new T(function(){return B(unCStr("BEL"));}),_ef=new T(function(){return B(unCStr("BS"));}),_eg=new T(function(){return B(unCStr("SP"));}),_eh=[1,_eg,_I],_ei=new T(function(){return B(unCStr("US"));}),_ej=[1,_ei,_eh],_ek=new T(function(){return B(unCStr("RS"));}),_el=[1,_ek,_ej],_em=new T(function(){return B(unCStr("GS"));}),_en=[1,_em,_el],_eo=new T(function(){return B(unCStr("FS"));}),_ep=[1,_eo,_en],_eq=new T(function(){return B(unCStr("ESC"));}),_er=[1,_eq,_ep],_es=new T(function(){return B(unCStr("SUB"));}),_et=[1,_es,_er],_eu=new T(function(){return B(unCStr("EM"));}),_ev=[1,_eu,_et],_ew=new T(function(){return B(unCStr("CAN"));}),_ex=[1,_ew,_ev],_ey=new T(function(){return B(unCStr("ETB"));}),_ez=[1,_ey,_ex],_eA=new T(function(){return B(unCStr("SYN"));}),_eB=[1,_eA,_ez],_eC=new T(function(){return B(unCStr("NAK"));}),_eD=[1,_eC,_eB],_eE=new T(function(){return B(unCStr("DC4"));}),_eF=[1,_eE,_eD],_eG=new T(function(){return B(unCStr("DC3"));}),_eH=[1,_eG,_eF],_eI=new T(function(){return B(unCStr("DC2"));}),_eJ=[1,_eI,_eH],_eK=new T(function(){return B(unCStr("DC1"));}),_eL=[1,_eK,_eJ],_eM=new T(function(){return B(unCStr("DLE"));}),_eN=[1,_eM,_eL],_eO=new T(function(){return B(unCStr("SI"));}),_eP=[1,_eO,_eN],_eQ=new T(function(){return B(unCStr("SO"));}),_eR=[1,_eQ,_eP],_eS=new T(function(){return B(unCStr("CR"));}),_eT=[1,_eS,_eR],_eU=new T(function(){return B(unCStr("FF"));}),_eV=[1,_eU,_eT],_eW=new T(function(){return B(unCStr("VT"));}),_eX=[1,_eW,_eV],_eY=new T(function(){return B(unCStr("LF"));}),_eZ=[1,_eY,_eX],_f0=new T(function(){return B(unCStr("HT"));}),_f1=[1,_f0,_eZ],_f2=[1,_ef,_f1],_f3=[1,_ee,_f2],_f4=[1,_ed,_f3],_f5=new T(function(){return B(unCStr("ENQ"));}),_f6=[1,_f5,_f4],_f7=new T(function(){return B(unCStr("EOT"));}),_f8=[1,_f7,_f6],_f9=new T(function(){return B(unCStr("ETX"));}),_fa=[1,_f9,_f8],_fb=new T(function(){return B(unCStr("STX"));}),_fc=[1,_fb,_fa],_fd=new T(function(){return B(unCStr("SOH"));}),_fe=[1,_fd,_fc],_ff=new T(function(){return B(unCStr("NUL"));}),_fg=[1,_ff,_fe],_fh=92,_fi=new T(function(){return B(unCStr("\\DEL"));}),_fj=new T(function(){return B(unCStr("\\a"));}),_fk=new T(function(){return B(unCStr("\\\\"));}),_fl=new T(function(){return B(unCStr("\\SO"));}),_fm=new T(function(){return B(unCStr("\\r"));}),_fn=new T(function(){return B(unCStr("\\f"));}),_fo=new T(function(){return B(unCStr("\\v"));}),_fp=new T(function(){return B(unCStr("\\n"));}),_fq=new T(function(){return B(unCStr("\\t"));}),_fr=new T(function(){return B(unCStr("\\b"));}),_fs=function(_ft,_fu){if(_ft<=127){var _fv=E(_ft);switch(_fv){case 92:return new F(function(){return _g(_fk,_fu);});break;case 127:return new F(function(){return _g(_fi,_fu);});break;default:if(_fv<32){var _fw=E(_fv);switch(_fw){case 7:return new F(function(){return _g(_fj,_fu);});break;case 8:return new F(function(){return _g(_fr,_fu);});break;case 9:return new F(function(){return _g(_fq,_fu);});break;case 10:return new F(function(){return _g(_fp,_fu);});break;case 11:return new F(function(){return _g(_fo,_fu);});break;case 12:return new F(function(){return _g(_fn,_fu);});break;case 13:return new F(function(){return _g(_fm,_fu);});break;case 14:return new F(function(){return _g(_fl,new T(function(){var _fx=E(_fu);if(!_fx[0]){return [0];}else{if(E(_fx[1])==72){return B(unAppCStr("\\&",_fx));}else{return E(_fx);}}},1));});break;default:return new F(function(){return _g([1,_fh,new T(function(){return B(_ea(_fg,_fw));})],_fu);});}}else{return [1,_fv,_fu];}}}else{var _fy=new T(function(){var _fz=jsShowI(_ft);return B(_g(fromJSStr(_fz),new T(function(){var _fA=E(_fu);if(!_fA[0]){return [0];}else{var _fB=E(_fA[1]);if(_fB<48){return E(_fA);}else{if(_fB>57){return E(_fA);}else{return B(unAppCStr("\\&",_fA));}}}},1)));});return [1,_fh,_fy];}},_fC=39,_fD=[1,_fC,_I],_fE=new T(function(){return B(unCStr("}}"));}),_fF=new T(function(){return B(unCStr("\'\\\'\'"));}),_fG=new T(function(){return B(_g(_fF,_I));}),_fH=new T(function(){return B(unCStr("\\\""));}),_fI=function(_fJ,_fK){var _fL=E(_fJ);if(!_fL[0]){return E(_fK);}else{var _fM=_fL[2],_fN=E(_fL[1]);if(_fN==34){return new F(function(){return _g(_fH,new T(function(){return B(_fI(_fM,_fK));},1));});}else{return new F(function(){return _fs(_fN,new T(function(){return B(_fI(_fM,_fK));}));});}}},_fO=function(_fP,_fQ,_fR){var _fS=new T(function(){var _fT=new T(function(){var _fU=new T(function(){var _fV=new T(function(){var _fW=new T(function(){var _fX=E(_fQ);if(_fX==39){return B(_g(_fG,_fE));}else{return B(_g([1,_fC,new T(function(){return B(_fs(_fX,_fD));})],_fE));}});return B(unAppCStr(", label: ",_fW));},1);return B(_g([1,_dW,new T(function(){return B(_fI(_fR,_dX));})],_fV));});return B(unAppCStr(", target: ",_fU));},1);return B(_g([1,_dW,new T(function(){return B(_fI(_fP,_dX));})],_fT));});return new F(function(){return unAppCStr("{data: {source: ",_fS);});},_fY=function(_fZ){var _g0=E(_fZ);return new F(function(){return _fO(_g0[1],_g0[2],_g0[3]);});},_g1=new T(function(){return B(unCStr("{\"final\":[\"q0\",\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"0\",\"q0\"],[\"q0\",\"1\",\"q1\"],[\"q1\",\"1\",\"q0\"],[\"q1\",\"0\",\"q2\"],[\"q2\",\"0\",\"q1\"],[\"q2\",\"1\",\"q2\"]],\"alphabet\":\"01\",\"state\":[\"q0\",\"q1\",\"q2\"]}"));}),_g2=new T(function(){return B(unCStr("DFA"));}),_g3=new T(function(){return B(unCStr("multiple of 3"));}),_g4=[0,_g3,_g2,_g1],_g5=[1,_g4,_I],_g6=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"a\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q1\",\"b\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_g7=new T(function(){return B(unCStr("NFA"));}),_g8=new T(function(){return B(unCStr("worst NFAtoDFA efficiency"));}),_g9=[0,_g8,_g7,_g6],_ga=[1,_g9,_g5],_gb=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"b\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_gc=new T(function(){return B(unCStr("exmple2"));}),_gd=[0,_gc,_g7,_gb],_ge=[1,_gd,_ga],_gf=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q1\"],[\"q0\",\"b\",\"q2\"],[\"q1\",\"a\",\"q3\"],[\"q2\",\"a\",\"q2\"],[\"q2\",\"b\",\"q3\"],[\"q3\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_gg=new T(function(){return B(unCStr("exmple1"));}),_gh=[0,_gg,_g7,_gf],_gi=[1,_gh,_ge],_gj=function(_gk,_gl,_gm){var _gn=E(_gl);return new F(function(){return A(_gk,[_gn,new T(function(){return B(_gj(_gk,B(_dt(_gn,_gm)),_gm));})]);});},_go=function(_gp,_gq,_gr){var _gs=E(_gr);return (_gs[0]==0)?[0]:[1,[0,_gp,_gs[1]],new T(function(){return B(A(_gq,[_gs[2]]));})];},_gt=new T(function(){return B(_gj(_go,_dH,_dH));}),_gu=new T(function(){return B(A(_gt,[_gi]));}),_gv=new T(function(){return B(unCStr("innerHTML"));}),_gw=new T(function(){return B(unCStr("]"));}),_gx=function(_gy,_gz){var _gA=E(_gz);return (_gA[0]==0)?[0]:[1,_gy,[1,_gA[1],new T(function(){return B(_gx(_gy,_gA[2]));})]];},_gB=function(_gC){var _gD=new T(function(){var _gE=E(_gC);if(!_gE[0]){return E(_gw);}else{return B(_g(B(_cK([1,_gE[1],new T(function(){return B(_gx(_dV,_gE[2]));})])),_gw));}});return new F(function(){return unAppCStr("[",_gD);});},_gF=function(_gG){var _gH=E(_gG);return [0,new T(function(){return B(_gB(_gH[1]));}),_gH[2],new T(function(){return B(_gB(_gH[3]));})];},_gI=new T(function(){return B(unCStr("\">Load</button>"));}),_gJ=function(_gK,_gL,_gM){var _gN=E(_gM);if(!_gN[0]){return [0];}else{var _gO=new T(function(){var _gP=E(_gN[1]),_gQ=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"load-",new T(function(){return B(_g(B(_aH(0,_gK,_I)),_gI));})));});return B(_ap(_gP[1],[1,_gP[2],[1,_gQ,_I]]));});return new F(function(){return _g(B(unAppCStr("<tr>",_gO)),new T(function(){return B(A(_gL,[_gN[2]]));},1));});}},_gR=new T(function(){return B(_gj(_gJ,_dH,_dH));}),_gS=function(_gT){var _gU=E(_gT);return [0,_gU[1],_gU[2]];},_gV=new T(function(){return B(_6B(_gS,_gi));}),_gW=new T(function(){return B(A(_gR,[_gV]));}),_gX=new T(function(){return B(_de("Main.hs:321:15-68|Right auto"));}),_gY=new T(function(){return B(unCStr("\">Go</button>"));}),_gZ=function(_h0,_h1,_h2){var _h3=E(_h2);if(!_h3[0]){return [0];}else{var _h4=new T(function(){var _h5=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"convert-",new T(function(){return B(_g(B(_aH(0,_h0,_I)),_gY));})));});return B(_ap(_h3[1],[1,_h5,_I]));});return new F(function(){return _g(B(unAppCStr("<tr>",_h4)),new T(function(){return B(A(_h1,[_h3[2]]));},1));});}},_h6=new T(function(){return B(_gj(_gZ,_dH,_dH));}),_h7=new T(function(){return B(unCStr("NFAtoDFA"));}),_h8=function(_h9,_ha,_hb){while(1){var _hc=E(_ha);if(!_hc[0]){return (E(_hb)[0]==0)?true:false;}else{var _hd=E(_hb);if(!_hd[0]){return false;}else{if(!B(A(_9C,[_h9,_hc[1],_hd[1]]))){return false;}else{_ha=_hc[2];_hb=_hd[2];continue;}}}}},_he=function(_hf,_hg,_hh){return (!B(_h8(_hf,_hg,_hh)))?true:false;},_hi=function(_hj){return [0,function(_hk,_hl){return new F(function(){return _h8(_hj,_hk,_hl);});},function(_hk,_hl){return new F(function(){return _he(_hj,_hk,_hl);});}];},_hm=function(_hn){return E(E(_hn)[1]);},_ho=function(_hp,_hq,_hr){while(1){var _hs=E(_hr);if(!_hs[0]){return false;}else{if(!B(A(_hp,[_hs[1],_hq]))){_hr=_hs[2];continue;}else{return true;}}}},_ht=function(_hu,_hv){var _hw=function(_hx,_hy){while(1){var _hz=B((function(_hA,_hB){var _hC=E(_hA);if(!_hC[0]){return [0];}else{var _hD=_hC[1],_hE=_hC[2];if(!B(_ho(_hu,_hD,_hB))){return [1,_hD,new T(function(){return B(_hw(_hE,[1,_hD,_hB]));})];}else{var _hF=_hB;_hx=_hE;_hy=_hF;return null;}}})(_hx,_hy));if(_hz!=null){return _hz;}}};return new F(function(){return _hw(_hv,_I);});},_hG=function(_hH,_hI,_hJ,_hK){var _hL=function(_hM){while(1){var _hN=B((function(_hO){var _hP=E(_hO);if(!_hP[0]){return [0];}else{var _hQ=_hP[2],_hR=E(_hP[1]);if(!B(_9E(_hH,_hR[1],_hJ))){_hM=_hQ;return null;}else{var _hS=E(_hK);if(_hS!=E(_hR[2])){var _hT=function(_hU){while(1){var _hV=B((function(_hW){var _hX=E(_hW);if(!_hX[0]){return [0];}else{var _hY=_hX[2],_hZ=E(_hX[1]);if(!B(_9E(_hH,_hZ[1],_hJ))){_hU=_hY;return null;}else{if(_hS!=E(_hZ[2])){_hU=_hY;return null;}else{return [1,_hZ[3],new T(function(){return B(_hT(_hY));})];}}}})(_hU));if(_hV!=null){return _hV;}}};return new F(function(){return _hT(_hQ);});}else{var _i0=new T(function(){var _i1=function(_i2){while(1){var _i3=B((function(_i4){var _i5=E(_i4);if(!_i5[0]){return [0];}else{var _i6=_i5[2],_i7=E(_i5[1]);if(!B(_9E(_hH,_i7[1],_hJ))){_i2=_i6;return null;}else{if(_hS!=E(_i7[2])){_i2=_i6;return null;}else{return [1,_i7[3],new T(function(){return B(_i1(_i6));})];}}}})(_i2));if(_i3!=null){return _i3;}}};return B(_i1(_hQ));});return [1,_hR[3],_i0];}}}})(_hM));if(_hN!=null){return _hN;}}};return new F(function(){return _ht(new T(function(){return B(_9C(_hH));}),B(_hL(E(E(E(E(_hI)[3])[3])[2])[1])));});},_i8=function(_i9,_ia,_ib,_ic){return new F(function(){return _hG(_i9,E(_ia)[1],_ib,_ic);});},_id=function(_ie,_if,_ig){var _ih=E(_if);if(!_ih[0]){return [0];}else{var _ii=E(_ig);if(!_ii[0]){return [0];}else{var _ij=function(_ik){while(1){var _il=B((function(_im){var _in=E(_im);if(!_in[0]){return [0];}else{var _io=_in[1],_ip=_in[2];if(!B(_9y(new T(function(){return B(A(_ie,[_io]));}),_ii))){_ik=_ip;return null;}else{return [1,_io,new T(function(){return B(_ij(_ip));})];}}})(_ik));if(_il!=null){return _il;}}};return new F(function(){return _ij(_ih);});}}},_iq=function(_ir){var _is=new T(function(){return B(_hm(_ir));}),_it=new T(function(){return B(_hi(_is));}),_iu=new T(function(){return B(_9C(_is));}),_iv=function(_iw,_ix){var _iy=E(_iw),_iz=E(_ix);if(!B(_h8(_is,_iy[1],_iz[1]))){return false;}else{if(E(_iy[2])!=E(_iz[2])){return false;}else{return new F(function(){return _h8(_is,_iy[3],_iz[3]);});}}},_iA=function(_iB,_6J){return new F(function(){return _h8(_is,_iB,_6J);});},_iC=function(_iD){var _iE=new T(function(){var _iF=new T(function(){return E(E(E(E(E(E(E(_iD)[1])[3])[3])[3])[2])[1]);}),_iG=new T(function(){return E(E(E(E(_iD)[1])[2])[1]);}),_iH=function(_iI,_iJ,_iK,_iL){while(1){var _iM=B((function(_iN,_iO,_iP,_iQ){var _iR=E(_iN);if(!_iR[0]){return [0,_iO,_iP,_iQ];}else{var _iS=_iR[1],_iT=[1,_iS,_iO],_iU=function(_iV){while(1){var _iW=B((function(_iX){var _iY=E(_iX);if(!_iY[0]){return E(_iR[2]);}else{var _iZ=_iY[1],_j0=_iY[2];if(!B(_9E(_it,new T(function(){return B(_hG(_is,E(_iD)[1],_iS,_iZ));}),_iT))){return [1,new T(function(){return B(_i8(_is,_iD,_iS,_iZ));}),new T(function(){return B(_iU(_j0));})];}else{_iV=_j0;return null;}}})(_iV));if(_iW!=null){return _iW;}}},_j1=new T(function(){var _j2=function(_j3){var _j4=E(_j3);if(!_j4[0]){return E(_iP);}else{var _j5=_j4[1];return [1,[0,_iS,_j5,new T(function(){return B(_i8(_is,_iD,_iS,_j5));})],new T(function(){return B(_j2(_j4[2]));})];}};return B(_ht(_iv,B(_j2(_iF))));});_iI=B(_ht(_iA,B(_iU(_iF))));_iJ=_iT;_iK=_j1;_iL=new T(function(){if(!B(_h8(_is,B(_id(_iu,_iS,_iG)),_I))){return [1,_iS,_iQ];}else{return E(_iQ);}});return null;}})(_iI,_iJ,_iK,_iL));if(_iM!=null){return _iM;}}},_j6=function(_j7,_j8,_j9,_ja,_jb){var _jc=[1,_j7,_j9],_jd=function(_je){while(1){var _jf=B((function(_jg){var _jh=E(_jg);if(!_jh[0]){return E(_j8);}else{var _ji=_jh[1],_jj=_jh[2];if(!B(_9E(_it,new T(function(){return B(_hG(_is,E(_iD)[1],_j7,_ji));}),_jc))){return [1,new T(function(){return B(_i8(_is,_iD,_j7,_ji));}),new T(function(){return B(_jd(_jj));})];}else{_je=_jj;return null;}}})(_je));if(_jf!=null){return _jf;}}},_jk=new T(function(){var _jl=function(_jm){var _jn=E(_jm);if(!_jn[0]){return E(_ja);}else{var _jo=_jn[1];return [1,[0,_j7,_jo,new T(function(){return B(_i8(_is,_iD,_j7,_jo));})],new T(function(){return B(_jl(_jn[2]));})];}};return B(_ht(_iv,B(_jl(_iF))));});return new F(function(){return _iH(B(_ht(_iA,B(_jd(_iF)))),_jc,_jk,new T(function(){if(!B(_h8(_is,B(_id(_iu,_j7,_iG)),_I))){return [1,_j7,_jb];}else{return E(_jb);}}));});},_jp=B(_j6([1,new T(function(){return E(E(E(E(E(_iD)[1])[3])[2])[1]);}),_I],_I,_I,_I,_I));return [0,_jp[1],_jp[2],_jp[3]];});return [0,[1,_,[0,new T(function(){return E(E(_iE)[3]);})],[1,_,[0,[1,new T(function(){return E(E(E(E(E(_iD)[1])[3])[2])[1]);}),_I]],[1,_,[0,new T(function(){return E(E(_iE)[2]);})],[1,_,[0,new T(function(){return E(E(E(E(E(E(E(_iD)[1])[3])[3])[3])[2])[1]);})],[1,_,[0,new T(function(){return E(E(_iE)[1]);})],_0]]]]]];};return E(_iC);},_jq=function(_jr,_js){return new F(function(){return _iq(_js);});},_jt=[0,_h7,_jq],_ju=[1,_jt,_I],_jv=function(_jw){return E(E(_jw)[1]);},_jx=new T(function(){return B(_6B(_jv,_ju));}),_jy=new T(function(){return B(A(_h6,[_jx]));}),_jz=function(_jA,_jB,_jC){var _jD=E(_jC);return (_jD[0]==0)?[0]:[1,[0,_jA,_jD[1]],new T(function(){return B(A(_jB,[_jD[2]]));})];},_jE=new T(function(){return B(_gj(_jz,_dH,_dH));}),_jF=new T(function(){return B(A(_jE,[_ju]));}),_jG=new T(function(){return B(unCStr("<span class=\"label label-success\">O</span>"));}),_jH=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:299:7-12"));}),_jI=[0,_2E,_2F,_I,_jH,_2E,_2E],_jJ=new T(function(){return B(_2C(_jI));}),_jK=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:291:7-12"));}),_jL=[0,_2E,_2F,_I,_jK,_2E,_2E],_jM=new T(function(){return B(_2C(_jL));}),_jN=new T(function(){return B(unCStr("<span class=\"label label-danger\">X</span>"));}),_jO=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:278:7-15"));}),_jP=[0,_2E,_2F,_I,_jO,_2E,_2E],_jQ=new T(function(){return B(_2C(_jP));}),_jR=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:275:7-15"));}),_jS=[0,_2E,_2F,_I,_jR,_2E,_2E],_jT=new T(function(){return B(_2C(_jS));}),_jU=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:272:7-15"));}),_jV=[0,_2E,_2F,_I,_jU,_2E,_2E],_jW=new T(function(){return B(_2C(_jV));}),_jX=function(_jY,_jZ){var _k0=E(_jY),_k1=E(_jZ);if(!B(_94(_k0[1],_k1[1]))){return false;}else{if(E(_k0[2])!=E(_k1[2])){return false;}else{return new F(function(){return _94(_k0[3],_k1[3]);});}}},_k2=function(_k3){return E(E(_k3)[1]);},_k4=function(_k5){return E(E(_k5)[2]);},_k6=function(_k7){return E(E(_k7)[1]);},_k8=function(_){return new F(function(){return nMV(_2E);});},_k9=new T(function(){return B(_2X(_k8));}),_ka=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_kb=function(_kc){return E(E(_kc)[2]);},_kd=function(_ke,_kf,_kg,_kh,_ki,_kj){var _kk=B(_k2(_ke)),_kl=B(_cg(_kk)),_km=new T(function(){return B(_co(_kk));}),_kn=new T(function(){return B(_cy(_kl));}),_ko=new T(function(){return B(A(_cm,[_kf,_kh]));}),_kp=new T(function(){return B(A(_k6,[_kg,_ki]));}),_kq=function(_kr){return new F(function(){return A(_kn,[[0,_kp,_ko,_kr]]);});},_ks=function(_kt){var _ku=new T(function(){var _kv=new T(function(){var _kw=__createJSFunc(2,function(_kx,_){var _ky=B(A(E(_kt),[_kx,_]));return _31;}),_kz=_kw;return function(_){return new F(function(){return E(_ka)(E(_ko),E(_kp),_kz);});};});return B(A(_km,[_kv]));});return new F(function(){return A(_ci,[_kl,_ku,_kq]);});},_kA=new T(function(){var _kB=new T(function(){return B(_co(_kk));}),_kC=function(_kD){var _kE=new T(function(){return B(A(_kB,[function(_){var _=wMV(E(_k9),[1,_kD]);return new F(function(){return A(_k4,[_kg,_ki,_kD,_]);});}]));});return new F(function(){return A(_ci,[_kl,_kE,_kj]);});};return B(A(_kb,[_ke,_kC]));});return new F(function(){return A(_ci,[_kl,_kA,_ks]);});},_kF=new T(function(){return B(unCStr(" found!"));}),_kG=function(_kH){return new F(function(){return err(B(unAppCStr("No element with ID ",new T(function(){return B(_g(fromJSStr(E(_kH)),_kF));}))));});},_kI=function(_kJ,_kK,_kL){var _kM=new T(function(){var _kN=function(_){var _kO=E(_cY)(E(_kK)),_kP=__eq(_kO,E(_31));return (E(_kP)==0)?[1,_kO]:_2E;};return B(A(_co,[_kJ,_kN]));});return new F(function(){return A(_ci,[B(_cg(_kJ)),_kM,function(_kQ){var _kR=E(_kQ);if(!_kR[0]){return new F(function(){return _kG(_kK);});}else{return new F(function(){return A(_kL,[_kR[1]]);});}}]);});},_kS=new T(function(){return B(unCStr("<input type=\"text\" class=\"form-control input-sm\" id=\"new-alphabet\">"));}),_kT=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-alphabet\">\u8ffd\u52a0</button>"));}),_kU=[1,_kT,_I],_kV=new T(function(){return B(_ap(_kS,_kU));}),_kW=new T(function(){return B(unAppCStr("<tr>",_kV));}),_kX=new T(function(){return B(_g(_kW,_I));}),_kY=new T(function(){return B(unCStr("<input type=\"text\" class=\"form-control input-sm\" id=\"new-state\">"));}),_kZ=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-state\">\u8ffd\u52a0</button>"));}),_l0=[1,_kZ,_I],_l1=new T(function(){return B(_ap(_kY,_l0));}),_l2=new T(function(){return B(unAppCStr("<tr>",_l1));}),_l3=new T(function(){return B(_g(_l2,_I));}),_l4=function(_l5,_){var _l6=rMV(_l5),_l7=new T(function(){var _l8=E(E(_l6)[1]),_l9=E(_l8[3]),_la=E(_l9[3]),_lb=new T(function(){var _lc=new T(function(){var _ld=B(_6B(_fY,E(_la[2])[1]));if(!_ld[0]){return E(_c0);}else{return B(_g(B(_cK([1,_ld[1],new T(function(){return B(_gx(_dV,_ld[2]));})])),_c0));}});return B(unAppCStr("], edges: [",_lc));}),_le=function(_lf){var _lg=new T(function(){var _lh=new T(function(){var _li=new T(function(){var _lj=new T(function(){return B(unAppCStr(", color: ",new T(function(){if(!B(_9E(_c,_lf,E(_l8[2])[1]))){if(!B(_94(_lf,E(_l9[2])[1]))){return E(_dc);}else{return E(_db);}}else{return E(_da);}})));},1);return B(_g([1,_dW,new T(function(){return B(_fI(_lf,_dX));})],_lj));});return B(unAppCStr(", id: ",_li));},1);return B(_g([1,_dW,new T(function(){return B(_fI(_lf,_dX));})],_lh));});return new F(function(){return unAppCStr("{data: {label: ",_lg);});},_lk=B(_6B(_le,E(E(E(_la[3])[3])[2])[1]));if(!_lk[0]){return E(_lb);}else{return B(_g(B(_cK([1,_lk[1],new T(function(){return B(_gx(_dV,_lk[2]));})])),_lb));}}),_ll=E(_cd)(toJSStr(B(unAppCStr("  var cy = cytoscape({  container: document.getElementById(\'cy\'),  style: cytoscape.stylesheet()    .selector(\'node\').css({      \'background-color\': \'data(color)\',      \'text-valign\': \'center\',      \'content\': \'data(id)\'    })    .selector(\'edge\').css({      \'target-arrow-shape\': \'triangle\',      \'line-color\': \'#a9f\',      \'target-arrow-color\': \'#a9f\',      \'text-valign\': \'top\',      \'width\': 3,      \'content\': \'data(label)\'    }),  elements: { nodes: [",_l7)))),_lm=function(_ln,_){var _lo=rMV(_l5),_lp=new T(function(){return E(E(E(E(_lo)[1])[2])[1]);}),_lq=function(_lr,_ls){var _lt=E(_lr);if(!_lt[0]){return E(_l3);}else{var _lu=_lt[1],_lv=E(_ls);if(!_lv[0]){return E(_l3);}else{var _lw=_lv[1],_lx=new T(function(){var _ly=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-state-",new T(function(){return B(_g(B(_aH(0,_lu,_I)),_dK));})));}),_lz=new T(function(){var _lA=new T(function(){var _lB=new T(function(){return B(unAppCStr("\"",new T(function(){if(!B(_9E(_c,_lw,_lp))){return E(_d7);}else{return E(_d9);}})));},1);return B(_g(B(_aH(0,_lu,_I)),_lB));});return B(unAppCStr("<input type=\"checkbox\" id=\"state-final-",_lA));});return B(_ap(_lw,[1,_lz,[1,_ly,_I]]));});return new F(function(){return _g(B(unAppCStr("<tr>",_lx)),new T(function(){return B(_lq(_lt[2],_lv[2]));},1));});}}},_lC=E(_cN)(E(_ln),toJSStr(E(_gv)),toJSStr(B(_lq(_dI,new T(function(){return E(E(E(E(E(E(E(E(_lo)[1])[3])[3])[3])[3])[2])[1]);},1)))));return new F(function(){return _3u(_);});},_lD=B(A(_kI,[_4a,_bS,_lm,_])),_lE=rMV(_l5),_lF=function(_lG,_lH,_){while(1){var _lI=B((function(_lJ,_lK,_){var _lL=E(_lJ);if(!_lL[0]){return _3t;}else{var _lM=_lL[1],_lN=E(_lK);if(!_lN[0]){return _3t;}else{var _lO=_lN[1],_lP=function(_){var _lQ=rMV(_l5),_lR=[0,new T(function(){var _lS=E(E(_lQ)[1]),_lT=new T(function(){var _lU=E(_lS[3]),_lV=new T(function(){var _lW=E(_lU[3]),_lX=new T(function(){var _lY=E(_lW[3]),_lZ=new T(function(){var _m0=E(_lY[3]);return [1,_,[0,new T(function(){return B(_c6(_94,_lO,E(_m0[2])[1]));})],_m0[3]];});return [1,_,_lY[2],_lZ];});return [1,_,_lW[2],_lX];});return [1,_,_lU[2],_lV];});return [1,_,_lS[2],_lT];})],_=wMV(_l5,_lR);return new F(function(){return _l4(_l5,_);});},_m1=function(_m2,_){return new F(function(){return _lP(_);});},_m3=new T(function(){return toJSStr(B(unAppCStr("delete-state-",new T(function(){return B(_aH(0,_lM,_I));}))));}),_m4=B(A(_kI,[_4a,_m3,function(_m5){return new F(function(){return _kd(_4b,_3z,_3s,_m5,_bR,_m1);});},_])),_m6=function(_m7){var _m8=function(_m9,_){var _ma=B(A(_cA,[_3z,_4a,_m7,_dU,_]));if(!B(_94(_ma,_dT))){if(!B(_94(_ma,_dS))){return E(_dR);}else{var _mb=rMV(_l5),_mc=[0,new T(function(){var _md=E(E(_mb)[1]);return [1,_,[0,[1,_lO,new T(function(){return E(E(_md[2])[1]);})]],_md[3]];})],_=wMV(_l5,_mc);return new F(function(){return _l4(_l5,_);});}}else{var _me=rMV(_l5),_mf=[0,new T(function(){var _mg=E(E(_me)[1]);return [1,_,[0,new T(function(){return B(_c6(_94,_lO,E(_mg[2])[1]));})],_mg[3]];})],_=wMV(_l5,_mf);return new F(function(){return _l4(_l5,_);});}};return new F(function(){return _kd(_4b,_3z,_3s,_m7,_bR,_m8);});},_mh=new T(function(){return toJSStr(B(unAppCStr("state-final-",new T(function(){return B(_aH(0,_lM,_I));}))));}),_mi=B(A(_kI,[_4a,_mh,_m6,_]));_lG=_lL[2];_lH=_lN[2];return null;}}})(_lG,_lH,_));if(_lI!=null){return _lI;}}},_mj=B(_lF(_dI,new T(function(){return E(E(E(E(E(E(E(E(_lE)[1])[3])[3])[3])[3])[2])[1]);},1),_)),_mk=function(_){var _ml=B(A(_dQ,[_])),_mm=E(_ml);if(!_mm[0]){return new F(function(){return die(_cX);});}else{var _mn=E(_cf)(E(_mm[1]),E(_ce)),_mo=rMV(_l5),_mp=[0,new T(function(){var _mq=E(E(_mo)[1]),_mr=new T(function(){var _ms=E(_mq[3]),_mt=new T(function(){var _mu=E(_ms[3]),_mv=new T(function(){var _mw=E(_mu[3]),_mx=new T(function(){var _my=E(_mw[3]),_mz=new T(function(){return B(_g(E(_my[2])[1],[1,new T(function(){var _mA=String(_mn);return fromJSStr(_mA);}),_I]));});return [1,_,[0,_mz],_my[3]];});return [1,_,_mw[2],_mx];});return [1,_,_mu[2],_mv];});return [1,_,_ms[2],_mt];});return [1,_,_mq[2],_mr];})],_=wMV(_l5,_mp);return new F(function(){return _l4(_l5,_);});}},_mB=function(_mC,_){return new F(function(){return _mk(_);});},_mD=B(A(_kI,[_4a,_bT,function(_mE){return new F(function(){return _kd(_4b,_3z,_3s,_mE,_bR,_mB);});},_])),_mF=function(_mG,_){var _mH=rMV(_l5),_mI=function(_mJ){var _mK=E(_mJ);if(!_mK[0]){return E(_kX);}else{var _mL=_mK[1],_mM=new T(function(){return B(_ap([1,_mL,_I],[1,new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-alphabet-",[1,_mL,_dK]));}),_I]));});return new F(function(){return _g(B(unAppCStr("<tr>",_mM)),new T(function(){return B(_mI(_mK[2]));},1));});}},_mN=E(_cN)(E(_mG),toJSStr(E(_gv)),toJSStr(B(_mI(E(E(E(E(E(E(_mH)[1])[3])[3])[3])[2])[1]))));return new F(function(){return _3u(_);});},_mO=B(A(_kI,[_4a,_bX,_mF,_])),_mP=rMV(_l5),_mQ=function(_mR,_){while(1){var _mS=B((function(_mT,_){var _mU=E(_mT);if(!_mU[0]){return _3t;}else{var _mV=_mU[1],_mW=function(_){var _mX=rMV(_l5),_mY=[0,new T(function(){var _mZ=E(E(_mX)[1]),_n0=new T(function(){var _n1=E(_mZ[3]),_n2=new T(function(){var _n3=E(_n1[3]),_n4=new T(function(){var _n5=E(_n3[3]);return [1,_,[0,new T(function(){return B(_c6(_1,_mV,E(_n5[2])[1]));})],_n5[3]];});return [1,_,_n3[2],_n4];});return [1,_,_n1[2],_n2];});return [1,_,_mZ[2],_n0];})],_=wMV(_l5,_mY);return new F(function(){return _l4(_l5,_);});},_n6=function(_n7,_){return new F(function(){return _mW(_);});},_n8=B(A(_kI,[_4a,new T(function(){return toJSStr(B(unAppCStr("delete-alphabet-",[1,_mV,_I])));}),function(_n9){return new F(function(){return _kd(_4b,_3z,_3s,_n9,_bR,_n6);});},_]));_mR=_mU[2];return null;}})(_mR,_));if(_mS!=null){return _mS;}}},_na=B(_mQ(E(E(E(E(E(E(_mP)[1])[3])[3])[3])[2])[1],_)),_nb=function(_){var _nc=B(A(_dO,[_])),_nd=E(_nc);if(!_nd[0]){return new F(function(){return die(_cU);});}else{var _ne=E(_cf)(E(_nd[1]),E(_ce)),_nf=String(_ne),_ng=fromJSStr(_nf);if(!_ng[0]){return new F(function(){return _b6(_);});}else{if(!E(_ng[2])[0]){var _nh=rMV(_l5),_ni=[0,new T(function(){var _nj=E(E(_nh)[1]),_nk=new T(function(){var _nl=E(_nj[3]),_nm=new T(function(){var _nn=E(_nl[3]),_no=new T(function(){var _np=E(_nn[3]);return [1,_,[0,new T(function(){return B(_g(E(_np[2])[1],[1,_ng[1],_I]));})],_np[3]];});return [1,_,_nn[2],_no];});return [1,_,_nl[2],_nm];});return [1,_,_nj[2],_nk];})],_=wMV(_l5,_ni);return new F(function(){return _l4(_l5,_);});}else{return new F(function(){return _b6(_);});}}}},_nq=function(_nr,_){return new F(function(){return _nb(_);});},_ns=B(A(_kI,[_4a,_bY,function(_nt){return new F(function(){return _kd(_4b,_3z,_3s,_nt,_bR,_nq);});},_])),_nu=function(_nv,_){var _nw=rMV(_l5),_nx=new T(function(){var _ny=new T(function(){var _nz=new T(function(){var _nA=new T(function(){var _nB=function(_nC){var _nD=E(_nC);if(!_nD[0]){return [0];}else{return new F(function(){return _g(B(unAppCStr("<option>",new T(function(){return B(_g(_nD[1],_cR));}))),new T(function(){return B(_nB(_nD[2]));},1));});}};return B(_g(B(_nB(E(E(E(E(E(E(E(_nw)[1])[3])[3])[3])[3])[2])[1])),_cQ));});return B(unAppCStr("\">",_nA));}),_nE=function(_nF){return new F(function(){return unAppCStr("<select class=\"form-control input-sm\" id=\"",new T(function(){return B(_g(_nF,_nz));}));});},_nG=new T(function(){var _nH=new T(function(){var _nI=function(_nJ){var _nK=E(_nJ);if(!_nK[0]){return E(_cQ);}else{return new F(function(){return _g(B(unAppCStr("<option>",[1,_nK[1],_cR])),new T(function(){return B(_nI(_nK[2]));},1));});}};return B(_nI(E(E(E(E(E(E(_nw)[1])[3])[3])[3])[2])[1]));});return B(unAppCStr("<select class=\"form-control input-sm\" id=\"select-alphabet\">",_nH));});return B(_ap(new T(function(){return B(_nE(_dM));}),[1,_nG,[1,new T(function(){return B(_nE(_dL));}),_cP]]));});return B(_g(B(unAppCStr("<tr>",_ny)),_I));}),_nL=function(_nM,_nN){var _nO=E(_nM);if(!_nO[0]){return E(_nx);}else{var _nP=E(_nN);if(!_nP[0]){return E(_nx);}else{var _nQ=new T(function(){var _nR=E(_nP[1]),_nS=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-transition-",new T(function(){return B(_g(B(_aH(0,_nO[1],_I)),_dK));})));});return B(_ap(_nR[1],[1,[1,_nR[2],_I],[1,_nR[3],[1,_nS,_I]]]));});return new F(function(){return _g(B(unAppCStr("<tr>",_nQ)),new T(function(){return B(_nL(_nO[2],_nP[2]));},1));});}}},_nT=E(_cN)(E(_nv),toJSStr(E(_gv)),toJSStr(B(_nL(_dI,new T(function(){return E(E(E(E(E(E(_nw)[1])[3])[3])[2])[1]);},1)))));return new F(function(){return _3u(_);});},_nU=B(A(_kI,[_4a,_bZ,_nu,_])),_nV=rMV(_l5),_nW=function(_nX,_nY,_){while(1){var _nZ=B((function(_o0,_o1,_){var _o2=E(_o0);if(!_o2[0]){return _3t;}else{var _o3=E(_o1);if(!_o3[0]){return _3t;}else{var _o4=function(_){var _o5=rMV(_l5),_o6=[0,new T(function(){var _o7=E(E(_o5)[1]),_o8=new T(function(){var _o9=E(_o7[3]),_oa=new T(function(){var _ob=E(_o9[3]);return [1,_,[0,new T(function(){return B(_c6(_jX,_o3[1],E(_ob[2])[1]));})],_ob[3]];});return [1,_,_o9[2],_oa];});return [1,_,_o7[2],_o8];})],_=wMV(_l5,_o6);return new F(function(){return _l4(_l5,_);});},_oc=function(_od,_){return new F(function(){return _o4(_);});},_oe=new T(function(){return toJSStr(B(unAppCStr("delete-transition-",new T(function(){return B(_aH(0,_o2[1],_I));}))));}),_of=B(A(_kI,[_4a,_oe,function(_og){return new F(function(){return _kd(_4b,_3z,_3s,_og,_bR,_oc);});},_]));_nX=_o2[2];_nY=_o3[2];return null;}}})(_nX,_nY,_));if(_nZ!=null){return _nZ;}}},_oh=B(_nW(_dI,new T(function(){return E(E(E(E(E(E(_nV)[1])[3])[3])[2])[1]);},1),_)),_oi=function(_){var _oj=B(A(_ds,[_])),_ok=E(_oj);if(!_ok[0]){return new F(function(){return die(_jW);});}else{var _ol=E(_cf),_om=E(_ce),_on=_ol(E(_ok[1]),_om),_oo=B(A(_dq,[_])),_op=E(_oo);if(!_op[0]){return new F(function(){return die(_jT);});}else{var _oq=_ol(E(_op[1]),_om),_or=String(_oq),_os=fromJSStr(_or);if(!_os[0]){return new F(function(){return _ba(_);});}else{if(!E(_os[2])[0]){var _ot=B(A(_do,[_])),_ou=E(_ot);if(!_ou[0]){return new F(function(){return die(_jQ);});}else{var _ov=_ol(E(_ou[1]),_om),_ow=rMV(_l5),_ox=[0,new T(function(){var _oy=E(E(_ow)[1]),_oz=new T(function(){var _oA=E(_oy[3]),_oB=new T(function(){var _oC=E(_oA[3]),_oD=new T(function(){return B(_ht(_jX,B(_g(E(_oC[2])[1],[1,[0,new T(function(){var _oE=String(_on);return fromJSStr(_oE);}),_os[1],new T(function(){var _oF=String(_ov);return fromJSStr(_oF);})],_I]))));});return [1,_,[0,_oD],_oC[3]];});return [1,_,_oA[2],_oB];});return [1,_,_oy[2],_oz];})],_=wMV(_l5,_ox);return new F(function(){return _l4(_l5,_);});}}else{return new F(function(){return _ba(_);});}}}}},_oG=function(_oH,_){return new F(function(){return _oi(_);});},_oI=B(A(_kI,[_4a,_c1,function(_oJ){return new F(function(){return _kd(_4b,_3z,_3s,_oJ,_bR,_oG);});},_])),_oK=function(_){var _oL=rMV(_l5),_oM=B(A(_dm,[_])),_oN=E(_oM);if(!_oN[0]){return new F(function(){return _46(_dk,_);});}else{var _oO=E(_cN)(E(_oN[1]),toJSStr(E(_dj)),toJSStr(fromJSStr(B(_bN([4,E(B(_8I(_8Y,_7z,E(_oL)[1])))])))));return new F(function(){return _3u(_);});}},_oP=function(_oQ,_){return new F(function(){return _oK(_);});},_oR=B(A(_kI,[_4a,_c2,function(_oS){return new F(function(){return _kd(_4b,_3z,_3s,_oS,_bR,_oP);});},_])),_oT=function(_){var _oU=B(A(_di,[_])),_oV=E(_oU);if(!_oV[0]){return new F(function(){return die(_jM);});}else{var _oW=E(_cf)(E(_oV[1]),E(_ce)),_oX=new T(function(){var _oY=String(_oW),_oZ=jsParseJSON(toJSStr(fromJSStr(_oY)));if(!_oZ[0]){return E(_dg);}else{var _p0=E(_oZ[1]);if(_p0[0]==4){var _p1=E(_p0[1]);if(!_p1[0]){return E(_8r);}else{var _p2=B(_7l(_6m,E(_p1[1])[2]));if(!_p2[0]){return E(_dg);}else{var _p3=E(_p1[2]);if(!_p3[0]){return E(_8r);}else{var _p4=E(E(_p3[1])[2]);if(_p4[0]==1){var _p5=E(_p3[2]);if(!_p5[0]){return E(_8r);}else{var _p6=B(_5U(_7w,_6m,_7w,E(_p5[1])[2]));if(!_p6[0]){return E(_dg);}else{var _p7=E(_p5[2]);if(!_p7[0]){return E(_8r);}else{var _p8=E(E(_p7[1])[2]);if(_p8[0]==1){var _p9=E(_p7[2]);if(!_p9[0]){return E(_6s);}else{var _pa=B(_7l(_6m,E(_p9[1])[2]));if(!_pa[0]){return E(_dg);}else{if(!E(_p9[2])[0]){return [0,[1,_,[0,_p2[1]],[1,_,[0,new T(function(){return fromJSStr(_p4[1]);})],[1,_,[0,_p6[1]],[1,_,[0,new T(function(){return fromJSStr(_p8[1]);})],[1,_,[0,_pa[1]],_0]]]]]];}else{return E(_6p);}}}}else{return E(_dg);}}}}}else{return E(_dg);}}}}}else{return E(_8r);}}}),_=wMV(_l5,_oX);return new F(function(){return _l4(_l5,_);});}},_pb=function(_pc,_){return new F(function(){return _oT(_);});},_pd=B(A(_kI,[_4a,_c3,function(_pe){return new F(function(){return _kd(_4b,_3z,_3s,_pe,_bR,_pb);});},_])),_pf=function(_){var _pg=B(A(_d6,[_])),_ph=E(_pg);if(!_ph[0]){return new F(function(){return die(_jJ);});}else{var _pi=E(_cf)(E(_ph[1]),E(_ce)),_pj=rMV(_l5),_pk=new T(function(){var _pl=String(_pi);if(!B(_9K(_pj,fromJSStr(_pl)))){return E(_jN);}else{return E(_jG);}});return new F(function(){return A(_kI,[_4a,_c5,function(_pm,_){var _pn=E(_cN)(E(_pm),toJSStr(E(_gv)),toJSStr(E(_pk)));return new F(function(){return _3u(_);});},_]);});}},_po=function(_pp,_){return new F(function(){return _pf(_);});},_pq=B(A(_kI,[_4a,_c4,function(_pr){return new F(function(){return _kd(_4b,_3z,_3s,_pr,_bR,_po);});},_])),_ps=function(_pt,_){var _pu=rMV(_l5),_pv=_pu,_pw=function(_px){var _py=E(_px);if(!_py[0]){return [0];}else{var _pz=_py[1],_pA=new T(function(){return B(_ap(_pz,[1,new T(function(){if(!B(_9K(_pv,_pz))){return E(_jN);}else{return E(_jG);}}),_I]));});return new F(function(){return _g(B(unAppCStr("<tr>",_pA)),new T(function(){return B(_pw(_py[2]));},1));});}},_pB=E(_cN)(E(_pt),toJSStr(E(_gv)),toJSStr(B(_pw(B(_aX(5,new T(function(){return E(E(E(E(E(E(E(_pv)[1])[3])[3])[3])[2])[1]);})))))));return new F(function(){return _3u(_);});},_pC=B(A(_kI,[_4a,_bU,_ps,_])),_pD=function(_pE,_){while(1){var _pF=B((function(_pG,_){var _pH=E(_pG);if(!_pH[0]){return _3t;}else{var _pI=E(_pH[1]),_pJ=function(_){var _pK=new T(function(){var _pL=jsParseJSON(toJSStr(E(E(_pI[2])[3])));if(!_pL[0]){return E(_gX);}else{var _pM=E(_pL[1]);if(_pM[0]==4){var _pN=E(_pM[1]);if(!_pN[0]){return E(_8r);}else{var _pO=B(_7l(_6m,E(_pN[1])[2]));if(!_pO[0]){return E(_gX);}else{var _pP=E(_pN[2]);if(!_pP[0]){return E(_8r);}else{var _pQ=E(E(_pP[1])[2]);if(_pQ[0]==1){var _pR=E(_pP[2]);if(!_pR[0]){return E(_8r);}else{var _pS=B(_5U(_7w,_6m,_7w,E(_pR[1])[2]));if(!_pS[0]){return E(_gX);}else{var _pT=E(_pR[2]);if(!_pT[0]){return E(_8r);}else{var _pU=E(E(_pT[1])[2]);if(_pU[0]==1){var _pV=E(_pT[2]);if(!_pV[0]){return E(_6s);}else{var _pW=B(_7l(_6m,E(_pV[1])[2]));if(!_pW[0]){return E(_gX);}else{if(!E(_pV[2])[0]){return [0,[1,_,[0,_pO[1]],[1,_,[0,new T(function(){return fromJSStr(_pQ[1]);})],[1,_,[0,_pS[1]],[1,_,[0,new T(function(){return fromJSStr(_pU[1]);})],[1,_,[0,_pW[1]],_0]]]]]];}else{return E(_6p);}}}}else{return E(_gX);}}}}}else{return E(_gX);}}}}}else{return E(_8r);}}}),_=wMV(_l5,_pK);return new F(function(){return _l4(_l5,_);});},_pX=function(_pY,_){return new F(function(){return _pJ(_);});},_pZ=new T(function(){return toJSStr(B(unAppCStr("load-",new T(function(){return B(_aH(0,_pI[1],_I));}))));}),_q0=B(A(_kI,[_4a,_pZ,function(_q1){return new F(function(){return _kd(_4b,_3z,_3s,_q1,_bR,_pX);});},_]));_pE=_pH[2];return null;}})(_pE,_));if(_pF!=null){return _pF;}}},_q2=B(A(_kI,[_4a,_bV,function(_q3,_){var _q4=rMV(_l5),_q5=E(_cN)(E(_q3),toJSStr(E(_gv)),toJSStr(E(_gW)));return new F(function(){return _pD(_gu,_);});},_])),_q6=function(_q7,_){while(1){var _q8=B((function(_q9,_){var _qa=E(_q9);if(!_qa[0]){return _3t;}else{var _qb=E(_qa[1]),_qc=function(_){var _qd=rMV(_l5),_qe=new T(function(){return B(A(E(_qb[2])[2],[_c,_4B,_qd]));}),_qf=new T(function(){return B(_gB(new T(function(){return E(E(E(E(E(_qe)[1])[3])[2])[1]);},1)));}),_=wMV(_l5,[0,[1,_,[0,new T(function(){return B(_6B(_gB,E(E(E(_qe)[1])[2])[1]));})],[1,_,[0,_qf],[1,_,[0,new T(function(){return B(_6B(_gF,E(E(E(E(E(_qe)[1])[3])[3])[2])[1]));})],[1,_,[0,new T(function(){return E(E(E(E(E(E(E(_qe)[1])[3])[3])[3])[2])[1]);})],[1,_,[0,new T(function(){return B(_6B(_gB,E(E(E(E(E(E(E(_qe)[1])[3])[3])[3])[3])[2])[1]));})],_0]]]]]]);return new F(function(){return _l4(_l5,_);});},_qg=function(_qh,_){return new F(function(){return _qc(_);});},_qi=new T(function(){return toJSStr(B(unAppCStr("convert-",new T(function(){return B(_aH(0,_qb[1],_I));}))));}),_qj=B(A(_kI,[_4a,_qi,function(_qk){return new F(function(){return _kd(_4b,_3z,_3s,_qk,_bR,_qg);});},_]));_q7=_qa[2];return null;}})(_q7,_));if(_q8!=null){return _q8;}}},_ql=B(A(_kI,[_4a,_bW,function(_qm,_){var _qn=rMV(_l5),_qo=E(_cN)(E(_qm),toJSStr(E(_gv)),toJSStr(E(_jy)));return new F(function(){return _q6(_jF,_);});},_]));return _3t;},_qp=function(_qq){return new F(function(){return _de("Main.hs:354:7-93|Right auto");});},_qr=new T(function(){var _qs=jsParseJSON(toJSStr(E(B(_ea(_gi,0))[3])));if(!_qs[0]){return B(_qp(_));}else{var _qt=E(_qs[1]);if(_qt[0]==4){var _qu=E(_qt[1]);if(!_qu[0]){return E(_8r);}else{var _qv=B(_7l(_6m,E(_qu[1])[2]));if(!_qv[0]){return B(_qp(_));}else{var _qw=E(_qu[2]);if(!_qw[0]){return E(_8r);}else{var _qx=E(E(_qw[1])[2]);if(_qx[0]==1){var _qy=E(_qw[2]);if(!_qy[0]){return E(_8r);}else{var _qz=B(_5U(_7w,_6m,_7w,E(_qy[1])[2]));if(!_qz[0]){return B(_qp(_));}else{var _qA=E(_qy[2]);if(!_qA[0]){return E(_8r);}else{var _qB=E(E(_qA[1])[2]);if(_qB[0]==1){var _qC=E(_qA[2]);if(!_qC[0]){return E(_6s);}else{var _qD=B(_7l(_6m,E(_qC[1])[2]));if(!_qD[0]){return B(_qp(_));}else{if(!E(_qC[2])[0]){return [0,[1,_,[0,_qv[1]],[1,_,[0,new T(function(){return fromJSStr(_qx[1]);})],[1,_,[0,_qz[1]],[1,_,[0,new T(function(){return fromJSStr(_qB[1]);})],[1,_,[0,_qD[1]],_0]]]]]];}else{return E(_6p);}}}}else{return B(_qp(_));}}}}}else{return B(_qp(_));}}}}}else{return E(_8r);}}}),_qE=function(_){var _qF=nMV(_qr);return new F(function(){return _l4(_qF,_);});},_qG=function(_){return new F(function(){return _qE(_);});};
var hasteMain = function() {B(A(_qG, [0]));};window.onload = hasteMain;