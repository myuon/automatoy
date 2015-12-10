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

var _0=[0,_],_1=function(_2,_3){return E(_2)!=E(_3);},_4=function(_5,_6){return E(_5)==E(_6);},_7=function(_8,_9){while(1){var _a=E(_8);if(!_a[0]){return (E(_9)[0]==0)?true:false;}else{var _b=E(_9);if(!_b[0]){return false;}else{if(E(_a[1])!=E(_b[1])){return false;}else{_8=_a[2];_9=_b[2];continue;}}}}},_c=function(_d,_e){return (!B(_7(_d,_e)))?true:false;},_f=[0,_7,_c],_g="deltaZ",_h="deltaY",_i="deltaX",_j=function(_k,_l){var _m=E(_k);return (_m[0]==0)?E(_l):[1,_m[1],new T(function(){return B(_j(_m[2],_l));})];},_n=function(_o,_p){var _q=jsShowI(_o);return new F(function(){return _j(fromJSStr(_q),_p);});},_r=41,_s=40,_t=function(_u,_v,_w){if(_v>=0){return new F(function(){return _n(_v,_w);});}else{if(_u<=6){return new F(function(){return _n(_v,_w);});}else{return [1,_s,new T(function(){var _x=jsShowI(_v);return B(_j(fromJSStr(_x),[1,_r,_w]));})];}}},_y=new T(function(){return B(unCStr(")"));}),_z=new T(function(){return B(_t(0,2,_y));}),_A=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_z));}),_B=function(_C){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_t(0,_C,_A));}))));});},_D=function(_E,_){return new T(function(){var _F=Number(E(_E)),_G=jsTrunc(_F);if(_G<0){return B(_B(_G));}else{if(_G>2){return B(_B(_G));}else{return _G;}}});},_H=0,_I=[0,_H,_H,_H],_J="button",_K=new T(function(){return jsGetMouseCoords;}),_L=[0],_M=function(_N,_){var _O=E(_N);if(!_O[0]){return _L;}else{var _P=B(_M(_O[2],_));return [1,new T(function(){var _Q=Number(E(_O[1]));return jsTrunc(_Q);}),_P];}},_R=function(_S,_){var _T=__arr2lst(0,_S);return new F(function(){return _M(_T,_);});},_U=function(_V,_){return new F(function(){return _R(E(_V),_);});},_W=function(_X,_){return new T(function(){var _Y=Number(E(_X));return jsTrunc(_Y);});},_Z=[0,_W,_U],_10=function(_11,_){var _12=E(_11);if(!_12[0]){return _L;}else{var _13=B(_10(_12[2],_));return [1,_12[1],_13];}},_14=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_15=new T(function(){return B(unCStr("base"));}),_16=new T(function(){return B(unCStr("IOException"));}),_17=new T(function(){var _18=hs_wordToWord64(4053623282),_19=hs_wordToWord64(3693590983);return [0,_18,_19,[0,_18,_19,_15,_14,_16],_L,_L];}),_1a=function(_1b){return E(_17);},_1c=function(_1d){return E(E(_1d)[1]);},_1e=function(_1f,_1g,_1h){var _1i=B(A(_1f,[_])),_1j=B(A(_1g,[_])),_1k=hs_eqWord64(_1i[1],_1j[1]);if(!_1k){return [0];}else{var _1l=hs_eqWord64(_1i[2],_1j[2]);return (!_1l)?[0]:[1,_1h];}},_1m=function(_1n){var _1o=E(_1n);return new F(function(){return _1e(B(_1c(_1o[1])),_1a,_1o[2]);});},_1p=new T(function(){return B(unCStr(": "));}),_1q=new T(function(){return B(unCStr(")"));}),_1r=new T(function(){return B(unCStr(" ("));}),_1s=new T(function(){return B(unCStr("interrupted"));}),_1t=new T(function(){return B(unCStr("system error"));}),_1u=new T(function(){return B(unCStr("unsatisified constraints"));}),_1v=new T(function(){return B(unCStr("user error"));}),_1w=new T(function(){return B(unCStr("permission denied"));}),_1x=new T(function(){return B(unCStr("illegal operation"));}),_1y=new T(function(){return B(unCStr("end of file"));}),_1z=new T(function(){return B(unCStr("resource exhausted"));}),_1A=new T(function(){return B(unCStr("resource busy"));}),_1B=new T(function(){return B(unCStr("does not exist"));}),_1C=new T(function(){return B(unCStr("already exists"));}),_1D=new T(function(){return B(unCStr("resource vanished"));}),_1E=new T(function(){return B(unCStr("timeout"));}),_1F=new T(function(){return B(unCStr("unsupported operation"));}),_1G=new T(function(){return B(unCStr("hardware fault"));}),_1H=new T(function(){return B(unCStr("inappropriate type"));}),_1I=new T(function(){return B(unCStr("invalid argument"));}),_1J=new T(function(){return B(unCStr("failed"));}),_1K=new T(function(){return B(unCStr("protocol error"));}),_1L=function(_1M,_1N){switch(E(_1M)){case 0:return new F(function(){return _j(_1C,_1N);});break;case 1:return new F(function(){return _j(_1B,_1N);});break;case 2:return new F(function(){return _j(_1A,_1N);});break;case 3:return new F(function(){return _j(_1z,_1N);});break;case 4:return new F(function(){return _j(_1y,_1N);});break;case 5:return new F(function(){return _j(_1x,_1N);});break;case 6:return new F(function(){return _j(_1w,_1N);});break;case 7:return new F(function(){return _j(_1v,_1N);});break;case 8:return new F(function(){return _j(_1u,_1N);});break;case 9:return new F(function(){return _j(_1t,_1N);});break;case 10:return new F(function(){return _j(_1K,_1N);});break;case 11:return new F(function(){return _j(_1J,_1N);});break;case 12:return new F(function(){return _j(_1I,_1N);});break;case 13:return new F(function(){return _j(_1H,_1N);});break;case 14:return new F(function(){return _j(_1G,_1N);});break;case 15:return new F(function(){return _j(_1F,_1N);});break;case 16:return new F(function(){return _j(_1E,_1N);});break;case 17:return new F(function(){return _j(_1D,_1N);});break;default:return new F(function(){return _j(_1s,_1N);});}},_1O=new T(function(){return B(unCStr("}"));}),_1P=new T(function(){return B(unCStr("{handle: "));}),_1Q=function(_1R,_1S,_1T,_1U,_1V,_1W){var _1X=new T(function(){var _1Y=new T(function(){var _1Z=new T(function(){var _20=E(_1U);if(!_20[0]){return E(_1W);}else{var _21=new T(function(){return B(_j(_20,new T(function(){return B(_j(_1q,_1W));},1)));},1);return B(_j(_1r,_21));}},1);return B(_1L(_1S,_1Z));}),_22=E(_1T);if(!_22[0]){return E(_1Y);}else{return B(_j(_22,new T(function(){return B(_j(_1p,_1Y));},1)));}}),_23=E(_1V);if(!_23[0]){var _24=E(_1R);if(!_24[0]){return E(_1X);}else{var _25=E(_24[1]);if(!_25[0]){var _26=new T(function(){var _27=new T(function(){return B(_j(_1O,new T(function(){return B(_j(_1p,_1X));},1)));},1);return B(_j(_25[1],_27));},1);return new F(function(){return _j(_1P,_26);});}else{var _28=new T(function(){var _29=new T(function(){return B(_j(_1O,new T(function(){return B(_j(_1p,_1X));},1)));},1);return B(_j(_25[1],_29));},1);return new F(function(){return _j(_1P,_28);});}}}else{return new F(function(){return _j(_23[1],new T(function(){return B(_j(_1p,_1X));},1));});}},_2a=function(_2b){var _2c=E(_2b);return new F(function(){return _1Q(_2c[1],_2c[2],_2c[3],_2c[4],_2c[6],_L);});},_2d=function(_2e,_2f,_2g){var _2h=E(_2f);return new F(function(){return _1Q(_2h[1],_2h[2],_2h[3],_2h[4],_2h[6],_2g);});},_2i=function(_2j,_2k){var _2l=E(_2j);return new F(function(){return _1Q(_2l[1],_2l[2],_2l[3],_2l[4],_2l[6],_2k);});},_2m=44,_2n=93,_2o=91,_2p=function(_2q,_2r,_2s){var _2t=E(_2r);if(!_2t[0]){return new F(function(){return unAppCStr("[]",_2s);});}else{var _2u=new T(function(){var _2v=new T(function(){var _2w=function(_2x){var _2y=E(_2x);if(!_2y[0]){return [1,_2n,_2s];}else{var _2z=new T(function(){return B(A(_2q,[_2y[1],new T(function(){return B(_2w(_2y[2]));})]));});return [1,_2m,_2z];}};return B(_2w(_2t[2]));});return B(A(_2q,[_2t[1],_2v]));});return [1,_2o,_2u];}},_2A=function(_2B,_2C){return new F(function(){return _2p(_2i,_2B,_2C);});},_2D=[0,_2d,_2a,_2A],_2E=new T(function(){return [0,_1a,_2D,_2F,_1m,_2a];}),_2F=function(_2G){return [0,_2E,_2G];},_2H=[0],_2I=7,_2J=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_2K=[0,_2H,_2I,_L,_2J,_2H,_2H],_2L=new T(function(){return B(_2F(_2K));}),_2M=function(_){return new F(function(){return die(_2L);});},_2N=function(_2O){return E(E(_2O)[1]);},_2P=function(_2Q,_2R,_2S,_){var _2T=__arr2lst(0,_2S),_2U=B(_10(_2T,_)),_2V=E(_2U);if(!_2V[0]){return new F(function(){return _2M(_);});}else{var _2W=E(_2V[2]);if(!_2W[0]){return new F(function(){return _2M(_);});}else{if(!E(_2W[2])[0]){var _2X=B(A(_2N,[_2Q,_2V[1],_])),_2Y=B(A(_2N,[_2R,_2W[1],_]));return [0,_2X,_2Y];}else{return new F(function(){return _2M(_);});}}}},_2Z=function(_){return new F(function(){return __jsNull();});},_30=function(_31){var _32=B(A(_31,[_]));return E(_32);},_33=new T(function(){return B(_30(_2Z));}),_34=new T(function(){return E(_33);}),_35=function(_36,_37,_){if(E(_36)==7){var _38=E(_K)(_37),_39=B(_2P(_Z,_Z,_38,_)),_3a=_37[E(_i)],_3b=_37[E(_h)],_3c=_37[E(_g)];return new T(function(){return [0,E(_39),E(_2H),[0,_3a,_3b,_3c]];});}else{var _3d=E(_K)(_37),_3e=B(_2P(_Z,_Z,_3d,_)),_3f=_37[E(_J)],_3g=__eq(_3f,E(_34));if(!E(_3g)){var _3h=B(_D(_3f,_));return new T(function(){return [0,E(_3e),[1,_3h],E(_I)];});}else{return new T(function(){return [0,E(_3e),E(_2H),E(_I)];});}}},_3i=function(_3j,_3k,_){return new F(function(){return _35(_3j,E(_3k),_);});},_3l="mouseout",_3m="mouseover",_3n="mousemove",_3o="mouseup",_3p="mousedown",_3q="dblclick",_3r="click",_3s="wheel",_3t=function(_3u){switch(E(_3u)){case 0:return E(_3r);case 1:return E(_3q);case 2:return E(_3p);case 3:return E(_3o);case 4:return E(_3n);case 5:return E(_3m);case 6:return E(_3l);default:return E(_3s);}},_3v=[0,_3t,_3i],_3w=0,_3x=function(_){return _3w;},_3y=function(_3z,_){return [1,_3z];},_3A=function(_3B){return E(_3B);},_3C=[0,_3A,_3y],_3D=function(_3E,_3F,_){var _3G=B(A(_3E,[_])),_3H=B(A(_3F,[_]));return _3G;},_3I=function(_3J,_3K,_){var _3L=B(A(_3J,[_])),_3M=B(A(_3K,[_]));return new T(function(){return B(A(_3L,[_3M]));});},_3N=function(_3O,_3P,_){var _3Q=B(A(_3P,[_]));return _3O;},_3R=function(_3S,_3T,_){var _3U=B(A(_3T,[_]));return new T(function(){return B(A(_3S,[_3U]));});},_3V=[0,_3R,_3N],_3W=function(_3X,_){return _3X;},_3Y=function(_3Z,_40,_){var _41=B(A(_3Z,[_]));return new F(function(){return A(_40,[_]);});},_42=[0,_3V,_3W,_3I,_3Y,_3D],_43=function(_44,_45,_){var _46=B(A(_44,[_]));return new F(function(){return A(_45,[_46,_]);});},_47=function(_48){return [0,_2H,_2I,_L,_48,_2H,_2H];},_49=function(_4a,_){var _4b=new T(function(){return B(_2F(new T(function(){return B(_47(_4a));})));});return new F(function(){return die(_4b);});},_4c=[0,_42,_43,_3Y,_3W,_49],_4d=[0,_4c,_3A],_4e=[0,_4d,_3W],_4f=function(_4g,_4h){while(1){var _4i=E(_4g);if(!_4i[0]){return (E(_4h)[0]==0)?1:0;}else{var _4j=E(_4h);if(!_4j[0]){return 2;}else{var _4k=E(_4i[1]),_4l=E(_4j[1]);if(_4k!=_4l){return (_4k>_4l)?2:0;}else{_4g=_4i[2];_4h=_4j[2];continue;}}}}},_4m=function(_4n,_4o){return (B(_4f(_4n,_4o))==0)?true:false;},_4p=function(_4q,_4r){return (B(_4f(_4q,_4r))==2)?false:true;},_4s=function(_4t,_4u){return (B(_4f(_4t,_4u))==2)?true:false;},_4v=function(_4w,_4x){return (B(_4f(_4w,_4x))==0)?false:true;},_4y=function(_4z,_4A){return (B(_4f(_4z,_4A))==2)?E(_4z):E(_4A);},_4B=function(_4C,_4D){return (B(_4f(_4C,_4D))==2)?E(_4D):E(_4C);},_4E=[0,_f,_4f,_4m,_4p,_4s,_4v,_4y,_4B],_4F=[1,_L],_4G=new T(function(){return B(unCStr("Tried to deserialie a non-array to a list!"));}),_4H=[0,_4G],_4I=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4J=new T(function(){return B(unCStr("base"));}),_4K=new T(function(){return B(unCStr("PatternMatchFail"));}),_4L=new T(function(){var _4M=hs_wordToWord64(18445595),_4N=hs_wordToWord64(52003073);return [0,_4M,_4N,[0,_4M,_4N,_4J,_4I,_4K],_L,_L];}),_4O=function(_4P){return E(_4L);},_4Q=function(_4R){var _4S=E(_4R);return new F(function(){return _1e(B(_1c(_4S[1])),_4O,_4S[2]);});},_4T=function(_4U){return E(E(_4U)[1]);},_4V=function(_4W){return [0,_4X,_4W];},_4Y=function(_4Z,_50){return new F(function(){return _j(E(_4Z)[1],_50);});},_51=function(_52,_53){return new F(function(){return _2p(_4Y,_52,_53);});},_54=function(_55,_56,_57){return new F(function(){return _j(E(_56)[1],_57);});},_58=[0,_54,_4T,_51],_4X=new T(function(){return [0,_4O,_58,_4V,_4Q,_4T];}),_59=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5a=function(_5b){return E(E(_5b)[3]);},_5c=function(_5d,_5e){return new F(function(){return die(new T(function(){return B(A(_5a,[_5e,_5d]));}));});},_5f=function(_5g,_5h){return new F(function(){return _5c(_5g,_5h);});},_5i=function(_5j,_5k){var _5l=E(_5k);if(!_5l[0]){return [0,_L,_L];}else{var _5m=_5l[1];if(!B(A(_5j,[_5m]))){return [0,_L,_5l];}else{var _5n=new T(function(){var _5o=B(_5i(_5j,_5l[2]));return [0,_5o[1],_5o[2]];});return [0,[1,_5m,new T(function(){return E(E(_5n)[1]);})],new T(function(){return E(E(_5n)[2]);})];}}},_5p=32,_5q=new T(function(){return B(unCStr("\n"));}),_5r=function(_5s){return (E(_5s)==124)?false:true;},_5t=function(_5u,_5v){var _5w=B(_5i(_5r,B(unCStr(_5u)))),_5x=_5w[1],_5y=function(_5z,_5A){var _5B=new T(function(){var _5C=new T(function(){return B(_j(_5v,new T(function(){return B(_j(_5A,_5q));},1)));});return B(unAppCStr(": ",_5C));},1);return new F(function(){return _j(_5z,_5B);});},_5D=E(_5w[2]);if(!_5D[0]){return new F(function(){return _5y(_5x,_L);});}else{if(E(_5D[1])==124){return new F(function(){return _5y(_5x,[1,_5p,_5D[2]]);});}else{return new F(function(){return _5y(_5x,_L);});}}},_5E=function(_5F){return new F(function(){return _5f([0,new T(function(){return B(_5t(_5F,_59));})],_4X);});},_5G=function(_5H){return new F(function(){return _5E("Main.hs:45:3-81|function parseJSON");});},_5I=new T(function(){return B(_5G(_));}),_5J=function(_5K){return E(E(_5K)[3]);},_5L=function(_5M,_5N,_5O,_5P){var _5Q=E(_5P);if(_5Q[0]==3){var _5R=E(_5Q[1]);if(!_5R[0]){return E(_5I);}else{var _5S=E(_5R[2]);if(!_5S[0]){return E(_5I);}else{var _5T=E(_5S[2]);if(!_5T[0]){return E(_5I);}else{if(!E(_5T[2])[0]){var _5U=B(A(_5J,[_5M,_5R[1]]));if(!_5U[0]){return [0,_5U[1]];}else{var _5V=B(A(_5J,[_5N,_5S[1]]));if(!_5V[0]){return [0,_5V[1]];}else{var _5W=B(A(_5J,[_5O,_5T[1]]));return (_5W[0]==0)?[0,_5W[1]]:[1,[0,_5U[1],_5V[1],_5W[1]]];}}}else{return E(_5I);}}}}}else{return E(_5I);}},_5X=function(_5Y,_5Z,_60,_61){var _62=E(_61);if(_62[0]==3){var _63=function(_64){var _65=E(_64);if(!_65[0]){return E(_4F);}else{var _66=B(_5L(_5Y,_5Z,_60,_65[1]));if(!_66[0]){return [0,_66[1]];}else{var _67=B(_63(_65[2]));return (_67[0]==0)?[0,_67[1]]:[1,[1,_66[1],_67[1]]];}}};return new F(function(){return _63(_62[1]);});}else{return E(_4H);}},_68=function(_69){return [1,toJSStr(E(_69))];},_6a=new T(function(){return B(unCStr("Tried to deserialize long string to a Char"));}),_6b=[0,_6a],_6c=new T(function(){return B(unCStr("Tried to deserialize a non-string to a Char"));}),_6d=[0,_6c],_6e=function(_6f){var _6g=E(_6f);if(_6g[0]==1){var _6h=fromJSStr(_6g[1]);return (_6h[0]==0)?E(_6b):(E(_6h[2])[0]==0)?[1,_6h[1]]:E(_6b);}else{return E(_6d);}},_6i=new T(function(){return B(unCStr("Tried to deserialize a non-JSString to a JSString"));}),_6j=[0,_6i],_6k=function(_6l){var _6m=E(_6l);return (_6m[0]==1)?[1,new T(function(){return fromJSStr(_6m[1]);})]:E(_6j);},_6n=function(_6o){return [1,toJSStr([1,_6o,_L])];},_6p=[0,_6n,_68,_6e,_6k],_6q=function(_6r){return new F(function(){return _5E("Main.hs:63:3-45|function jsonToUnion");});},_6s=new T(function(){return B(_6q(_));}),_6t=function(_6u){return new F(function(){return _5E("Main.hs:(67,3)-(70,33)|function jsonToUnion");});},_6v=new T(function(){return B(_6t(_));}),_6w=function(_6x){return E(E(_6x)[1]);},_6y=function(_6z){return new F(function(){return toJSStr(E(_6z));});},_6A=function(_6B,_6C,_6D){return [4,[1,[0,new T(function(){return B(_6y(_6C));}),new T(function(){return B(A(_6w,[_6B,E(_6D)[1]]));})],_L]];},_6E=function(_6F,_6G){var _6H=E(_6G);return (_6H[0]==0)?[0]:[1,new T(function(){return B(A(_6F,[_6H[1]]));}),new T(function(){return B(_6E(_6F,_6H[2]));})];},_6I=function(_6J,_6K,_6L){return [3,E(B(_6E(function(_6M){return new F(function(){return _6A(_6J,_6K,_6M);});},_6L)))];},_6N=function(_6O){return new F(function(){return _5E("Main.hs:49:3-73|function parseJSON");});},_6P=new T(function(){return B(_6N(_));}),_6Q=function(_6R,_6S){var _6T=E(_6S);if(_6T[0]==4){var _6U=E(_6T[1]);if(!_6U[0]){return E(_6P);}else{if(!E(_6U[2])[0]){var _6V=B(A(_5J,[_6R,E(_6U[1])[2]]));return (_6V[0]==0)?[0,_6V[1]]:[1,[0,_6V[1]]];}else{return E(_6P);}}}else{return E(_6P);}},_6W=[1,_L],_6X=[0,_4G],_6Y=function(_6Z,_70){var _71=E(_70);if(_71[0]==3){var _72=function(_73){var _74=E(_73);if(!_74[0]){return E(_6W);}else{var _75=E(_74[1]);if(_75[0]==4){var _76=E(_75[1]);if(!_76[0]){return E(_6P);}else{if(!E(_76[2])[0]){var _77=B(A(_5J,[_6Z,E(_76[1])[2]]));if(!_77[0]){return [0,_77[1]];}else{var _78=B(_72(_74[2]));return (_78[0]==0)?[0,_78[1]]:[1,[1,[0,_77[1]],_78[1]]];}}else{return E(_6P);}}}else{return E(_6P);}}};return new F(function(){return _72(_71[1]);});}else{return E(_6X);}},_79=function(_7a,_7b){return [0,function(_6M){return new F(function(){return _6A(_7a,_7b,_6M);});},function(_6M){return new F(function(){return _6I(_7a,_7b,_6M);});},function(_7c){return new F(function(){return _6Q(_7a,_7c);});},function(_7d){return new F(function(){return _6Y(_7a,_7d);});}];},_7e=new T(function(){return B(unCStr("final"));}),_7f=function(_7g){return [3,E(B(_6E(_68,_7g)))];},_7h=function(_7i){return [3,E(B(_6E(_7f,_7i)))];},_7j=[1,_L],_7k=new T(function(){return B(unCStr("Tried to deserialie a non-array to a list!"));}),_7l=[0,_7k],_7m=function(_7n){return E(E(_7n)[4]);},_7o=function(_7p,_7q){var _7r=E(_7q);if(_7r[0]==3){var _7s=new T(function(){return B(_7m(_7p));}),_7t=function(_7u){var _7v=E(_7u);if(!_7v[0]){return E(_7j);}else{var _7w=B(A(_7s,[_7v[1]]));if(!_7w[0]){return [0,_7w[1]];}else{var _7x=B(_7t(_7v[2]));return (_7x[0]==0)?[0,_7x[1]]:[1,[1,_7w[1],_7x[1]]];}}};return new F(function(){return _7t(_7r[1]);});}else{return E(_7l);}},_7y=function(_6M){return new F(function(){return _7o(_6p,_6M);});},_7z=[0,_68,_7f,_6k,_7y],_7A=function(_6M){return new F(function(){return _7o(_7z,_6M);});},_7B=[0,_7f,_7h,_7y,_7A],_7C=new T(function(){return B(_79(_7B,_7e));}),_7D=new T(function(){return B(unCStr("initial"));}),_7E=new T(function(){return B(_79(_7z,_7D));}),_7F=new T(function(){return B(unCStr("transition"));}),_7G=function(_6M){return new F(function(){return _5X(_7z,_6p,_7z,_6M);});},_7H=function(_7I){var _7J=E(_7I);return [3,[1,new T(function(){return B(_68(_7J[1]));}),[1,new T(function(){return B(_6n(_7J[2]));}),[1,new T(function(){return B(_68(_7J[3]));}),_L]]]];},_7K=function(_7L){return [3,E(B(_6E(_7H,_7L)))];},_7M=function(_7N){return [3,E(B(_6E(_7H,_7N)))];},_7O=function(_7P){return [3,E(B(_6E(_7M,_7P)))];},_7Q=function(_7R,_7S,_7T,_7U){var _7V=E(_7U);return [3,[1,new T(function(){return B(A(_6w,[_7R,_7V[1]]));}),[1,new T(function(){return B(A(_6w,[_7S,_7V[2]]));}),[1,new T(function(){return B(A(_6w,[_7T,_7V[3]]));}),_L]]]];},_7W=function(_7X,_7Y,_7Z,_80){return [3,E(B(_6E(function(_6M){return new F(function(){return _7Q(_7X,_7Y,_7Z,_6M);});},_80)))];},_81=function(_82,_83,_84){return [0,function(_6M){return new F(function(){return _7Q(_82,_83,_84,_6M);});},function(_6M){return new F(function(){return _7W(_82,_83,_84,_6M);});},function(_6M){return new F(function(){return _5L(_82,_83,_84,_6M);});},function(_6M){return new F(function(){return _5X(_82,_83,_84,_6M);});}];},_85=new T(function(){return B(_81(_7z,_6p,_7z));}),_86=function(_6M){return new F(function(){return _7o(_85,_6M);});},_87=[0,_7K,_7O,_7G,_86],_88=new T(function(){return B(_79(_87,_7F));}),_89=new T(function(){return B(unCStr("alphabet"));}),_8a=new T(function(){return B(_79(_7z,_89));}),_8b=function(_8c){var _8d=E(_8c);if(_8d[0]==4){var _8e=E(_8d[1]);if(!_8e[0]){return E(_6v);}else{var _8f=B(_7o(_6p,E(_8e[1])[2]));return (_8f[0]==0)?[0,_8f[1]]:(E(_8e[2])[0]==0)?[1,[0,[1,_,[0,_8f[1]],_0]]]:E(_6s);}}else{return E(_6v);}},_8g=new T(function(){return B(unCStr("state"));}),_8h=new T(function(){return toJSStr(E(_8g));}),_8i=function(_8j){var _8k=E(_8j),_8l=E(_8k[3]);return new F(function(){return _j([1,[0,_8h,new T(function(){return [3,E(B(_6E(_68,E(_8k[2])[1])))];})],_L],_L);});},_8m=function(_8n){return [4,E(B(_8i(E(_8n)[1])))];},_8o=[0,_8m,_8b],_8p=function(_8q,_8r){return [1,_,_8q,_8r];},_8s=function(_8t){return new F(function(){return _5E("Main.hs:(67,3)-(70,33)|function jsonToUnion");});},_8u=new T(function(){return B(_8s(_));}),_8v=function(_8w){return E(E(_8w)[2]);},_8x=function(_8y,_8z,_8A){var _8B=E(_8A);if(_8B[0]==4){var _8C=E(_8B[1]);if(!_8C[0]){return E(_8u);}else{var _8D=B(A(_5J,[_8z,[4,[1,_8C[1],_L]]]));if(!_8D[0]){return [0,_8D[1]];}else{var _8E=B(A(_8v,[_8y,new T(function(){return [4,E(_8C[2])];})]));return (_8E[0]==0)?[0,_8E[1]]:[1,[0,new T(function(){return B(_8p(_8D[1],E(_8E[1])[1]));})]];}}}else{return E(_8u);}},_8F=new T(function(){return B(unCStr("Monoid JSON: out of domain"));}),_8G=function(_8H){return new F(function(){return err(_8F);});},_8I=new T(function(){return B(_8G(_));}),_8J=function(_8K){return E(E(_8K)[1]);},_8L=function(_8M,_8N,_8O){var _8P=E(_8O),_8Q=B(A(_6w,[_8N,_8P[2]]));if(_8Q[0]==4){var _8R=B(A(_8J,[_8M,[0,_8P[3]]]));if(_8R[0]==4){return new F(function(){return _j(_8Q[1],_8R[1]);});}else{return E(_8I);}}else{return E(_8I);}},_8S=function(_8T,_8U,_8V){return [4,E(B(_8L(_8T,_8U,E(_8V)[1])))];},_8W=function(_8X,_8Y){return [0,function(_6M){return new F(function(){return _8S(_8X,_8Y,_6M);});},function(_6M){return new F(function(){return _8x(_8X,_8Y,_6M);});}];},_8Z=new T(function(){return B(_8W(_8o,_8a));}),_90=new T(function(){return B(_8W(_8Z,_88));}),_91=new T(function(){return B(_8W(_90,_7E));}),_92=function(_93,_94){while(1){var _95=E(_93);if(!_95[0]){return (E(_94)[0]==0)?true:false;}else{var _96=E(_94);if(!_96[0]){return false;}else{if(!B(_7(_95[1],_96[1]))){return false;}else{_93=_95[2];_94=_96[2];continue;}}}}},_97=function(_98,_99){while(1){var _9a=E(_98);if(!_9a[0]){return (E(_99)[0]==0)?true:false;}else{var _9b=E(_99);if(!_9b[0]){return false;}else{if(E(_9a[1])!=E(_9b[1])){return false;}else{_98=_9a[2];_99=_9b[2];continue;}}}}},_9c=function(_9d,_9e,_9f,_9g,_9h,_9i){return (!B(_97(_9d,_9g)))?true:(E(_9e)!=E(_9h))?true:(!B(_97(_9f,_9i)))?true:false;},_9j=function(_9k,_9l){var _9m=E(_9k),_9n=E(_9l);return new F(function(){return _9c(_9m[1],_9m[2],_9m[3],_9n[1],_9n[2],_9n[3]);});},_9o=function(_9p,_9q,_9r,_9s,_9t,_9u){if(!B(_97(_9p,_9s))){return false;}else{if(E(_9q)!=E(_9t)){return false;}else{return new F(function(){return _97(_9r,_9u);});}}},_9v=function(_9w,_9x){var _9y=E(_9w),_9z=E(_9x);return new F(function(){return _9o(_9y[1],_9y[2],_9y[3],_9z[1],_9z[2],_9z[3]);});},_9A=[0,_9v,_9j],_9B=function(_9C,_9D){while(1){var _9E=E(_9D);if(!_9E[0]){return false;}else{if(!B(A(_9C,[_9E[1]]))){_9D=_9E[2];continue;}else{return true;}}}},_9F=function(_9G){return E(E(_9G)[1]);},_9H=function(_9I,_9J,_9K){while(1){var _9L=E(_9K);if(!_9L[0]){return false;}else{if(!B(A(_9F,[_9I,_9J,_9L[1]]))){_9K=_9L[2];continue;}else{return true;}}}},_9M=new T(function(){return B(_92(_L,_L));}),_9N=function(_9O,_9P){var _9Q=new T(function(){return E(E(E(E(E(E(_9O)[1])[3])[3])[2])[1]);}),_9R=new T(function(){return E(E(E(E(E(E(E(E(_9O)[1])[3])[3])[3])[3])[2])[1]);}),_9S=function(_9T,_9U){while(1){var _9V=B((function(_9W,_9X){var _9Y=E(_9X);if(!_9Y[0]){return E(_9W);}else{var _9Z=new T(function(){var _a0=function(_a1){var _a2=E(_a1);if(!_a2[0]){return [0];}else{var _a3=_a2[1],_a4=new T(function(){return B(_a0(_a2[2]));}),_a5=function(_a6){while(1){var _a7=B((function(_a8){var _a9=E(_a8);if(!_a9[0]){return E(_a4);}else{var _aa=_a9[2];if(!B(_9H(_9A,[0,_a9[1],_9Y[1],_a3],_9Q))){_a6=_aa;return null;}else{return [1,_a3,new T(function(){return B(_a5(_aa));})];}}})(_a6));if(_a7!=null){return _a7;}}};return new F(function(){return _a5(_9W);});}};return B(_a0(_9R));});_9T=_9Z;_9U=_9Y[2];return null;}})(_9T,_9U));if(_9V!=null){return _9V;}}},_ab=B(_9S([1,new T(function(){return E(E(E(E(E(_9O)[1])[3])[2])[1]);}),_L],_9P));if(!_ab[0]){return (!E(_9M))?true:false;}else{var _ac=E(E(E(E(_9O)[1])[2])[1]);if(!_ac[0]){return (!E(_9M))?true:false;}else{var _ad=function(_ae){while(1){var _af=B((function(_ag){var _ah=E(_ag);if(!_ah[0]){return [0];}else{var _ai=_ah[1],_aj=_ah[2];if(!B(_9B(function(_6M){return new F(function(){return _97(_ai,_6M);});},_ac))){_ae=_aj;return null;}else{return [1,_ai,new T(function(){return B(_ad(_aj));})];}}})(_ae));if(_af!=null){return _af;}}},_ak=function(_al,_am){if(!B(_9B(function(_6M){return new F(function(){return _97(_al,_6M);});},_ac))){return new F(function(){return _ad(_am);});}else{return [1,_al,new T(function(){return B(_ad(_am));})];}};return (!B(_92(B(_ak(_ab[1],_ab[2])),_L)))?true:false;}}},_an=new T(function(){return B(unCStr("</td>"));}),_ao=new T(function(){return B(unCStr("</tr>"));}),_ap=function(_aq){var _ar=E(_aq);if(!_ar[0]){return E(_ao);}else{return new F(function(){return _j(B(unAppCStr("<td>",new T(function(){return B(_j(_ar[1],_an));}))),new T(function(){return B(_ap(_ar[2]));},1));});}},_as=function(_at,_au){return new F(function(){return _j(B(unAppCStr("<td>",new T(function(){return B(_j(_at,_an));}))),new T(function(){return B(_ap(_au));},1));});},_av=[1,_L,_L],_aw=function(_ax){var _ay=E(_ax);if(!_ay[0]){return E(_av);}else{var _az=new T(function(){return B(_aw(_ay[2]));}),_aA=function(_aB){var _aC=E(_aB);if(!_aC[0]){return [0];}else{var _aD=new T(function(){return B(_aA(_aC[2]));}),_aE=function(_aF){var _aG=E(_aF);return (_aG[0]==0)?E(_aD):[1,[1,_aC[1],_aG[1]],new T(function(){return B(_aE(_aG[2]));})];};return new F(function(){return _aE(_az);});}};return new F(function(){return _aA(_ay[1]);});}},_aH=function(_aI,_aJ){if(0>=_aI){return E(_av);}else{var _aK=function(_aL){var _aM=E(_aL);return (_aM==1)?[1,_aJ,_L]:[1,_aJ,new T(function(){return B(_aK(_aM-1|0));})];};return new F(function(){return _aw(B(_aK(_aI)));});}},_aN=function(_aO,_aP){return new F(function(){return _aH(E(_aO),_aP);});},_aQ=function(_aR){while(1){var _aS=E(_aR);if(!_aS[0]){_aR=[1,I_fromInt(_aS[1])];continue;}else{return new F(function(){return I_toString(_aS[1]);});}}},_aT=function(_aU,_aV){return new F(function(){return _j(fromJSStr(B(_aQ(_aU))),_aV);});},_aW=function(_aX,_aY){var _aZ=E(_aX);if(!_aZ[0]){var _b0=_aZ[1],_b1=E(_aY);return (_b1[0]==0)?_b0<_b1[1]:I_compareInt(_b1[1],_b0)>0;}else{var _b2=_aZ[1],_b3=E(_aY);return (_b3[0]==0)?I_compareInt(_b2,_b3[1])<0:I_compare(_b2,_b3[1])<0;}},_b4=[0,0],_b5=function(_b6,_b7,_b8){if(_b6<=6){return new F(function(){return _aT(_b7,_b8);});}else{if(!B(_aW(_b7,_b4))){return new F(function(){return _aT(_b7,_b8);});}else{return [1,_s,new T(function(){return B(_j(fromJSStr(B(_aQ(_b7))),[1,_r,_b8]));})];}}},_b9=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:243:7-14"));}),_ba=[0,_2H,_2I,_L,_b9,_2H,_2H],_bb=new T(function(){return B(_2F(_ba));}),_bc=function(_){return new F(function(){return die(_bb);});},_bd=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:264:7-14"));}),_be=[0,_2H,_2I,_L,_bd,_2H,_2H],_bf=new T(function(){return B(_2F(_be));}),_bg=function(_){return new F(function(){return die(_bf);});},_bh=",",_bi="[",_bj="]",_bk="{",_bl="}",_bm=":",_bn="\"",_bo="true",_bp="false",_bq="null",_br=new T(function(){return JSON.stringify;}),_bs=function(_bt,_bu){var _bv=E(_bu);switch(_bv[0]){case 0:return [0,new T(function(){return jsShow(_bv[1]);}),_bt];case 1:return [0,new T(function(){var _bw=E(_br)(_bv[1]);return String(_bw);}),_bt];case 2:return (!E(_bv[1]))?[0,_bp,_bt]:[0,_bo,_bt];case 3:var _bx=E(_bv[1]);if(!_bx[0]){return [0,_bi,[1,_bj,_bt]];}else{var _by=new T(function(){var _bz=new T(function(){var _bA=function(_bB){var _bC=E(_bB);if(!_bC[0]){return [1,_bj,_bt];}else{var _bD=new T(function(){var _bE=B(_bs(new T(function(){return B(_bA(_bC[2]));}),_bC[1]));return [1,_bE[1],_bE[2]];});return [1,_bh,_bD];}};return B(_bA(_bx[2]));}),_bF=B(_bs(_bz,_bx[1]));return [1,_bF[1],_bF[2]];});return [0,_bi,_by];}break;case 4:var _bG=E(_bv[1]);if(!_bG[0]){return [0,_bk,[1,_bl,_bt]];}else{var _bH=E(_bG[1]),_bI=new T(function(){var _bJ=new T(function(){var _bK=function(_bL){var _bM=E(_bL);if(!_bM[0]){return [1,_bl,_bt];}else{var _bN=E(_bM[1]),_bO=new T(function(){var _bP=B(_bs(new T(function(){return B(_bK(_bM[2]));}),_bN[2]));return [1,_bP[1],_bP[2]];});return [1,_bh,[1,_bn,[1,_bN[1],[1,_bn,[1,_bm,_bO]]]]];}};return B(_bK(_bG[2]));}),_bQ=B(_bs(_bJ,_bH[2]));return [1,_bQ[1],_bQ[2]];});return [0,_bk,[1,new T(function(){var _bR=E(_br)(E(_bH[1]));return String(_bR);}),[1,_bm,_bI]]];}break;default:return [0,_bq,_bt];}},_bS=new T(function(){return toJSStr(_L);}),_bT=function(_bU){var _bV=B(_bs(_L,_bU)),_bW=jsCat([1,_bV[1],_bV[2]],E(_bS));return E(_bW);},_bX=0,_bY="state-table-tbody",_bZ="add-state",_c0="word-table-tbody",_c1="example-table-tbody",_c2="conversion-table-tbody",_c3="alphabet-table-tbody",_c4="add-alphabet",_c5="transition-table-tbody",_c6=new T(function(){return B(unCStr("] },  layout: {    name: \'cose\',    directed: true,    roots: \'#a\'  }  });   "));}),_c7="add-transition",_c8="export-button",_c9="import-button",_ca="accept-check-button",_cb="accept-check-result",_cc=function(_cd,_ce,_cf){var _cg=E(_cf);if(!_cg[0]){return [0];}else{var _ch=_cg[1],_ci=_cg[2];return (!B(A(_cd,[_ce,_ch])))?[1,_ch,new T(function(){return B(_cc(_cd,_ce,_ci));})]:E(_ci);}},_cj=(function(s){var x = eval(s);return (typeof x === 'undefined') ? 'undefined' : x.toString();}),_ck=function(_cl,_cm){while(1){var _cn=B((function(_co,_cp){var _cq=E(_cp);if(!_cq[0]){return [0];}else{var _cr=_cq[1],_cs=_cq[2];if(!B(A(_co,[_cr]))){var _ct=_co;_cl=_ct;_cm=_cs;return null;}else{return [1,_cr,new T(function(){return B(_ck(_co,_cs));})];}}})(_cl,_cm));if(_cn!=null){return _cn;}}},_cu="value",_cv=(function(e,p){return e[p].toString();}),_cw=function(_cx){return E(E(_cx)[1]);},_cy=function(_cz){return E(E(_cz)[2]);},_cA=function(_cB){return new F(function(){return fromJSStr(E(_cB));});},_cC=function(_cD){return E(E(_cD)[1]);},_cE=function(_cF){return E(E(_cF)[2]);},_cG=function(_cH,_cI,_cJ,_cK){var _cL=new T(function(){var _cM=function(_){var _cN=E(_cv)(B(A(_cC,[_cH,_cJ])),E(_cK));return new T(function(){return String(_cN);});};return E(_cM);});return new F(function(){return A(_cE,[_cI,_cL]);});},_cO=function(_cP){return E(E(_cP)[4]);},_cQ=function(_cR,_cS,_cT,_cU){var _cV=B(_cw(_cS)),_cW=new T(function(){return B(_cO(_cV));}),_cX=function(_cY){return new F(function(){return A(_cW,[new T(function(){return B(_cA(_cY));})]);});},_cZ=new T(function(){return B(_cG(_cR,_cS,_cT,new T(function(){return toJSStr(E(_cU));},1)));});return new F(function(){return A(_cy,[_cV,_cZ,_cX]);});},_d0=function(_d1){var _d2=E(_d1);if(!_d2[0]){return [0];}else{return new F(function(){return _j(_d2[1],new T(function(){return B(_d0(_d2[2]));},1));});}},_d3=(function(e,p,v){e[p] = v;}),_d4=new T(function(){return B(unCStr("<span class=\"label label-danger\">X</span>"));}),_d5=function(_d6,_d7){var _d8=E(_d6),_d9=E(_d7);if(!B(_97(_d8[1],_d9[1]))){return false;}else{if(E(_d8[2])!=E(_d9[2])){return false;}else{return new F(function(){return _97(_d8[3],_d9[3]);});}}},_da=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-transition\">\u8ffd\u52a0</button>"));}),_db=[1,_da,_L],_dc=new T(function(){return B(unCStr("</select>"));}),_dd=new T(function(){return B(unCStr("</option>"));}),_de=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:242:7-15"));}),_df=[0,_2H,_2I,_L,_de,_2H,_2H],_dg=new T(function(){return B(_2F(_df));}),_dh=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:223:7-15"));}),_di=[0,_2H,_2I,_L,_dh,_2H,_2H],_dj=new T(function(){return B(_2F(_di));}),_dk=new T(function(){return B(unCStr(">"));}),_dl=new T(function(){return B(unCStr(" checked=\"checked\""));}),_dm=new T(function(){return B(_j(_dl,_dk));}),_dn=new T(function(){return B(unCStr("\'#494\'}}"));}),_do=new T(function(){return B(unCStr("\'#c4f\'}}"));}),_dp=new T(function(){return B(unCStr("\'#f94\'}}"));}),_dq=(function(id){return document.getElementById(id);}),_dr=function(_ds,_dt){var _du=function(_){var _dv=E(_dq)(E(_dt)),_dw=__eq(_dv,E(_34));return (E(_dw)==0)?[1,_dv]:_2H;};return new F(function(){return A(_cE,[_ds,_du]);});},_dx="accept-check-text",_dy=new T(function(){return B(_dr(_4d,_dx));}),_dz=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_dA=function(_dB){return new F(function(){return _5f([0,new T(function(){return B(_5t(_dB,_dz));})],_4X);});},_dC=new T(function(){return B(_dA("Main.hs:281:11-64|Right auto"));}),_dD="import-text",_dE=new T(function(){return B(_dr(_4d,_dD));}),_dF=new T(function(){return B(unCStr("innerText"));}),_dG=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:274:7-12"));}),_dH="export-text",_dI=new T(function(){return B(_dr(_4d,_dH));}),_dJ="select-target",_dK=new T(function(){return B(_dr(_4d,_dJ));}),_dL="select-alphabet",_dM=new T(function(){return B(_dr(_4d,_dL));}),_dN="select-source",_dO=new T(function(){return B(_dr(_4d,_dN));}),_dP=function(_dQ,_dR){while(1){var _dS=E(_dQ);if(!_dS[0]){var _dT=_dS[1],_dU=E(_dR);if(!_dU[0]){var _dV=_dU[1],_dW=addC(_dT,_dV);if(!E(_dW[2])){return [0,_dW[1]];}else{_dQ=[1,I_fromInt(_dT)];_dR=[1,I_fromInt(_dV)];continue;}}else{_dQ=[1,I_fromInt(_dT)];_dR=_dU;continue;}}else{var _dX=E(_dR);if(!_dX[0]){_dQ=_dS;_dR=[1,I_fromInt(_dX[1])];continue;}else{return [1,I_add(_dS[1],_dX[1])];}}}},_dY=function(_dZ,_e0){var _e1=E(_dZ);return [0,_e1,new T(function(){var _e2=B(_dY(B(_dP(_e1,_e0)),_e0));return [1,_e2[1],_e2[2]];})];},_e3=[0,1],_e4=new T(function(){var _e5=B(_dY(_e3,_e3));return [1,_e5[1],_e5[2]];}),_e6=new T(function(){return B(unCStr("\">\u524a\u9664</button>"));}),_e7=new T(function(){return B(unCStr("select-target"));}),_e8=new T(function(){return B(unCStr("select-source"));}),_e9="new-alphabet",_ea=new T(function(){return B(_dr(_4d,_e9));}),_eb="new-state",_ec=new T(function(){return B(_dr(_4d,_eb));}),_ed=new T(function(){return B(_5E("Main.hs:(216,9)-(218,58)|case"));}),_ee=new T(function(){return B(unCStr("true"));}),_ef=new T(function(){return B(unCStr("false"));}),_eg=new T(function(){return B(unCStr("checked"));}),_eh=new T(function(){return B(unCStr(","));}),_ei=34,_ej=[1,_ei,_L],_ek=new T(function(){return B(unCStr("!!: negative index"));}),_el=new T(function(){return B(unCStr("Prelude."));}),_em=new T(function(){return B(_j(_el,_ek));}),_en=new T(function(){return B(err(_em));}),_eo=new T(function(){return B(unCStr("!!: index too large"));}),_ep=new T(function(){return B(_j(_el,_eo));}),_eq=new T(function(){return B(err(_ep));}),_er=function(_es,_et){while(1){var _eu=E(_es);if(!_eu[0]){return E(_eq);}else{var _ev=E(_et);if(!_ev){return E(_eu[1]);}else{_es=_eu[2];_et=_ev-1|0;continue;}}}},_ew=function(_ex,_ey){if(_ey>=0){return new F(function(){return _er(_ex,_ey);});}else{return E(_en);}},_ez=new T(function(){return B(unCStr("ACK"));}),_eA=new T(function(){return B(unCStr("BEL"));}),_eB=new T(function(){return B(unCStr("BS"));}),_eC=new T(function(){return B(unCStr("SP"));}),_eD=[1,_eC,_L],_eE=new T(function(){return B(unCStr("US"));}),_eF=[1,_eE,_eD],_eG=new T(function(){return B(unCStr("RS"));}),_eH=[1,_eG,_eF],_eI=new T(function(){return B(unCStr("GS"));}),_eJ=[1,_eI,_eH],_eK=new T(function(){return B(unCStr("FS"));}),_eL=[1,_eK,_eJ],_eM=new T(function(){return B(unCStr("ESC"));}),_eN=[1,_eM,_eL],_eO=new T(function(){return B(unCStr("SUB"));}),_eP=[1,_eO,_eN],_eQ=new T(function(){return B(unCStr("EM"));}),_eR=[1,_eQ,_eP],_eS=new T(function(){return B(unCStr("CAN"));}),_eT=[1,_eS,_eR],_eU=new T(function(){return B(unCStr("ETB"));}),_eV=[1,_eU,_eT],_eW=new T(function(){return B(unCStr("SYN"));}),_eX=[1,_eW,_eV],_eY=new T(function(){return B(unCStr("NAK"));}),_eZ=[1,_eY,_eX],_f0=new T(function(){return B(unCStr("DC4"));}),_f1=[1,_f0,_eZ],_f2=new T(function(){return B(unCStr("DC3"));}),_f3=[1,_f2,_f1],_f4=new T(function(){return B(unCStr("DC2"));}),_f5=[1,_f4,_f3],_f6=new T(function(){return B(unCStr("DC1"));}),_f7=[1,_f6,_f5],_f8=new T(function(){return B(unCStr("DLE"));}),_f9=[1,_f8,_f7],_fa=new T(function(){return B(unCStr("SI"));}),_fb=[1,_fa,_f9],_fc=new T(function(){return B(unCStr("SO"));}),_fd=[1,_fc,_fb],_fe=new T(function(){return B(unCStr("CR"));}),_ff=[1,_fe,_fd],_fg=new T(function(){return B(unCStr("FF"));}),_fh=[1,_fg,_ff],_fi=new T(function(){return B(unCStr("VT"));}),_fj=[1,_fi,_fh],_fk=new T(function(){return B(unCStr("LF"));}),_fl=[1,_fk,_fj],_fm=new T(function(){return B(unCStr("HT"));}),_fn=[1,_fm,_fl],_fo=[1,_eB,_fn],_fp=[1,_eA,_fo],_fq=[1,_ez,_fp],_fr=new T(function(){return B(unCStr("ENQ"));}),_fs=[1,_fr,_fq],_ft=new T(function(){return B(unCStr("EOT"));}),_fu=[1,_ft,_fs],_fv=new T(function(){return B(unCStr("ETX"));}),_fw=[1,_fv,_fu],_fx=new T(function(){return B(unCStr("STX"));}),_fy=[1,_fx,_fw],_fz=new T(function(){return B(unCStr("SOH"));}),_fA=[1,_fz,_fy],_fB=new T(function(){return B(unCStr("NUL"));}),_fC=[1,_fB,_fA],_fD=92,_fE=new T(function(){return B(unCStr("\\DEL"));}),_fF=new T(function(){return B(unCStr("\\a"));}),_fG=new T(function(){return B(unCStr("\\\\"));}),_fH=new T(function(){return B(unCStr("\\SO"));}),_fI=new T(function(){return B(unCStr("\\r"));}),_fJ=new T(function(){return B(unCStr("\\f"));}),_fK=new T(function(){return B(unCStr("\\v"));}),_fL=new T(function(){return B(unCStr("\\n"));}),_fM=new T(function(){return B(unCStr("\\t"));}),_fN=new T(function(){return B(unCStr("\\b"));}),_fO=function(_fP,_fQ){if(_fP<=127){var _fR=E(_fP);switch(_fR){case 92:return new F(function(){return _j(_fG,_fQ);});break;case 127:return new F(function(){return _j(_fE,_fQ);});break;default:if(_fR<32){var _fS=E(_fR);switch(_fS){case 7:return new F(function(){return _j(_fF,_fQ);});break;case 8:return new F(function(){return _j(_fN,_fQ);});break;case 9:return new F(function(){return _j(_fM,_fQ);});break;case 10:return new F(function(){return _j(_fL,_fQ);});break;case 11:return new F(function(){return _j(_fK,_fQ);});break;case 12:return new F(function(){return _j(_fJ,_fQ);});break;case 13:return new F(function(){return _j(_fI,_fQ);});break;case 14:return new F(function(){return _j(_fH,new T(function(){var _fT=E(_fQ);if(!_fT[0]){return [0];}else{if(E(_fT[1])==72){return B(unAppCStr("\\&",_fT));}else{return E(_fT);}}},1));});break;default:return new F(function(){return _j([1,_fD,new T(function(){return B(_ew(_fC,_fS));})],_fQ);});}}else{return [1,_fR,_fQ];}}}else{var _fU=new T(function(){var _fV=jsShowI(_fP);return B(_j(fromJSStr(_fV),new T(function(){var _fW=E(_fQ);if(!_fW[0]){return [0];}else{var _fX=E(_fW[1]);if(_fX<48){return E(_fW);}else{if(_fX>57){return E(_fW);}else{return B(unAppCStr("\\&",_fW));}}}},1)));});return [1,_fD,_fU];}},_fY=39,_fZ=[1,_fY,_L],_g0=new T(function(){return B(unCStr("}}"));}),_g1=new T(function(){return B(unCStr("\'\\\'\'"));}),_g2=new T(function(){return B(_j(_g1,_L));}),_g3=new T(function(){return B(unCStr("\\\""));}),_g4=function(_g5,_g6){var _g7=E(_g5);if(!_g7[0]){return E(_g6);}else{var _g8=_g7[2],_g9=E(_g7[1]);if(_g9==34){return new F(function(){return _j(_g3,new T(function(){return B(_g4(_g8,_g6));},1));});}else{return new F(function(){return _fO(_g9,new T(function(){return B(_g4(_g8,_g6));}));});}}},_ga=function(_gb,_gc,_gd){var _ge=new T(function(){var _gf=new T(function(){var _gg=new T(function(){var _gh=new T(function(){var _gi=new T(function(){var _gj=E(_gc);if(_gj==39){return B(_j(_g2,_g0));}else{return B(_j([1,_fY,new T(function(){return B(_fO(_gj,_fZ));})],_g0));}});return B(unAppCStr(", label: ",_gi));},1);return B(_j([1,_ei,new T(function(){return B(_g4(_gd,_ej));})],_gh));});return B(unAppCStr(", target: ",_gg));},1);return B(_j([1,_ei,new T(function(){return B(_g4(_gb,_ej));})],_gf));});return new F(function(){return unAppCStr("{data: {source: ",_ge);});},_gk=function(_gl){var _gm=E(_gl);return new F(function(){return _ga(_gm[1],_gm[2],_gm[3]);});},_gn=new T(function(){return B(unCStr("{\"final\":[\"q0\",\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"0\",\"q0\"],[\"q0\",\"1\",\"q1\"],[\"q1\",\"1\",\"q0\"],[\"q1\",\"0\",\"q2\"],[\"q2\",\"0\",\"q1\"],[\"q2\",\"1\",\"q2\"]],\"alphabet\":\"01\",\"state\":[\"q0\",\"q1\",\"q2\"]}"));}),_go=new T(function(){return B(unCStr("DFA"));}),_gp=new T(function(){return B(unCStr("multiple of 3"));}),_gq=[0,_gp,_go,_gn],_gr=[1,_gq,_L],_gs=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"a\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q1\",\"b\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_gt=new T(function(){return B(unCStr("NFA"));}),_gu=new T(function(){return B(unCStr("worst NFAtoDFA efficiency"));}),_gv=[0,_gu,_gt,_gs],_gw=[1,_gv,_gr],_gx=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"b\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_gy=new T(function(){return B(unCStr("exmple2"));}),_gz=[0,_gy,_gt,_gx],_gA=[1,_gz,_gw],_gB=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q1\"],[\"q0\",\"b\",\"q2\"],[\"q1\",\"a\",\"q3\"],[\"q2\",\"a\",\"q2\"],[\"q2\",\"b\",\"q3\"],[\"q3\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_gC=new T(function(){return B(unCStr("exmple1"));}),_gD=[0,_gC,_gt,_gB],_gE=[1,_gD,_gA],_gF=function(_gG,_gH,_gI){var _gJ=E(_gH);return new F(function(){return A(_gG,[_gJ,new T(function(){return B(_gF(_gG,B(_dP(_gJ,_gI)),_gI));})]);});},_gK=function(_gL,_gM,_gN){var _gO=E(_gN);return (_gO[0]==0)?[0]:[1,[0,_gL,_gO[1]],new T(function(){return B(A(_gM,[_gO[2]]));})];},_gP=new T(function(){return B(_gF(_gK,_e3,_e3));}),_gQ=new T(function(){return B(A(_gP,[_gE]));}),_gR=new T(function(){return B(unCStr("innerHTML"));}),_gS=new T(function(){return B(unCStr("]"));}),_gT=function(_gU,_gV){var _gW=E(_gV);return (_gW[0]==0)?[0]:[1,_gU,[1,_gW[1],new T(function(){return B(_gT(_gU,_gW[2]));})]];},_gX=function(_gY){var _gZ=new T(function(){var _h0=E(_gY);if(!_h0[0]){return E(_gS);}else{return B(_j(B(_d0([1,_h0[1],new T(function(){return B(_gT(_eh,_h0[2]));})])),_gS));}});return new F(function(){return unAppCStr("[",_gZ);});},_h1=function(_h2){var _h3=E(_h2);return [0,new T(function(){return B(_gX(_h3[1]));}),_h3[2],new T(function(){return B(_gX(_h3[3]));})];},_h4=new T(function(){return B(unCStr("\">Load</button>"));}),_h5=function(_h6,_h7,_h8){var _h9=E(_h8);if(!_h9[0]){return [0];}else{var _ha=new T(function(){var _hb=E(_h9[1]),_hc=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"load-",new T(function(){return B(_j(B(_b5(0,_h6,_L)),_h4));})));});return B(_as(_hb[1],[1,_hb[2],[1,_hc,_L]]));});return new F(function(){return _j(B(unAppCStr("<tr>",_ha)),new T(function(){return B(A(_h7,[_h9[2]]));},1));});}},_hd=new T(function(){return B(_gF(_h5,_e3,_e3));}),_he=function(_hf){var _hg=E(_hf);return [0,_hg[1],_hg[2]];},_hh=new T(function(){return B(_6E(_he,_gE));}),_hi=new T(function(){return B(A(_hd,[_hh]));}),_hj=new T(function(){return B(_dA("Main.hs:309:15-68|Right auto"));}),_hk=new T(function(){return B(unCStr("\">Go</button>"));}),_hl=function(_hm,_hn,_ho){var _hp=E(_ho);if(!_hp[0]){return [0];}else{var _hq=new T(function(){var _hr=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"convert-",new T(function(){return B(_j(B(_b5(0,_hm,_L)),_hk));})));});return B(_as(_hp[1],[1,_hr,_L]));});return new F(function(){return _j(B(unAppCStr("<tr>",_hq)),new T(function(){return B(A(_hn,[_hp[2]]));},1));});}},_hs=new T(function(){return B(_gF(_hl,_e3,_e3));}),_ht=new T(function(){return B(unCStr("NFAtoDFA"));}),_hu=function(_hv,_hw,_hx){while(1){var _hy=E(_hw);if(!_hy[0]){return (E(_hx)[0]==0)?true:false;}else{var _hz=E(_hx);if(!_hz[0]){return false;}else{if(!B(A(_9F,[_hv,_hy[1],_hz[1]]))){return false;}else{_hw=_hy[2];_hx=_hz[2];continue;}}}}},_hA=function(_hB,_hC,_hD){return (!B(_hu(_hB,_hC,_hD)))?true:false;},_hE=function(_hF){return [0,function(_hG,_hH){return new F(function(){return _hu(_hF,_hG,_hH);});},function(_hG,_hH){return new F(function(){return _hA(_hF,_hG,_hH);});}];},_hI=function(_hJ){return E(E(_hJ)[1]);},_hK=function(_hL,_hM,_hN){while(1){var _hO=E(_hN);if(!_hO[0]){return false;}else{if(!B(A(_hL,[_hO[1],_hM]))){_hN=_hO[2];continue;}else{return true;}}}},_hP=function(_hQ,_hR){var _hS=function(_hT,_hU){while(1){var _hV=B((function(_hW,_hX){var _hY=E(_hW);if(!_hY[0]){return [0];}else{var _hZ=_hY[1],_i0=_hY[2];if(!B(_hK(_hQ,_hZ,_hX))){return [1,_hZ,new T(function(){return B(_hS(_i0,[1,_hZ,_hX]));})];}else{var _i1=_hX;_hT=_i0;_hU=_i1;return null;}}})(_hT,_hU));if(_hV!=null){return _hV;}}};return new F(function(){return _hS(_hR,_L);});},_i2=function(_i3,_i4,_i5,_i6){var _i7=function(_i8){while(1){var _i9=B((function(_ia){var _ib=E(_ia);if(!_ib[0]){return [0];}else{var _ic=_ib[2],_id=E(_ib[1]);if(!B(_9H(_i3,_id[1],_i5))){_i8=_ic;return null;}else{var _ie=E(_i6);if(_ie!=E(_id[2])){var _if=function(_ig){while(1){var _ih=B((function(_ii){var _ij=E(_ii);if(!_ij[0]){return [0];}else{var _ik=_ij[2],_il=E(_ij[1]);if(!B(_9H(_i3,_il[1],_i5))){_ig=_ik;return null;}else{if(_ie!=E(_il[2])){_ig=_ik;return null;}else{return [1,_il[3],new T(function(){return B(_if(_ik));})];}}}})(_ig));if(_ih!=null){return _ih;}}};return new F(function(){return _if(_ic);});}else{var _im=new T(function(){var _in=function(_io){while(1){var _ip=B((function(_iq){var _ir=E(_iq);if(!_ir[0]){return [0];}else{var _is=_ir[2],_it=E(_ir[1]);if(!B(_9H(_i3,_it[1],_i5))){_io=_is;return null;}else{if(_ie!=E(_it[2])){_io=_is;return null;}else{return [1,_it[3],new T(function(){return B(_in(_is));})];}}}})(_io));if(_ip!=null){return _ip;}}};return B(_in(_ic));});return [1,_id[3],_im];}}}})(_i8));if(_i9!=null){return _i9;}}};return new F(function(){return _hP(new T(function(){return B(_9F(_i3));}),B(_i7(E(E(E(E(_i4)[3])[3])[2])[1])));});},_iu=function(_iv,_iw,_ix,_iy){return new F(function(){return _i2(_iv,E(_iw)[1],_ix,_iy);});},_iz=function(_iA,_iB,_iC){var _iD=E(_iB);if(!_iD[0]){return [0];}else{var _iE=E(_iC);if(!_iE[0]){return [0];}else{var _iF=function(_iG){while(1){var _iH=B((function(_iI){var _iJ=E(_iI);if(!_iJ[0]){return [0];}else{var _iK=_iJ[1],_iL=_iJ[2];if(!B(_9B(new T(function(){return B(A(_iA,[_iK]));}),_iE))){_iG=_iL;return null;}else{return [1,_iK,new T(function(){return B(_iF(_iL));})];}}})(_iG));if(_iH!=null){return _iH;}}};return new F(function(){return _iF(_iD);});}}},_iM=function(_iN){var _iO=new T(function(){return B(_hI(_iN));}),_iP=new T(function(){return B(_hE(_iO));}),_iQ=new T(function(){return B(_9F(_iO));}),_iR=function(_iS,_iT){var _iU=E(_iS),_iV=E(_iT);if(!B(_hu(_iO,_iU[1],_iV[1]))){return false;}else{if(E(_iU[2])!=E(_iV[2])){return false;}else{return new F(function(){return _hu(_iO,_iU[3],_iV[3]);});}}},_iW=function(_iX,_6M){return new F(function(){return _hu(_iO,_iX,_6M);});},_iY=function(_iZ){var _j0=new T(function(){var _j1=new T(function(){return E(E(E(E(E(E(E(_iZ)[1])[3])[3])[3])[2])[1]);}),_j2=new T(function(){return E(E(E(E(_iZ)[1])[2])[1]);}),_j3=function(_j4,_j5,_j6,_j7){while(1){var _j8=B((function(_j9,_ja,_jb,_jc){var _jd=E(_j9);if(!_jd[0]){return [0,_ja,_jb,_jc];}else{var _je=_jd[1],_jf=[1,_je,_ja],_jg=function(_jh){while(1){var _ji=B((function(_jj){var _jk=E(_jj);if(!_jk[0]){return E(_jd[2]);}else{var _jl=_jk[1],_jm=_jk[2];if(!B(_9H(_iP,new T(function(){return B(_i2(_iO,E(_iZ)[1],_je,_jl));}),_jf))){return [1,new T(function(){return B(_iu(_iO,_iZ,_je,_jl));}),new T(function(){return B(_jg(_jm));})];}else{_jh=_jm;return null;}}})(_jh));if(_ji!=null){return _ji;}}},_jn=new T(function(){var _jo=function(_jp){var _jq=E(_jp);if(!_jq[0]){return E(_jb);}else{var _jr=_jq[1];return [1,[0,_je,_jr,new T(function(){return B(_iu(_iO,_iZ,_je,_jr));})],new T(function(){return B(_jo(_jq[2]));})];}};return B(_hP(_iR,B(_jo(_j1))));});_j4=B(_hP(_iW,B(_jg(_j1))));_j5=_jf;_j6=_jn;_j7=new T(function(){if(!B(_hu(_iO,B(_iz(_iQ,_je,_j2)),_L))){return [1,_je,_jc];}else{return E(_jc);}});return null;}})(_j4,_j5,_j6,_j7));if(_j8!=null){return _j8;}}},_js=function(_jt,_ju,_jv,_jw,_jx){var _jy=[1,_jt,_jv],_jz=function(_jA){while(1){var _jB=B((function(_jC){var _jD=E(_jC);if(!_jD[0]){return E(_ju);}else{var _jE=_jD[1],_jF=_jD[2];if(!B(_9H(_iP,new T(function(){return B(_i2(_iO,E(_iZ)[1],_jt,_jE));}),_jy))){return [1,new T(function(){return B(_iu(_iO,_iZ,_jt,_jE));}),new T(function(){return B(_jz(_jF));})];}else{_jA=_jF;return null;}}})(_jA));if(_jB!=null){return _jB;}}},_jG=new T(function(){var _jH=function(_jI){var _jJ=E(_jI);if(!_jJ[0]){return E(_jw);}else{var _jK=_jJ[1];return [1,[0,_jt,_jK,new T(function(){return B(_iu(_iO,_iZ,_jt,_jK));})],new T(function(){return B(_jH(_jJ[2]));})];}};return B(_hP(_iR,B(_jH(_j1))));});return new F(function(){return _j3(B(_hP(_iW,B(_jz(_j1)))),_jy,_jG,new T(function(){if(!B(_hu(_iO,B(_iz(_iQ,_jt,_j2)),_L))){return [1,_jt,_jx];}else{return E(_jx);}}));});},_jL=B(_js([1,new T(function(){return E(E(E(E(E(_iZ)[1])[3])[2])[1]);}),_L],_L,_L,_L,_L));return [0,_jL[1],_jL[2],_jL[3]];});return [0,[1,_,[0,new T(function(){return E(E(_j0)[3]);})],[1,_,[0,[1,new T(function(){return E(E(E(E(E(_iZ)[1])[3])[2])[1]);}),_L]],[1,_,[0,new T(function(){return E(E(_j0)[2]);})],[1,_,[0,new T(function(){return E(E(E(E(E(E(E(_iZ)[1])[3])[3])[3])[2])[1]);})],[1,_,[0,new T(function(){return E(E(_j0)[1]);})],_0]]]]]];};return E(_iY);},_jM=function(_jN,_jO){return new F(function(){return _iM(_jO);});},_jP=[0,_ht,_jM],_jQ=[1,_jP,_L],_jR=function(_jS){return E(E(_jS)[1]);},_jT=new T(function(){return B(_6E(_jR,_jQ));}),_jU=new T(function(){return B(A(_hs,[_jT]));}),_jV=function(_jW,_jX,_jY){var _jZ=E(_jY);return (_jZ[0]==0)?[0]:[1,[0,_jW,_jZ[1]],new T(function(){return B(A(_jX,[_jZ[2]]));})];},_k0=new T(function(){return B(_gF(_jV,_e3,_e3));}),_k1=new T(function(){return B(A(_k0,[_jQ]));}),_k2=function(_k3,_k4){if(_k3<=_k4){var _k5=function(_k6){return [1,_k6,new T(function(){if(_k6!=_k4){return B(_k5(_k6+1|0));}else{return [0];}})];};return new F(function(){return _k5(_k3);});}else{return [0];}},_k7=new T(function(){return B(_k2(1,5));}),_k8=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:287:7-12"));}),_k9=[0,_2H,_2I,_L,_k8,_2H,_2H],_ka=new T(function(){return B(_2F(_k9));}),_kb=new T(function(){return B(unCStr("<span class=\"label label-success\">O</span>"));}),_kc=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:279:7-12"));}),_kd=[0,_2H,_2I,_L,_kc,_2H,_2H],_ke=new T(function(){return B(_2F(_kd));}),_kf=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:266:7-15"));}),_kg=[0,_2H,_2I,_L,_kf,_2H,_2H],_kh=new T(function(){return B(_2F(_kg));}),_ki=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:263:7-15"));}),_kj=[0,_2H,_2I,_L,_ki,_2H,_2H],_kk=new T(function(){return B(_2F(_kj));}),_kl=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:260:7-15"));}),_km=[0,_2H,_2I,_L,_kl,_2H,_2H],_kn=new T(function(){return B(_2F(_km));}),_ko=function(_kp){return E(E(_kp)[1]);},_kq=function(_kr){return E(E(_kr)[2]);},_ks=function(_kt){return E(E(_kt)[1]);},_ku=function(_){return new F(function(){return nMV(_2H);});},_kv=new T(function(){return B(_30(_ku));}),_kw=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_kx=function(_ky){return E(E(_ky)[2]);},_kz=function(_kA,_kB,_kC,_kD,_kE,_kF){var _kG=B(_ko(_kA)),_kH=B(_cw(_kG)),_kI=new T(function(){return B(_cE(_kG));}),_kJ=new T(function(){return B(_cO(_kH));}),_kK=new T(function(){return B(A(_cC,[_kB,_kD]));}),_kL=new T(function(){return B(A(_ks,[_kC,_kE]));}),_kM=function(_kN){return new F(function(){return A(_kJ,[[0,_kL,_kK,_kN]]);});},_kO=function(_kP){var _kQ=new T(function(){var _kR=new T(function(){var _kS=__createJSFunc(2,function(_kT,_){var _kU=B(A(E(_kP),[_kT,_]));return _34;}),_kV=_kS;return function(_){return new F(function(){return E(_kw)(E(_kK),E(_kL),_kV);});};});return B(A(_kI,[_kR]));});return new F(function(){return A(_cy,[_kH,_kQ,_kM]);});},_kW=new T(function(){var _kX=new T(function(){return B(_cE(_kG));}),_kY=function(_kZ){var _l0=new T(function(){return B(A(_kX,[function(_){var _=wMV(E(_kv),[1,_kZ]);return new F(function(){return A(_kq,[_kC,_kE,_kZ,_]);});}]));});return new F(function(){return A(_cy,[_kH,_l0,_kF]);});};return B(A(_kx,[_kA,_kY]));});return new F(function(){return A(_cy,[_kH,_kW,_kO]);});},_l1=new T(function(){return B(unCStr(" found!"));}),_l2=function(_l3){return new F(function(){return err(B(unAppCStr("No element with ID ",new T(function(){return B(_j(fromJSStr(E(_l3)),_l1));}))));});},_l4=function(_l5,_l6,_l7){var _l8=new T(function(){var _l9=function(_){var _la=E(_dq)(E(_l6)),_lb=__eq(_la,E(_34));return (E(_lb)==0)?[1,_la]:_2H;};return B(A(_cE,[_l5,_l9]));});return new F(function(){return A(_cy,[B(_cw(_l5)),_l8,function(_lc){var _ld=E(_lc);if(!_ld[0]){return new F(function(){return _l2(_l6);});}else{return new F(function(){return A(_l7,[_ld[1]]);});}}]);});},_le=new T(function(){return B(unCStr("<input type=\"text\" class=\"form-control input-sm\" id=\"new-alphabet\">"));}),_lf=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-alphabet\">\u8ffd\u52a0</button>"));}),_lg=[1,_lf,_L],_lh=new T(function(){return B(_as(_le,_lg));}),_li=new T(function(){return B(unAppCStr("<tr>",_lh));}),_lj=new T(function(){return B(_j(_li,_L));}),_lk=new T(function(){return B(unCStr("<input type=\"text\" class=\"form-control input-sm\" id=\"new-state\">"));}),_ll=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-state\">\u8ffd\u52a0</button>"));}),_lm=[1,_ll,_L],_ln=new T(function(){return B(_as(_lk,_lm));}),_lo=new T(function(){return B(unAppCStr("<tr>",_ln));}),_lp=new T(function(){return B(_j(_lo,_L));}),_lq=function(_lr,_){var _ls=rMV(_lr),_lt=new T(function(){var _lu=E(E(_ls)[1]),_lv=E(_lu[3]),_lw=E(_lv[3]),_lx=new T(function(){var _ly=new T(function(){var _lz=B(_6E(_gk,E(_lw[2])[1]));if(!_lz[0]){return E(_c6);}else{return B(_j(B(_d0([1,_lz[1],new T(function(){return B(_gT(_eh,_lz[2]));})])),_c6));}});return B(unAppCStr("], edges: [",_ly));}),_lA=function(_lB){var _lC=new T(function(){var _lD=new T(function(){var _lE=new T(function(){var _lF=new T(function(){return B(unAppCStr(", color: ",new T(function(){if(!B(_9H(_f,_lB,E(_lu[2])[1]))){if(!B(_97(_lB,E(_lv[2])[1]))){return E(_dp);}else{return E(_do);}}else{return E(_dn);}})));},1);return B(_j([1,_ei,new T(function(){return B(_g4(_lB,_ej));})],_lF));});return B(unAppCStr(", id: ",_lE));},1);return B(_j([1,_ei,new T(function(){return B(_g4(_lB,_ej));})],_lD));});return new F(function(){return unAppCStr("{data: {label: ",_lC);});},_lG=B(_6E(_lA,E(E(E(_lw[3])[3])[2])[1]));if(!_lG[0]){return E(_lx);}else{return B(_j(B(_d0([1,_lG[1],new T(function(){return B(_gT(_eh,_lG[2]));})])),_lx));}}),_lH=E(_cj)(toJSStr(B(unAppCStr("  var cy = cytoscape({  container: document.getElementById(\'cy\'),  style: cytoscape.stylesheet()    .selector(\'node\').css({      \'background-color\': \'data(color)\',      \'text-valign\': \'center\',      \'content\': \'data(id)\'    })    .selector(\'edge\').css({      \'target-arrow-shape\': \'triangle\',      \'line-color\': \'#a9f\',      \'target-arrow-color\': \'#a9f\',      \'text-valign\': \'top\',      \'width\': 3,      \'content\': \'data(label)\'    }),  elements: { nodes: [",_lt)))),_lI=function(_lJ,_){var _lK=rMV(_lr),_lL=new T(function(){return E(E(E(E(_lK)[1])[2])[1]);}),_lM=function(_lN,_lO){var _lP=E(_lN);if(!_lP[0]){return E(_lp);}else{var _lQ=_lP[1],_lR=E(_lO);if(!_lR[0]){return E(_lp);}else{var _lS=_lR[1],_lT=new T(function(){var _lU=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-state-",new T(function(){return B(_j(B(_b5(0,_lQ,_L)),_e6));})));}),_lV=new T(function(){var _lW=new T(function(){var _lX=new T(function(){return B(unAppCStr("\"",new T(function(){if(!B(_9H(_f,_lS,_lL))){return E(_dk);}else{return E(_dm);}})));},1);return B(_j(B(_b5(0,_lQ,_L)),_lX));});return B(unAppCStr("<input type=\"checkbox\" id=\"state-final-",_lW));});return B(_as(_lS,[1,_lV,[1,_lU,_L]]));});return new F(function(){return _j(B(unAppCStr("<tr>",_lT)),new T(function(){return B(_lM(_lP[2],_lR[2]));},1));});}}},_lY=E(_d3)(E(_lJ),toJSStr(E(_gR)),toJSStr(B(_lM(_e4,new T(function(){return E(E(E(E(E(E(E(E(_lK)[1])[3])[3])[3])[3])[2])[1]);},1)))));return new F(function(){return _3x(_);});},_lZ=B(A(_l4,[_4d,_bY,_lI,_])),_m0=rMV(_lr),_m1=function(_m2,_m3,_){while(1){var _m4=B((function(_m5,_m6,_){var _m7=E(_m5);if(!_m7[0]){return _3w;}else{var _m8=_m7[1],_m9=E(_m6);if(!_m9[0]){return _3w;}else{var _ma=_m9[1],_mb=function(_){var _mc=rMV(_lr),_md=[0,new T(function(){var _me=E(E(_mc)[1]),_mf=new T(function(){var _mg=E(_me[3]),_mh=new T(function(){var _mi=E(_mg[3]),_mj=new T(function(){var _mk=E(_mi[3]),_ml=new T(function(){var _mm=E(_mk[3]);return [1,_,[0,new T(function(){return B(_cc(_97,_ma,E(_mm[2])[1]));})],_mm[3]];});return [1,_,_mk[2],_ml];});return [1,_,_mi[2],_mj];});return [1,_,_mg[2],_mh];});return [1,_,_me[2],_mf];})],_=wMV(_lr,_md),_mn=rMV(_lr),_mo=[0,new T(function(){var _mp=E(E(_mn)[1]),_mq=new T(function(){var _mr=E(_mp[3]),_ms=new T(function(){var _mt=E(_mr[3]),_mu=new T(function(){return B(_ck(function(_mv){var _mw=E(_mv);if(!B(_7(_ma,_mw[1]))){return new F(function(){return _c(_ma,_mw[3]);});}else{return false;}},E(_mt[2])[1]));});return [1,_,[0,_mu],_mt[3]];});return [1,_,_mr[2],_ms];});return [1,_,_mp[2],_mq];})],_=wMV(_lr,_mo);return new F(function(){return _lq(_lr,_);});},_mx=function(_my,_){return new F(function(){return _mb(_);});},_mz=new T(function(){return toJSStr(B(unAppCStr("delete-state-",new T(function(){return B(_b5(0,_m8,_L));}))));}),_mA=B(A(_l4,[_4d,_mz,function(_mB){return new F(function(){return _kz(_4e,_3C,_3v,_mB,_bX,_mx);});},_])),_mC=function(_mD){var _mE=function(_mF,_){var _mG=B(A(_cQ,[_3C,_4d,_mD,_eg,_]));if(!B(_97(_mG,_ef))){if(!B(_97(_mG,_ee))){return E(_ed);}else{var _mH=rMV(_lr),_mI=[0,new T(function(){var _mJ=E(E(_mH)[1]);return [1,_,[0,[1,_ma,new T(function(){return E(E(_mJ[2])[1]);})]],_mJ[3]];})],_=wMV(_lr,_mI);return new F(function(){return _lq(_lr,_);});}}else{var _mK=rMV(_lr),_mL=[0,new T(function(){var _mM=E(E(_mK)[1]);return [1,_,[0,new T(function(){return B(_cc(_97,_ma,E(_mM[2])[1]));})],_mM[3]];})],_=wMV(_lr,_mL);return new F(function(){return _lq(_lr,_);});}};return new F(function(){return _kz(_4e,_3C,_3v,_mD,_bX,_mE);});},_mN=new T(function(){return toJSStr(B(unAppCStr("state-final-",new T(function(){return B(_b5(0,_m8,_L));}))));}),_mO=B(A(_l4,[_4d,_mN,_mC,_]));_m2=_m7[2];_m3=_m9[2];return null;}}})(_m2,_m3,_));if(_m4!=null){return _m4;}}},_mP=B(_m1(_e4,new T(function(){return E(E(E(E(E(E(E(E(_m0)[1])[3])[3])[3])[3])[2])[1]);},1),_)),_mQ=function(_){var _mR=B(A(_ec,[_])),_mS=E(_mR);if(!_mS[0]){return new F(function(){return die(_dj);});}else{var _mT=E(_cv)(E(_mS[1]),E(_cu)),_mU=rMV(_lr),_mV=[0,new T(function(){var _mW=E(E(_mU)[1]),_mX=new T(function(){var _mY=E(_mW[3]),_mZ=new T(function(){var _n0=E(_mY[3]),_n1=new T(function(){var _n2=E(_n0[3]),_n3=new T(function(){var _n4=E(_n2[3]),_n5=new T(function(){return B(_j(E(_n4[2])[1],[1,new T(function(){var _n6=String(_mT);return fromJSStr(_n6);}),_L]));});return [1,_,[0,_n5],_n4[3]];});return [1,_,_n2[2],_n3];});return [1,_,_n0[2],_n1];});return [1,_,_mY[2],_mZ];});return [1,_,_mW[2],_mX];})],_=wMV(_lr,_mV);return new F(function(){return _lq(_lr,_);});}},_n7=function(_n8,_){return new F(function(){return _mQ(_);});},_n9=B(A(_l4,[_4d,_bZ,function(_na){return new F(function(){return _kz(_4e,_3C,_3v,_na,_bX,_n7);});},_])),_nb=function(_nc,_){var _nd=rMV(_lr),_ne=function(_nf){var _ng=E(_nf);if(!_ng[0]){return E(_lj);}else{var _nh=_ng[1],_ni=new T(function(){return B(_as([1,_nh,_L],[1,new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-alphabet-",[1,_nh,_e6]));}),_L]));});return new F(function(){return _j(B(unAppCStr("<tr>",_ni)),new T(function(){return B(_ne(_ng[2]));},1));});}},_nj=E(_d3)(E(_nc),toJSStr(E(_gR)),toJSStr(B(_ne(E(E(E(E(E(E(_nd)[1])[3])[3])[3])[2])[1]))));return new F(function(){return _3x(_);});},_nk=B(A(_l4,[_4d,_c3,_nb,_])),_nl=rMV(_lr),_nm=function(_nn,_){while(1){var _no=B((function(_np,_){var _nq=E(_np);if(!_nq[0]){return _3w;}else{var _nr=_nq[1],_ns=function(_){var _nt=rMV(_lr),_nu=[0,new T(function(){var _nv=E(E(_nt)[1]),_nw=new T(function(){var _nx=E(_nv[3]),_ny=new T(function(){var _nz=E(_nx[3]),_nA=new T(function(){var _nB=E(_nz[3]);return [1,_,[0,new T(function(){return B(_cc(_4,_nr,E(_nB[2])[1]));})],_nB[3]];});return [1,_,_nz[2],_nA];});return [1,_,_nx[2],_ny];});return [1,_,_nv[2],_nw];})],_=wMV(_lr,_nu),_nC=rMV(_lr),_nD=[0,new T(function(){var _nE=E(E(_nC)[1]),_nF=new T(function(){var _nG=E(_nE[3]),_nH=new T(function(){var _nI=E(_nG[3]),_nJ=new T(function(){return B(_ck(function(_nK){return new F(function(){return _1(_nr,E(_nK)[2]);});},E(_nI[2])[1]));});return [1,_,[0,_nJ],_nI[3]];});return [1,_,_nG[2],_nH];});return [1,_,_nE[2],_nF];})],_=wMV(_lr,_nD);return new F(function(){return _lq(_lr,_);});},_nL=function(_nM,_){return new F(function(){return _ns(_);});},_nN=B(A(_l4,[_4d,new T(function(){return toJSStr(B(unAppCStr("delete-alphabet-",[1,_nr,_L])));}),function(_nO){return new F(function(){return _kz(_4e,_3C,_3v,_nO,_bX,_nL);});},_]));_nn=_nq[2];return null;}})(_nn,_));if(_no!=null){return _no;}}},_nP=B(_nm(E(E(E(E(E(E(_nl)[1])[3])[3])[3])[2])[1],_)),_nQ=function(_){var _nR=B(A(_ea,[_])),_nS=E(_nR);if(!_nS[0]){return new F(function(){return die(_dg);});}else{var _nT=E(_cv)(E(_nS[1]),E(_cu)),_nU=String(_nT),_nV=fromJSStr(_nU);if(!_nV[0]){return new F(function(){return _bc(_);});}else{if(!E(_nV[2])[0]){var _nW=rMV(_lr),_nX=[0,new T(function(){var _nY=E(E(_nW)[1]),_nZ=new T(function(){var _o0=E(_nY[3]),_o1=new T(function(){var _o2=E(_o0[3]),_o3=new T(function(){var _o4=E(_o2[3]);return [1,_,[0,new T(function(){return B(_j(E(_o4[2])[1],[1,_nV[1],_L]));})],_o4[3]];});return [1,_,_o2[2],_o3];});return [1,_,_o0[2],_o1];});return [1,_,_nY[2],_nZ];})],_=wMV(_lr,_nX);return new F(function(){return _lq(_lr,_);});}else{return new F(function(){return _bc(_);});}}}},_o5=function(_o6,_){return new F(function(){return _nQ(_);});},_o7=B(A(_l4,[_4d,_c4,function(_o8){return new F(function(){return _kz(_4e,_3C,_3v,_o8,_bX,_o5);});},_])),_o9=function(_oa,_){var _ob=rMV(_lr),_oc=new T(function(){var _od=new T(function(){var _oe=new T(function(){var _of=new T(function(){var _og=function(_oh){var _oi=E(_oh);if(!_oi[0]){return [0];}else{return new F(function(){return _j(B(unAppCStr("<option>",new T(function(){return B(_j(_oi[1],_dd));}))),new T(function(){return B(_og(_oi[2]));},1));});}};return B(_j(B(_og(E(E(E(E(E(E(E(_ob)[1])[3])[3])[3])[3])[2])[1])),_dc));});return B(unAppCStr("\">",_of));}),_oj=function(_ok){return new F(function(){return unAppCStr("<select class=\"form-control input-sm\" id=\"",new T(function(){return B(_j(_ok,_oe));}));});},_ol=new T(function(){var _om=new T(function(){var _on=function(_oo){var _op=E(_oo);if(!_op[0]){return E(_dc);}else{return new F(function(){return _j(B(unAppCStr("<option>",[1,_op[1],_dd])),new T(function(){return B(_on(_op[2]));},1));});}};return B(_on(E(E(E(E(E(E(_ob)[1])[3])[3])[3])[2])[1]));});return B(unAppCStr("<select class=\"form-control input-sm\" id=\"select-alphabet\">",_om));});return B(_as(new T(function(){return B(_oj(_e8));}),[1,_ol,[1,new T(function(){return B(_oj(_e7));}),_db]]));});return B(_j(B(unAppCStr("<tr>",_od)),_L));}),_oq=function(_or,_os){var _ot=E(_or);if(!_ot[0]){return E(_oc);}else{var _ou=E(_os);if(!_ou[0]){return E(_oc);}else{var _ov=new T(function(){var _ow=E(_ou[1]),_ox=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-transition-",new T(function(){return B(_j(B(_b5(0,_ot[1],_L)),_e6));})));});return B(_as(_ow[1],[1,[1,_ow[2],_L],[1,_ow[3],[1,_ox,_L]]]));});return new F(function(){return _j(B(unAppCStr("<tr>",_ov)),new T(function(){return B(_oq(_ot[2],_ou[2]));},1));});}}},_oy=E(_d3)(E(_oa),toJSStr(E(_gR)),toJSStr(B(_oq(_e4,new T(function(){return E(E(E(E(E(E(_ob)[1])[3])[3])[2])[1]);},1)))));return new F(function(){return _3x(_);});},_oz=B(A(_l4,[_4d,_c5,_o9,_])),_oA=rMV(_lr),_oB=function(_oC,_oD,_){while(1){var _oE=B((function(_oF,_oG,_){var _oH=E(_oF);if(!_oH[0]){return _3w;}else{var _oI=E(_oG);if(!_oI[0]){return _3w;}else{var _oJ=function(_){var _oK=rMV(_lr),_oL=[0,new T(function(){var _oM=E(E(_oK)[1]),_oN=new T(function(){var _oO=E(_oM[3]),_oP=new T(function(){var _oQ=E(_oO[3]);return [1,_,[0,new T(function(){return B(_cc(_d5,_oI[1],E(_oQ[2])[1]));})],_oQ[3]];});return [1,_,_oO[2],_oP];});return [1,_,_oM[2],_oN];})],_=wMV(_lr,_oL);return new F(function(){return _lq(_lr,_);});},_oR=function(_oS,_){return new F(function(){return _oJ(_);});},_oT=new T(function(){return toJSStr(B(unAppCStr("delete-transition-",new T(function(){return B(_b5(0,_oH[1],_L));}))));}),_oU=B(A(_l4,[_4d,_oT,function(_oV){return new F(function(){return _kz(_4e,_3C,_3v,_oV,_bX,_oR);});},_]));_oC=_oH[2];_oD=_oI[2];return null;}}})(_oC,_oD,_));if(_oE!=null){return _oE;}}},_oW=B(_oB(_e4,new T(function(){return E(E(E(E(E(E(_oA)[1])[3])[3])[2])[1]);},1),_)),_oX=function(_){var _oY=B(A(_dO,[_])),_oZ=E(_oY);if(!_oZ[0]){return new F(function(){return die(_kn);});}else{var _p0=E(_cv),_p1=E(_cu),_p2=_p0(E(_oZ[1]),_p1),_p3=B(A(_dM,[_])),_p4=E(_p3);if(!_p4[0]){return new F(function(){return die(_kk);});}else{var _p5=_p0(E(_p4[1]),_p1),_p6=String(_p5),_p7=fromJSStr(_p6);if(!_p7[0]){return new F(function(){return _bg(_);});}else{if(!E(_p7[2])[0]){var _p8=B(A(_dK,[_])),_p9=E(_p8);if(!_p9[0]){return new F(function(){return die(_kh);});}else{var _pa=_p0(E(_p9[1]),_p1),_pb=rMV(_lr),_pc=[0,new T(function(){var _pd=E(E(_pb)[1]),_pe=new T(function(){var _pf=E(_pd[3]),_pg=new T(function(){var _ph=E(_pf[3]),_pi=new T(function(){return B(_hP(_d5,B(_j(E(_ph[2])[1],[1,[0,new T(function(){var _pj=String(_p2);return fromJSStr(_pj);}),_p7[1],new T(function(){var _pk=String(_pa);return fromJSStr(_pk);})],_L]))));});return [1,_,[0,_pi],_ph[3]];});return [1,_,_pf[2],_pg];});return [1,_,_pd[2],_pe];})],_=wMV(_lr,_pc);return new F(function(){return _lq(_lr,_);});}}else{return new F(function(){return _bg(_);});}}}}},_pl=function(_pm,_){return new F(function(){return _oX(_);});},_pn=B(A(_l4,[_4d,_c7,function(_po){return new F(function(){return _kz(_4e,_3C,_3v,_po,_bX,_pl);});},_])),_pp=function(_){var _pq=rMV(_lr),_pr=B(A(_dI,[_])),_ps=E(_pr);if(!_ps[0]){return new F(function(){return _49(_dG,_);});}else{var _pt=E(_d3)(E(_ps[1]),toJSStr(E(_dF)),toJSStr(fromJSStr(B(_bT([4,E(B(_8L(_91,_7C,E(_pq)[1])))])))));return new F(function(){return _3x(_);});}},_pu=function(_pv,_){return new F(function(){return _pp(_);});},_pw=B(A(_l4,[_4d,_c8,function(_px){return new F(function(){return _kz(_4e,_3C,_3v,_px,_bX,_pu);});},_])),_py=function(_){var _pz=B(A(_dE,[_])),_pA=E(_pz);if(!_pA[0]){return new F(function(){return die(_ke);});}else{var _pB=E(_cv)(E(_pA[1]),E(_cu)),_pC=new T(function(){var _pD=String(_pB),_pE=jsParseJSON(toJSStr(fromJSStr(_pD)));if(!_pE[0]){return E(_dC);}else{var _pF=E(_pE[1]);if(_pF[0]==4){var _pG=E(_pF[1]);if(!_pG[0]){return E(_8u);}else{var _pH=B(_7o(_6p,E(_pG[1])[2]));if(!_pH[0]){return E(_dC);}else{var _pI=E(_pG[2]);if(!_pI[0]){return E(_8u);}else{var _pJ=E(E(_pI[1])[2]);if(_pJ[0]==1){var _pK=E(_pI[2]);if(!_pK[0]){return E(_8u);}else{var _pL=B(_5X(_7z,_6p,_7z,E(_pK[1])[2]));if(!_pL[0]){return E(_dC);}else{var _pM=E(_pK[2]);if(!_pM[0]){return E(_8u);}else{var _pN=E(E(_pM[1])[2]);if(_pN[0]==1){var _pO=E(_pM[2]);if(!_pO[0]){return E(_6v);}else{var _pP=B(_7o(_6p,E(_pO[1])[2]));if(!_pP[0]){return E(_dC);}else{if(!E(_pO[2])[0]){return [0,[1,_,[0,_pH[1]],[1,_,[0,new T(function(){return fromJSStr(_pJ[1]);})],[1,_,[0,_pL[1]],[1,_,[0,new T(function(){return fromJSStr(_pN[1]);})],[1,_,[0,_pP[1]],_0]]]]]];}else{return E(_6s);}}}}else{return E(_dC);}}}}}else{return E(_dC);}}}}}else{return E(_8u);}}}),_=wMV(_lr,_pC);return new F(function(){return _lq(_lr,_);});}},_pQ=function(_pR,_){return new F(function(){return _py(_);});},_pS=B(A(_l4,[_4d,_c9,function(_pT){return new F(function(){return _kz(_4e,_3C,_3v,_pT,_bX,_pQ);});},_])),_pU=function(_){var _pV=B(A(_dy,[_])),_pW=E(_pV);if(!_pW[0]){return new F(function(){return die(_ka);});}else{var _pX=E(_cv)(E(_pW[1]),E(_cu)),_pY=rMV(_lr),_pZ=new T(function(){var _q0=String(_pX);if(!B(_9N(_pY,fromJSStr(_q0)))){return E(_d4);}else{return E(_kb);}});return new F(function(){return A(_l4,[_4d,_cb,function(_q1,_){var _q2=E(_d3)(E(_q1),toJSStr(E(_gR)),toJSStr(E(_pZ)));return new F(function(){return _3x(_);});},_]);});}},_q3=function(_q4,_){return new F(function(){return _pU(_);});},_q5=B(A(_l4,[_4d,_ca,function(_q6){return new F(function(){return _kz(_4e,_3C,_3v,_q6,_bX,_q3);});},_])),_q7=function(_q8,_){var _q9=rMV(_lr),_qa=_q9,_qb=new T(function(){return E(E(E(E(E(E(E(_qa)[1])[3])[3])[3])[2])[1]);}),_qc=function(_qd,_qe){var _qf=E(_qd);if(!_qf[0]){return [0];}else{var _qg=function(_qh,_qi){var _qj=E(_qh);if(!_qj[0]){return new F(function(){return _qc(_qf[2],_qi);});}else{var _qk=_qj[1],_ql=E(_qi);if(_ql==1){var _qm=new T(function(){return B(_as(_qk,[1,new T(function(){if(!B(_9N(_qa,_qk))){return E(_d4);}else{return E(_kb);}}),_L]));});return new F(function(){return _j(B(unAppCStr("<tr>",_qm)),_L);});}else{var _qn=new T(function(){return B(_as(_qk,[1,new T(function(){if(!B(_9N(_qa,_qk))){return E(_d4);}else{return E(_kb);}}),_L]));});return new F(function(){return _j(B(unAppCStr("<tr>",_qn)),new T(function(){return B(_qg(_qj[2],_ql-1|0));},1));});}}};return new F(function(){return _qg(B(_aN(_qf[1],_qb)),_qe);});}},_qo=E(_d3)(E(_q8),toJSStr(E(_gR)),toJSStr(B(_qc(_k7,50))));return new F(function(){return _3x(_);});},_qp=B(A(_l4,[_4d,_c0,_q7,_])),_qq=function(_qr,_){while(1){var _qs=B((function(_qt,_){var _qu=E(_qt);if(!_qu[0]){return _3w;}else{var _qv=E(_qu[1]),_qw=function(_){var _qx=new T(function(){var _qy=jsParseJSON(toJSStr(E(E(_qv[2])[3])));if(!_qy[0]){return E(_hj);}else{var _qz=E(_qy[1]);if(_qz[0]==4){var _qA=E(_qz[1]);if(!_qA[0]){return E(_8u);}else{var _qB=B(_7o(_6p,E(_qA[1])[2]));if(!_qB[0]){return E(_hj);}else{var _qC=E(_qA[2]);if(!_qC[0]){return E(_8u);}else{var _qD=E(E(_qC[1])[2]);if(_qD[0]==1){var _qE=E(_qC[2]);if(!_qE[0]){return E(_8u);}else{var _qF=B(_5X(_7z,_6p,_7z,E(_qE[1])[2]));if(!_qF[0]){return E(_hj);}else{var _qG=E(_qE[2]);if(!_qG[0]){return E(_8u);}else{var _qH=E(E(_qG[1])[2]);if(_qH[0]==1){var _qI=E(_qG[2]);if(!_qI[0]){return E(_6v);}else{var _qJ=B(_7o(_6p,E(_qI[1])[2]));if(!_qJ[0]){return E(_hj);}else{if(!E(_qI[2])[0]){return [0,[1,_,[0,_qB[1]],[1,_,[0,new T(function(){return fromJSStr(_qD[1]);})],[1,_,[0,_qF[1]],[1,_,[0,new T(function(){return fromJSStr(_qH[1]);})],[1,_,[0,_qJ[1]],_0]]]]]];}else{return E(_6s);}}}}else{return E(_hj);}}}}}else{return E(_hj);}}}}}else{return E(_8u);}}}),_=wMV(_lr,_qx);return new F(function(){return _lq(_lr,_);});},_qK=function(_qL,_){return new F(function(){return _qw(_);});},_qM=new T(function(){return toJSStr(B(unAppCStr("load-",new T(function(){return B(_b5(0,_qv[1],_L));}))));}),_qN=B(A(_l4,[_4d,_qM,function(_qO){return new F(function(){return _kz(_4e,_3C,_3v,_qO,_bX,_qK);});},_]));_qr=_qu[2];return null;}})(_qr,_));if(_qs!=null){return _qs;}}},_qP=B(A(_l4,[_4d,_c1,function(_qQ,_){var _qR=rMV(_lr),_qS=E(_d3)(E(_qQ),toJSStr(E(_gR)),toJSStr(E(_hi)));return new F(function(){return _qq(_gQ,_);});},_])),_qT=function(_qU,_){while(1){var _qV=B((function(_qW,_){var _qX=E(_qW);if(!_qX[0]){return _3w;}else{var _qY=E(_qX[1]),_qZ=function(_){var _r0=rMV(_lr),_r1=new T(function(){return B(A(E(_qY[2])[2],[_f,_4E,_r0]));}),_r2=new T(function(){return B(_gX(new T(function(){return E(E(E(E(E(_r1)[1])[3])[2])[1]);},1)));}),_=wMV(_lr,[0,[1,_,[0,new T(function(){return B(_6E(_gX,E(E(E(_r1)[1])[2])[1]));})],[1,_,[0,_r2],[1,_,[0,new T(function(){return B(_6E(_h1,E(E(E(E(E(_r1)[1])[3])[3])[2])[1]));})],[1,_,[0,new T(function(){return E(E(E(E(E(E(E(_r1)[1])[3])[3])[3])[2])[1]);})],[1,_,[0,new T(function(){return B(_6E(_gX,E(E(E(E(E(E(E(_r1)[1])[3])[3])[3])[3])[2])[1]));})],_0]]]]]]);return new F(function(){return _lq(_lr,_);});},_r3=function(_r4,_){return new F(function(){return _qZ(_);});},_r5=new T(function(){return toJSStr(B(unAppCStr("convert-",new T(function(){return B(_b5(0,_qY[1],_L));}))));}),_r6=B(A(_l4,[_4d,_r5,function(_r7){return new F(function(){return _kz(_4e,_3C,_3v,_r7,_bX,_r3);});},_]));_qU=_qX[2];return null;}})(_qU,_));if(_qV!=null){return _qV;}}},_r8=B(A(_l4,[_4d,_c2,function(_r9,_){var _ra=rMV(_lr),_rb=E(_d3)(E(_r9),toJSStr(E(_gR)),toJSStr(E(_jU)));return new F(function(){return _qT(_k1,_);});},_]));return _3w;},_rc=function(_rd){return new F(function(){return _dA("Main.hs:342:7-93|Right auto");});},_re=new T(function(){var _rf=jsParseJSON(toJSStr(E(B(_ew(_gE,0))[3])));if(!_rf[0]){return B(_rc(_));}else{var _rg=E(_rf[1]);if(_rg[0]==4){var _rh=E(_rg[1]);if(!_rh[0]){return E(_8u);}else{var _ri=B(_7o(_6p,E(_rh[1])[2]));if(!_ri[0]){return B(_rc(_));}else{var _rj=E(_rh[2]);if(!_rj[0]){return E(_8u);}else{var _rk=E(E(_rj[1])[2]);if(_rk[0]==1){var _rl=E(_rj[2]);if(!_rl[0]){return E(_8u);}else{var _rm=B(_5X(_7z,_6p,_7z,E(_rl[1])[2]));if(!_rm[0]){return B(_rc(_));}else{var _rn=E(_rl[2]);if(!_rn[0]){return E(_8u);}else{var _ro=E(E(_rn[1])[2]);if(_ro[0]==1){var _rp=E(_rn[2]);if(!_rp[0]){return E(_6v);}else{var _rq=B(_7o(_6p,E(_rp[1])[2]));if(!_rq[0]){return B(_rc(_));}else{if(!E(_rp[2])[0]){return [0,[1,_,[0,_ri[1]],[1,_,[0,new T(function(){return fromJSStr(_rk[1]);})],[1,_,[0,_rm[1]],[1,_,[0,new T(function(){return fromJSStr(_ro[1]);})],[1,_,[0,_rq[1]],_0]]]]]];}else{return E(_6s);}}}}else{return B(_rc(_));}}}}}else{return B(_rc(_));}}}}}else{return E(_8u);}}}),_rr=function(_){var _rs=nMV(_re);return new F(function(){return _lq(_rs,_);});},_rt=function(_){return new F(function(){return _rr(_);});};
var hasteMain = function() {B(A(_rt, [0]));};window.onload = hasteMain;