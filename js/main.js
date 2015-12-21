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

var _0=[0,_],_1=function(_2,_3){return E(_2)!=E(_3);},_4=function(_5,_6){return E(_5)==E(_6);},_7=function(_8){return E(E(_8)[1]);},_9=function(_a,_b,_c){while(1){var _d=E(_b);if(!_d[0]){return (E(_c)[0]==0)?true:false;}else{var _e=E(_c);if(!_e[0]){return false;}else{if(!B(A(_7,[_a,_d[1],_e[1]]))){return false;}else{_b=_d[2];_c=_e[2];continue;}}}}},_f=function(_g,_h){while(1){var _i=E(_g);if(!_i[0]){return (E(_h)[0]==0)?true:false;}else{var _j=E(_h);if(!_j[0]){return false;}else{if(E(_i[1])!=E(_j[1])){return false;}else{_g=_i[2];_h=_j[2];continue;}}}}},_k=function(_l,_m){return (!B(_f(_l,_m)))?true:false;},_n=function(_o,_p){while(1){var _q=E(_o);if(!_q[0]){return (E(_p)[0]==0)?true:false;}else{var _r=E(_p);if(!_r[0]){return false;}else{if(!B(_f(_q[1],_r[1]))){return false;}else{_o=_q[2];_p=_r[2];continue;}}}}},_s=[0,_f,_k],_t=function(_u,_v){return (!B(_n(_u,_v)))?true:false;},_w=[0,_n,_t],_x="deltaZ",_y="deltaY",_z="deltaX",_A=function(_B,_C){var _D=E(_B);return (_D[0]==0)?E(_C):[1,_D[1],new T(function(){return B(_A(_D[2],_C));})];},_E=function(_F,_G){var _H=jsShowI(_F);return new F(function(){return _A(fromJSStr(_H),_G);});},_I=41,_J=40,_K=function(_L,_M,_N){if(_M>=0){return new F(function(){return _E(_M,_N);});}else{if(_L<=6){return new F(function(){return _E(_M,_N);});}else{return [1,_J,new T(function(){var _O=jsShowI(_M);return B(_A(fromJSStr(_O),[1,_I,_N]));})];}}},_P=new T(function(){return B(unCStr(")"));}),_Q=new T(function(){return B(_K(0,2,_P));}),_R=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_Q));}),_S=function(_T){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_K(0,_T,_R));}))));});},_U=function(_V,_){return new T(function(){var _W=Number(E(_V)),_X=jsTrunc(_W);if(_X<0){return B(_S(_X));}else{if(_X>2){return B(_S(_X));}else{return _X;}}});},_Y=0,_Z=[0,_Y,_Y,_Y],_10="button",_11=new T(function(){return jsGetMouseCoords;}),_12=[0],_13=function(_14,_){var _15=E(_14);if(!_15[0]){return _12;}else{var _16=B(_13(_15[2],_));return [1,new T(function(){var _17=Number(E(_15[1]));return jsTrunc(_17);}),_16];}},_18=function(_19,_){var _1a=__arr2lst(0,_19);return new F(function(){return _13(_1a,_);});},_1b=function(_1c,_){return new F(function(){return _18(E(_1c),_);});},_1d=function(_1e,_){return new T(function(){var _1f=Number(E(_1e));return jsTrunc(_1f);});},_1g=[0,_1d,_1b],_1h=function(_1i,_){var _1j=E(_1i);if(!_1j[0]){return _12;}else{var _1k=B(_1h(_1j[2],_));return [1,_1j[1],_1k];}},_1l=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1m=new T(function(){return B(unCStr("base"));}),_1n=new T(function(){return B(unCStr("IOException"));}),_1o=new T(function(){var _1p=hs_wordToWord64(4053623282),_1q=hs_wordToWord64(3693590983);return [0,_1p,_1q,[0,_1p,_1q,_1m,_1l,_1n],_12,_12];}),_1r=function(_1s){return E(_1o);},_1t=function(_1u){return E(E(_1u)[1]);},_1v=function(_1w,_1x,_1y){var _1z=B(A(_1w,[_])),_1A=B(A(_1x,[_])),_1B=hs_eqWord64(_1z[1],_1A[1]);if(!_1B){return [0];}else{var _1C=hs_eqWord64(_1z[2],_1A[2]);return (!_1C)?[0]:[1,_1y];}},_1D=function(_1E){var _1F=E(_1E);return new F(function(){return _1v(B(_1t(_1F[1])),_1r,_1F[2]);});},_1G=new T(function(){return B(unCStr(": "));}),_1H=new T(function(){return B(unCStr(")"));}),_1I=new T(function(){return B(unCStr(" ("));}),_1J=new T(function(){return B(unCStr("interrupted"));}),_1K=new T(function(){return B(unCStr("system error"));}),_1L=new T(function(){return B(unCStr("unsatisified constraints"));}),_1M=new T(function(){return B(unCStr("user error"));}),_1N=new T(function(){return B(unCStr("permission denied"));}),_1O=new T(function(){return B(unCStr("illegal operation"));}),_1P=new T(function(){return B(unCStr("end of file"));}),_1Q=new T(function(){return B(unCStr("resource exhausted"));}),_1R=new T(function(){return B(unCStr("resource busy"));}),_1S=new T(function(){return B(unCStr("does not exist"));}),_1T=new T(function(){return B(unCStr("already exists"));}),_1U=new T(function(){return B(unCStr("resource vanished"));}),_1V=new T(function(){return B(unCStr("timeout"));}),_1W=new T(function(){return B(unCStr("unsupported operation"));}),_1X=new T(function(){return B(unCStr("hardware fault"));}),_1Y=new T(function(){return B(unCStr("inappropriate type"));}),_1Z=new T(function(){return B(unCStr("invalid argument"));}),_20=new T(function(){return B(unCStr("failed"));}),_21=new T(function(){return B(unCStr("protocol error"));}),_22=function(_23,_24){switch(E(_23)){case 0:return new F(function(){return _A(_1T,_24);});break;case 1:return new F(function(){return _A(_1S,_24);});break;case 2:return new F(function(){return _A(_1R,_24);});break;case 3:return new F(function(){return _A(_1Q,_24);});break;case 4:return new F(function(){return _A(_1P,_24);});break;case 5:return new F(function(){return _A(_1O,_24);});break;case 6:return new F(function(){return _A(_1N,_24);});break;case 7:return new F(function(){return _A(_1M,_24);});break;case 8:return new F(function(){return _A(_1L,_24);});break;case 9:return new F(function(){return _A(_1K,_24);});break;case 10:return new F(function(){return _A(_21,_24);});break;case 11:return new F(function(){return _A(_20,_24);});break;case 12:return new F(function(){return _A(_1Z,_24);});break;case 13:return new F(function(){return _A(_1Y,_24);});break;case 14:return new F(function(){return _A(_1X,_24);});break;case 15:return new F(function(){return _A(_1W,_24);});break;case 16:return new F(function(){return _A(_1V,_24);});break;case 17:return new F(function(){return _A(_1U,_24);});break;default:return new F(function(){return _A(_1J,_24);});}},_25=new T(function(){return B(unCStr("}"));}),_26=new T(function(){return B(unCStr("{handle: "));}),_27=function(_28,_29,_2a,_2b,_2c,_2d){var _2e=new T(function(){var _2f=new T(function(){var _2g=new T(function(){var _2h=E(_2b);if(!_2h[0]){return E(_2d);}else{var _2i=new T(function(){return B(_A(_2h,new T(function(){return B(_A(_1H,_2d));},1)));},1);return B(_A(_1I,_2i));}},1);return B(_22(_29,_2g));}),_2j=E(_2a);if(!_2j[0]){return E(_2f);}else{return B(_A(_2j,new T(function(){return B(_A(_1G,_2f));},1)));}}),_2k=E(_2c);if(!_2k[0]){var _2l=E(_28);if(!_2l[0]){return E(_2e);}else{var _2m=E(_2l[1]);if(!_2m[0]){var _2n=new T(function(){var _2o=new T(function(){return B(_A(_25,new T(function(){return B(_A(_1G,_2e));},1)));},1);return B(_A(_2m[1],_2o));},1);return new F(function(){return _A(_26,_2n);});}else{var _2p=new T(function(){var _2q=new T(function(){return B(_A(_25,new T(function(){return B(_A(_1G,_2e));},1)));},1);return B(_A(_2m[1],_2q));},1);return new F(function(){return _A(_26,_2p);});}}}else{return new F(function(){return _A(_2k[1],new T(function(){return B(_A(_1G,_2e));},1));});}},_2r=function(_2s){var _2t=E(_2s);return new F(function(){return _27(_2t[1],_2t[2],_2t[3],_2t[4],_2t[6],_12);});},_2u=function(_2v,_2w,_2x){var _2y=E(_2w);return new F(function(){return _27(_2y[1],_2y[2],_2y[3],_2y[4],_2y[6],_2x);});},_2z=function(_2A,_2B){var _2C=E(_2A);return new F(function(){return _27(_2C[1],_2C[2],_2C[3],_2C[4],_2C[6],_2B);});},_2D=44,_2E=93,_2F=91,_2G=function(_2H,_2I,_2J){var _2K=E(_2I);if(!_2K[0]){return new F(function(){return unAppCStr("[]",_2J);});}else{var _2L=new T(function(){var _2M=new T(function(){var _2N=function(_2O){var _2P=E(_2O);if(!_2P[0]){return [1,_2E,_2J];}else{var _2Q=new T(function(){return B(A(_2H,[_2P[1],new T(function(){return B(_2N(_2P[2]));})]));});return [1,_2D,_2Q];}};return B(_2N(_2K[2]));});return B(A(_2H,[_2K[1],_2M]));});return [1,_2F,_2L];}},_2R=function(_2S,_2T){return new F(function(){return _2G(_2z,_2S,_2T);});},_2U=[0,_2u,_2r,_2R],_2V=new T(function(){return [0,_1r,_2U,_2W,_1D,_2r];}),_2W=function(_2X){return [0,_2V,_2X];},_2Y=[0],_2Z=7,_30=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_31=[0,_2Y,_2Z,_12,_30,_2Y,_2Y],_32=new T(function(){return B(_2W(_31));}),_33=function(_){return new F(function(){return die(_32);});},_34=function(_35){return E(E(_35)[1]);},_36=function(_37,_38,_39,_){var _3a=__arr2lst(0,_39),_3b=B(_1h(_3a,_)),_3c=E(_3b);if(!_3c[0]){return new F(function(){return _33(_);});}else{var _3d=E(_3c[2]);if(!_3d[0]){return new F(function(){return _33(_);});}else{if(!E(_3d[2])[0]){var _3e=B(A(_34,[_37,_3c[1],_])),_3f=B(A(_34,[_38,_3d[1],_]));return [0,_3e,_3f];}else{return new F(function(){return _33(_);});}}}},_3g=function(_){return new F(function(){return __jsNull();});},_3h=function(_3i){var _3j=B(A(_3i,[_]));return E(_3j);},_3k=new T(function(){return B(_3h(_3g));}),_3l=new T(function(){return E(_3k);}),_3m=function(_3n,_3o,_){if(E(_3n)==7){var _3p=E(_11)(_3o),_3q=B(_36(_1g,_1g,_3p,_)),_3r=_3o[E(_z)],_3s=_3o[E(_y)],_3t=_3o[E(_x)];return new T(function(){return [0,E(_3q),E(_2Y),[0,_3r,_3s,_3t]];});}else{var _3u=E(_11)(_3o),_3v=B(_36(_1g,_1g,_3u,_)),_3w=_3o[E(_10)],_3x=__eq(_3w,E(_3l));if(!E(_3x)){var _3y=B(_U(_3w,_));return new T(function(){return [0,E(_3v),[1,_3y],E(_Z)];});}else{return new T(function(){return [0,E(_3v),E(_2Y),E(_Z)];});}}},_3z=function(_3A,_3B,_){return new F(function(){return _3m(_3A,E(_3B),_);});},_3C="mouseout",_3D="mouseover",_3E="mousemove",_3F="mouseup",_3G="mousedown",_3H="dblclick",_3I="click",_3J="wheel",_3K=function(_3L){switch(E(_3L)){case 0:return E(_3I);case 1:return E(_3H);case 2:return E(_3G);case 3:return E(_3F);case 4:return E(_3E);case 5:return E(_3D);case 6:return E(_3C);default:return E(_3J);}},_3M=[0,_3K,_3z],_3N=0,_3O=function(_){return _3N;},_3P=function(_3Q,_){return [1,_3Q];},_3R=function(_3S){return E(_3S);},_3T=[0,_3R,_3P],_3U=function(_3V,_3W,_){var _3X=B(A(_3V,[_])),_3Y=B(A(_3W,[_]));return _3X;},_3Z=function(_40,_41,_){var _42=B(A(_40,[_])),_43=B(A(_41,[_]));return new T(function(){return B(A(_42,[_43]));});},_44=function(_45,_46,_){var _47=B(A(_46,[_]));return _45;},_48=function(_49,_4a,_){var _4b=B(A(_4a,[_]));return new T(function(){return B(A(_49,[_4b]));});},_4c=[0,_48,_44],_4d=function(_4e,_){return _4e;},_4f=function(_4g,_4h,_){var _4i=B(A(_4g,[_]));return new F(function(){return A(_4h,[_]);});},_4j=[0,_4c,_4d,_3Z,_4f,_3U],_4k=function(_4l,_4m,_){var _4n=B(A(_4l,[_]));return new F(function(){return A(_4m,[_4n,_]);});},_4o=function(_4p){return [0,_2Y,_2Z,_12,_4p,_2Y,_2Y];},_4q=function(_4r,_){var _4s=new T(function(){return B(_2W(new T(function(){return B(_4o(_4r));})));});return new F(function(){return die(_4s);});},_4t=[0,_4j,_4k,_4f,_4d,_4q],_4u=[0,_4t,_3R],_4v=[0,_4u,_4d],_4w=[1,_12],_4x=new T(function(){return B(unCStr("Tried to deserialie a non-array to a list!"));}),_4y=[0,_4x],_4z=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4A=new T(function(){return B(unCStr("base"));}),_4B=new T(function(){return B(unCStr("PatternMatchFail"));}),_4C=new T(function(){var _4D=hs_wordToWord64(18445595),_4E=hs_wordToWord64(52003073);return [0,_4D,_4E,[0,_4D,_4E,_4A,_4z,_4B],_12,_12];}),_4F=function(_4G){return E(_4C);},_4H=function(_4I){var _4J=E(_4I);return new F(function(){return _1v(B(_1t(_4J[1])),_4F,_4J[2]);});},_4K=function(_4L){return E(E(_4L)[1]);},_4M=function(_4N){return [0,_4O,_4N];},_4P=function(_4Q,_4R){return new F(function(){return _A(E(_4Q)[1],_4R);});},_4S=function(_4T,_4U){return new F(function(){return _2G(_4P,_4T,_4U);});},_4V=function(_4W,_4X,_4Y){return new F(function(){return _A(E(_4X)[1],_4Y);});},_4Z=[0,_4V,_4K,_4S],_4O=new T(function(){return [0,_4F,_4Z,_4M,_4H,_4K];}),_50=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_51=function(_52){return E(E(_52)[3]);},_53=function(_54,_55){return new F(function(){return die(new T(function(){return B(A(_51,[_55,_54]));}));});},_56=function(_57,_58){return new F(function(){return _53(_57,_58);});},_59=function(_5a,_5b){var _5c=E(_5b);if(!_5c[0]){return [0,_12,_12];}else{var _5d=_5c[1];if(!B(A(_5a,[_5d]))){return [0,_12,_5c];}else{var _5e=new T(function(){var _5f=B(_59(_5a,_5c[2]));return [0,_5f[1],_5f[2]];});return [0,[1,_5d,new T(function(){return E(E(_5e)[1]);})],new T(function(){return E(E(_5e)[2]);})];}}},_5g=32,_5h=new T(function(){return B(unCStr("\n"));}),_5i=function(_5j){return (E(_5j)==124)?false:true;},_5k=function(_5l,_5m){var _5n=B(_59(_5i,B(unCStr(_5l)))),_5o=_5n[1],_5p=function(_5q,_5r){var _5s=new T(function(){var _5t=new T(function(){return B(_A(_5m,new T(function(){return B(_A(_5r,_5h));},1)));});return B(unAppCStr(": ",_5t));},1);return new F(function(){return _A(_5q,_5s);});},_5u=E(_5n[2]);if(!_5u[0]){return new F(function(){return _5p(_5o,_12);});}else{if(E(_5u[1])==124){return new F(function(){return _5p(_5o,[1,_5g,_5u[2]]);});}else{return new F(function(){return _5p(_5o,_12);});}}},_5v=function(_5w){return new F(function(){return _56([0,new T(function(){return B(_5k(_5w,_50));})],_4O);});},_5x=function(_5y){return new F(function(){return _5v("Main.hs:46:3-81|function parseJSON");});},_5z=new T(function(){return B(_5x(_));}),_5A=function(_5B){return E(E(_5B)[3]);},_5C=function(_5D,_5E,_5F,_5G){var _5H=E(_5G);if(_5H[0]==3){var _5I=E(_5H[1]);if(!_5I[0]){return E(_5z);}else{var _5J=E(_5I[2]);if(!_5J[0]){return E(_5z);}else{var _5K=E(_5J[2]);if(!_5K[0]){return E(_5z);}else{if(!E(_5K[2])[0]){var _5L=B(A(_5A,[_5D,_5I[1]]));if(!_5L[0]){return [0,_5L[1]];}else{var _5M=B(A(_5A,[_5E,_5J[1]]));if(!_5M[0]){return [0,_5M[1]];}else{var _5N=B(A(_5A,[_5F,_5K[1]]));return (_5N[0]==0)?[0,_5N[1]]:[1,[0,_5L[1],_5M[1],_5N[1]]];}}}else{return E(_5z);}}}}}else{return E(_5z);}},_5O=function(_5P,_5Q,_5R,_5S){var _5T=E(_5S);if(_5T[0]==3){var _5U=function(_5V){var _5W=E(_5V);if(!_5W[0]){return E(_4w);}else{var _5X=B(_5C(_5P,_5Q,_5R,_5W[1]));if(!_5X[0]){return [0,_5X[1]];}else{var _5Y=B(_5U(_5W[2]));return (_5Y[0]==0)?[0,_5Y[1]]:[1,[1,_5X[1],_5Y[1]]];}}};return new F(function(){return _5U(_5T[1]);});}else{return E(_4y);}},_5Z=function(_60){return [1,toJSStr(E(_60))];},_61=new T(function(){return B(unCStr("Tried to deserialize long string to a Char"));}),_62=[0,_61],_63=new T(function(){return B(unCStr("Tried to deserialize a non-string to a Char"));}),_64=[0,_63],_65=function(_66){var _67=E(_66);if(_67[0]==1){var _68=fromJSStr(_67[1]);return (_68[0]==0)?E(_62):(E(_68[2])[0]==0)?[1,_68[1]]:E(_62);}else{return E(_64);}},_69=new T(function(){return B(unCStr("Tried to deserialize a non-JSString to a JSString"));}),_6a=[0,_69],_6b=function(_6c){var _6d=E(_6c);return (_6d[0]==1)?[1,new T(function(){return fromJSStr(_6d[1]);})]:E(_6a);},_6e=function(_6f){return [1,toJSStr([1,_6f,_12])];},_6g=[0,_6e,_5Z,_65,_6b],_6h=function(_6i){return new F(function(){return _5v("Main.hs:64:3-45|function jsonToUnion");});},_6j=new T(function(){return B(_6h(_));}),_6k=function(_6l){return new F(function(){return _5v("Main.hs:(68,3)-(71,33)|function jsonToUnion");});},_6m=new T(function(){return B(_6k(_));}),_6n=function(_6o){return E(E(_6o)[1]);},_6p=function(_6q){return new F(function(){return toJSStr(E(_6q));});},_6r=function(_6s,_6t,_6u){return [4,[1,[0,new T(function(){return B(_6p(_6t));}),new T(function(){return B(A(_6n,[_6s,E(_6u)[1]]));})],_12]];},_6v=function(_6w,_6x){var _6y=E(_6x);return (_6y[0]==0)?[0]:[1,new T(function(){return B(A(_6w,[_6y[1]]));}),new T(function(){return B(_6v(_6w,_6y[2]));})];},_6z=function(_6A,_6B,_6C){return [3,E(B(_6v(function(_6D){return new F(function(){return _6r(_6A,_6B,_6D);});},_6C)))];},_6E=function(_6F){return new F(function(){return _5v("Main.hs:50:3-73|function parseJSON");});},_6G=new T(function(){return B(_6E(_));}),_6H=function(_6I,_6J){var _6K=E(_6J);if(_6K[0]==4){var _6L=E(_6K[1]);if(!_6L[0]){return E(_6G);}else{if(!E(_6L[2])[0]){var _6M=B(A(_5A,[_6I,E(_6L[1])[2]]));return (_6M[0]==0)?[0,_6M[1]]:[1,[0,_6M[1]]];}else{return E(_6G);}}}else{return E(_6G);}},_6N=[1,_12],_6O=[0,_4x],_6P=function(_6Q,_6R){var _6S=E(_6R);if(_6S[0]==3){var _6T=function(_6U){var _6V=E(_6U);if(!_6V[0]){return E(_6N);}else{var _6W=E(_6V[1]);if(_6W[0]==4){var _6X=E(_6W[1]);if(!_6X[0]){return E(_6G);}else{if(!E(_6X[2])[0]){var _6Y=B(A(_5A,[_6Q,E(_6X[1])[2]]));if(!_6Y[0]){return [0,_6Y[1]];}else{var _6Z=B(_6T(_6V[2]));return (_6Z[0]==0)?[0,_6Z[1]]:[1,[1,[0,_6Y[1]],_6Z[1]]];}}else{return E(_6G);}}}else{return E(_6G);}}};return new F(function(){return _6T(_6S[1]);});}else{return E(_6O);}},_70=function(_71,_72){return [0,function(_6D){return new F(function(){return _6r(_71,_72,_6D);});},function(_6D){return new F(function(){return _6z(_71,_72,_6D);});},function(_73){return new F(function(){return _6H(_71,_73);});},function(_74){return new F(function(){return _6P(_71,_74);});}];},_75=new T(function(){return B(unCStr("final"));}),_76=function(_77){return [3,E(B(_6v(_5Z,_77)))];},_78=function(_79){return [3,E(B(_6v(_76,_79)))];},_7a=[1,_12],_7b=new T(function(){return B(unCStr("Tried to deserialie a non-array to a list!"));}),_7c=[0,_7b],_7d=function(_7e){return E(E(_7e)[4]);},_7f=function(_7g,_7h){var _7i=E(_7h);if(_7i[0]==3){var _7j=new T(function(){return B(_7d(_7g));}),_7k=function(_7l){var _7m=E(_7l);if(!_7m[0]){return E(_7a);}else{var _7n=B(A(_7j,[_7m[1]]));if(!_7n[0]){return [0,_7n[1]];}else{var _7o=B(_7k(_7m[2]));return (_7o[0]==0)?[0,_7o[1]]:[1,[1,_7n[1],_7o[1]]];}}};return new F(function(){return _7k(_7i[1]);});}else{return E(_7c);}},_7p=function(_6D){return new F(function(){return _7f(_6g,_6D);});},_7q=[0,_5Z,_76,_6b,_7p],_7r=function(_6D){return new F(function(){return _7f(_7q,_6D);});},_7s=[0,_76,_78,_7p,_7r],_7t=new T(function(){return B(_70(_7s,_75));}),_7u=new T(function(){return B(unCStr("initial"));}),_7v=new T(function(){return B(_70(_7q,_7u));}),_7w=new T(function(){return B(unCStr("transition"));}),_7x=function(_6D){return new F(function(){return _5O(_7q,_6g,_7q,_6D);});},_7y=function(_7z){var _7A=E(_7z);return [3,[1,new T(function(){return B(_5Z(_7A[1]));}),[1,new T(function(){return B(_6e(_7A[2]));}),[1,new T(function(){return B(_5Z(_7A[3]));}),_12]]]];},_7B=function(_7C){return [3,E(B(_6v(_7y,_7C)))];},_7D=function(_7E){return [3,E(B(_6v(_7y,_7E)))];},_7F=function(_7G){return [3,E(B(_6v(_7D,_7G)))];},_7H=function(_7I,_7J,_7K,_7L){var _7M=E(_7L);return [3,[1,new T(function(){return B(A(_6n,[_7I,_7M[1]]));}),[1,new T(function(){return B(A(_6n,[_7J,_7M[2]]));}),[1,new T(function(){return B(A(_6n,[_7K,_7M[3]]));}),_12]]]];},_7N=function(_7O,_7P,_7Q,_7R){return [3,E(B(_6v(function(_6D){return new F(function(){return _7H(_7O,_7P,_7Q,_6D);});},_7R)))];},_7S=function(_7T,_7U,_7V){return [0,function(_6D){return new F(function(){return _7H(_7T,_7U,_7V,_6D);});},function(_6D){return new F(function(){return _7N(_7T,_7U,_7V,_6D);});},function(_6D){return new F(function(){return _5C(_7T,_7U,_7V,_6D);});},function(_6D){return new F(function(){return _5O(_7T,_7U,_7V,_6D);});}];},_7W=new T(function(){return B(_7S(_7q,_6g,_7q));}),_7X=function(_6D){return new F(function(){return _7f(_7W,_6D);});},_7Y=[0,_7B,_7F,_7x,_7X],_7Z=new T(function(){return B(_70(_7Y,_7w));}),_80=new T(function(){return B(unCStr("alphabet"));}),_81=new T(function(){return B(_70(_7q,_80));}),_82=function(_83){var _84=E(_83);if(_84[0]==4){var _85=E(_84[1]);if(!_85[0]){return E(_6m);}else{var _86=B(_7f(_6g,E(_85[1])[2]));return (_86[0]==0)?[0,_86[1]]:(E(_85[2])[0]==0)?[1,[0,[1,_,[0,_86[1]],_0]]]:E(_6j);}}else{return E(_6m);}},_87=new T(function(){return B(unCStr("state"));}),_88=new T(function(){return toJSStr(E(_87));}),_89=function(_8a){var _8b=E(_8a),_8c=E(_8b[3]);return new F(function(){return _A([1,[0,_88,new T(function(){return [3,E(B(_6v(_5Z,E(_8b[2])[1])))];})],_12],_12);});},_8d=function(_8e){return [4,E(B(_89(E(_8e)[1])))];},_8f=[0,_8d,_82],_8g=function(_8h,_8i){return [1,_,_8h,_8i];},_8j=function(_8k){return new F(function(){return _5v("Main.hs:(68,3)-(71,33)|function jsonToUnion");});},_8l=new T(function(){return B(_8j(_));}),_8m=function(_8n){return E(E(_8n)[2]);},_8o=function(_8p,_8q,_8r){var _8s=E(_8r);if(_8s[0]==4){var _8t=E(_8s[1]);if(!_8t[0]){return E(_8l);}else{var _8u=B(A(_5A,[_8q,[4,[1,_8t[1],_12]]]));if(!_8u[0]){return [0,_8u[1]];}else{var _8v=B(A(_8m,[_8p,new T(function(){return [4,E(_8t[2])];})]));return (_8v[0]==0)?[0,_8v[1]]:[1,[0,new T(function(){return B(_8g(_8u[1],E(_8v[1])[1]));})]];}}}else{return E(_8l);}},_8w=new T(function(){return B(unCStr("Monoid JSON: out of domain"));}),_8x=function(_8y){return new F(function(){return err(_8w);});},_8z=new T(function(){return B(_8x(_));}),_8A=function(_8B){return E(E(_8B)[1]);},_8C=function(_8D,_8E,_8F){var _8G=E(_8F),_8H=B(A(_6n,[_8E,_8G[2]]));if(_8H[0]==4){var _8I=B(A(_8A,[_8D,[0,_8G[3]]]));if(_8I[0]==4){return new F(function(){return _A(_8H[1],_8I[1]);});}else{return E(_8z);}}else{return E(_8z);}},_8J=function(_8K,_8L,_8M){return [4,E(B(_8C(_8K,_8L,E(_8M)[1])))];},_8N=function(_8O,_8P){return [0,function(_6D){return new F(function(){return _8J(_8O,_8P,_6D);});},function(_6D){return new F(function(){return _8o(_8O,_8P,_6D);});}];},_8Q=new T(function(){return B(_8N(_8f,_81));}),_8R=new T(function(){return B(_8N(_8Q,_7Z));}),_8S=new T(function(){return B(_8N(_8R,_7v));}),_8T=new T(function(){return B(unCStr(")"));}),_8U=function(_8V,_8W){var _8X=function(_8Y){var _8Z=E(_8W);if(_8Z[0]==2){var _90=new T(function(){return B(_A(B(_91(_8V)),new T(function(){return B(unAppCStr(")",[1,_8Z[1],_12]));},1)));});return new F(function(){return unAppCStr("(",_90);});}else{var _92=function(_93){var _94=E(_8Z);if(_94[0]==3){var _95=new T(function(){var _96=new T(function(){return B(unAppCStr(")",new T(function(){return B(_8U(_94[1],_94[2]));})));},1);return B(_A(B(_91(_8V)),_96));});return new F(function(){return unAppCStr("(",_95);});}else{var _97=E(_8V);if(_97[0]==3){var _98=new T(function(){return B(unAppCStr("(",new T(function(){return B(_A(B(_91(_94)),_8T));})));},1);return new F(function(){return _A(B(_8U(_97[1],_97[2])),_98);});}else{var _99=new T(function(){var _9a=new T(function(){return B(unAppCStr(")(",new T(function(){return B(_A(B(_91(_94)),_8T));})));},1);return B(_A(B(_91(_97)),_9a));});return new F(function(){return unAppCStr("(",_99);});}}},_9b=E(_8V);if(_9b[0]==3){var _9c=E(_8Z);if(_9c[0]==3){return new F(function(){return _A(B(_8U(_9b[1],_9b[2])),new T(function(){return B(_8U(_9c[1],_9c[2]));},1));});}else{return new F(function(){return _92(_);});}}else{return new F(function(){return _92(_);});}}},_9d=E(_8V);switch(_9d[0]){case 2:var _9e=_9d[1],_9f=E(_8W);switch(_9f[0]){case 2:return new F(function(){return _A([1,_9e,_12],[1,_9f[1],_12]);});break;case 3:return new F(function(){return _A([1,_9e,_12],new T(function(){return B(_8U(_9f[1],_9f[2]));},1));});break;default:var _9g=new T(function(){return B(unAppCStr("(",new T(function(){return B(_A(B(_91(_9f)),_8T));})));},1);return new F(function(){return _A([1,_9e,_12],_9g);});}break;case 3:var _9h=E(_8W);if(_9h[0]==2){return new F(function(){return _A(B(_8U(_9d[1],_9d[2])),[1,_9h[1],_12]);});}else{return new F(function(){return _8X(_);});}break;default:return new F(function(){return _8X(_);});}},_9i=new T(function(){return B(unCStr("\u03b5"));}),_9j=new T(function(){return B(unCStr("\u2205"));}),_9k=new T(function(){return B(unCStr("*"));}),_9l=new T(function(){return B(unCStr(")*"));}),_91=function(_9m){var _9n=E(_9m);switch(_9n[0]){case 0:return E(_9j);case 1:return E(_9i);case 2:return [1,_9n[1],_12];case 3:var _9o=_9n[1],_9p=_9n[2],_9q=function(_9r){var _9s=E(_9p);if(_9s[0]==2){var _9t=new T(function(){return B(_A(B(_91(_9o)),new T(function(){return B(unAppCStr(")",[1,_9s[1],_12]));},1)));});return new F(function(){return unAppCStr("(",_9t);});}else{var _9u=function(_9v){var _9w=E(_9s);if(_9w[0]==3){var _9x=new T(function(){var _9y=new T(function(){return B(unAppCStr(")",new T(function(){return B(_8U(_9w[1],_9w[2]));})));},1);return B(_A(B(_91(_9o)),_9y));});return new F(function(){return unAppCStr("(",_9x);});}else{var _9z=E(_9o);if(_9z[0]==3){var _9A=new T(function(){return B(unAppCStr("(",new T(function(){return B(_A(B(_91(_9w)),_8T));})));},1);return new F(function(){return _A(B(_8U(_9z[1],_9z[2])),_9A);});}else{var _9B=new T(function(){var _9C=new T(function(){return B(unAppCStr(")(",new T(function(){return B(_A(B(_91(_9w)),_8T));})));},1);return B(_A(B(_91(_9z)),_9C));});return new F(function(){return unAppCStr("(",_9B);});}}},_9D=E(_9o);if(_9D[0]==3){var _9E=E(_9s);if(_9E[0]==3){return new F(function(){return _A(B(_8U(_9D[1],_9D[2])),new T(function(){return B(_8U(_9E[1],_9E[2]));},1));});}else{return new F(function(){return _9u(_);});}}else{return new F(function(){return _9u(_);});}}},_9F=E(_9o);switch(_9F[0]){case 2:var _9G=_9F[1],_9H=E(_9p);switch(_9H[0]){case 2:return new F(function(){return _A([1,_9G,_12],[1,_9H[1],_12]);});break;case 3:return new F(function(){return _A([1,_9G,_12],new T(function(){return B(_8U(_9H[1],_9H[2]));},1));});break;default:var _9I=new T(function(){return B(unAppCStr("(",new T(function(){return B(_A(B(_91(_9H)),_8T));})));},1);return new F(function(){return _A([1,_9G,_12],_9I);});}break;case 3:var _9J=E(_9p);if(_9J[0]==2){return new F(function(){return _A(B(_8U(_9F[1],_9F[2])),[1,_9J[1],_12]);});}else{return new F(function(){return _9q(_);});}break;default:return new F(function(){return _9q(_);});}break;case 4:var _9K=new T(function(){return B(unAppCStr("+",new T(function(){return B(_91(_9n[2]));})));},1);return new F(function(){return _A(B(_91(_9n[1])),_9K);});break;default:var _9L=E(_9n[1]);if(_9L[0]==2){return new F(function(){return _A([1,_9L[1],_12],_9k);});}else{return new F(function(){return unAppCStr("(",new T(function(){return B(_A(B(_91(_9L)),_9l));}));});}}},_9M=function(_9N,_9O){while(1){var _9P=E(_9N);if(!_9P[0]){return (E(_9O)[0]==0)?true:false;}else{var _9Q=E(_9O);if(!_9Q[0]){return false;}else{if(E(_9P[1])!=E(_9Q[1])){return false;}else{_9N=_9P[2];_9O=_9Q[2];continue;}}}}},_9R=function(_9S,_9T,_9U,_9V,_9W,_9X){return (!B(_9M(_9S,_9V)))?true:(E(_9T)!=E(_9W))?true:(!B(_9M(_9U,_9X)))?true:false;},_9Y=function(_9Z,_a0){var _a1=E(_9Z),_a2=E(_a0);return new F(function(){return _9R(_a1[1],_a1[2],_a1[3],_a2[1],_a2[2],_a2[3]);});},_a3=function(_a4,_a5,_a6,_a7,_a8,_a9){if(!B(_9M(_a4,_a7))){return false;}else{if(E(_a5)!=E(_a8)){return false;}else{return new F(function(){return _9M(_a6,_a9);});}}},_aa=function(_ab,_ac){var _ad=E(_ab),_ae=E(_ac);return new F(function(){return _a3(_ad[1],_ad[2],_ad[3],_ae[1],_ae[2],_ae[3]);});},_af=[0,_aa,_9Y],_ag=function(_ah,_ai){while(1){var _aj=E(_ah);switch(_aj[0]){case 0:return (E(_ai)[0]==0)?true:false;case 1:return (E(_ai)[0]==1)?true:false;case 2:var _ak=E(_ai);if(_ak[0]==2){return new F(function(){return _4(_aj[1],_ak[1]);});}else{return false;}break;case 3:var _al=E(_ai);if(_al[0]==3){if(!B(_ag(_aj[1],_al[1]))){return false;}else{_ah=_aj[2];_ai=_al[2];continue;}}else{return false;}break;case 4:var _am=E(_ai);if(_am[0]==4){if(!B(_ag(_aj[1],_am[1]))){return false;}else{_ah=_aj[2];_ai=_am[2];continue;}}else{return false;}break;default:var _an=E(_ai);if(_an[0]==5){_ah=_aj[1];_ai=_an[1];continue;}else{return false;}}}},_ao=function(_ap,_aq,_ar,_as){if(!B(_ag(_ap,_ar))){return false;}else{return new F(function(){return _ag(_aq,_as);});}},_at=function(_au,_av,_aw,_ax){if(!B(_ag(_au,_aw))){return false;}else{return new F(function(){return _ag(_av,_ax);});}},_ay=function(_az,_aA){while(1){var _aB=B((function(_aC,_aD){var _aE=E(_aC);if(!_aE[0]){return [0];}else{var _aF=E(_aD);if(!_aF[0]){return [0];}else{var _aG=new T(function(){return B(_aH(_aE));}),_aI=new T(function(){return B(_aH(_aF));});if(!B(_at(_aG,_aI,_aE,_aF))){_az=_aG;_aA=_aI;return null;}else{return [4,_aG,_aI];}}}})(_az,_aA));if(_aB!=null){return _aB;}}},_aH=function(_aJ){var _aK=E(_aJ);switch(_aK[0]){case 3:var _aL=E(_aK[1]);if(!_aL[0]){return [0];}else{var _aM=E(_aK[2]);switch(_aM[0]){case 0:return [0];case 1:return E(_aL);default:var _aN=E(_aL);if(_aN[0]==1){return E(_aM);}else{var _aO=new T(function(){return B(_aH(_aN));}),_aP=new T(function(){return B(_aH(_aM));});if(!B(_ao(_aO,_aP,_aN,_aM))){return new F(function(){return _aQ(_aO,_aP);});}else{return [3,_aO,_aP];}}}}break;case 4:var _aR=E(_aK[1]);if(!_aR[0]){return [0];}else{var _aS=E(_aK[2]);if(!_aS[0]){return [0];}else{var _aT=new T(function(){return B(_aH(_aR));}),_aU=new T(function(){return B(_aH(_aS));});if(!B(_at(_aT,_aU,_aR,_aS))){return new F(function(){return _ay(_aT,_aU);});}else{return [4,_aT,_aU];}}}break;case 5:return (E(_aK[1])[0]==0)?[1]:E(_aK);default:return E(_aK);}},_aQ=function(_aV,_aW){while(1){var _aX=B((function(_aY,_aZ){var _b0=E(_aY);if(!_b0[0]){return [0];}else{var _b1=E(_aZ);switch(_b1[0]){case 0:return [0];case 1:return E(_b0);default:var _b2=E(_b0);if(_b2[0]==1){return E(_b1);}else{var _b3=new T(function(){return B(_aH(_b2));}),_b4=new T(function(){return B(_aH(_b1));});if(!B(_ao(_b3,_b4,_b2,_b1))){_aV=_b3;_aW=_b4;return null;}else{return [3,_b3,_b4];}}}}})(_aV,_aW));if(_aX!=null){return _aX;}}},_b5=function(_b6,_b7,_b8,_b9){while(1){var _ba=E(_b6);if(!_ba[0]){return [0,_b7,_b8,_b9];}else{var _bb=[4,_b8,E(_ba[1])[2]];_b6=_ba[2];_b8=_bb;continue;}}},_bc=function(_bd,_be){while(1){var _bf=E(_bd);if(!_bf[0]){return E(_be);}else{var _bg=_be+1|0;_bd=_bf[2];_be=_bg;continue;}}},_bh=function(_bi,_bj){while(1){var _bk=B((function(_bl,_bm){var _bn=E(_bm);if(!_bn[0]){return [0];}else{var _bo=_bn[1],_bp=_bn[2];if(!B(A(_bl,[_bo]))){var _bq=_bl;_bi=_bq;_bj=_bp;return null;}else{return [1,_bo,new T(function(){return B(_bh(_bl,_bp));})];}}})(_bi,_bj));if(_bk!=null){return _bk;}}},_br=new T(function(){return B(unCStr(": empty list"));}),_bs=new T(function(){return B(unCStr("Prelude."));}),_bt=function(_bu){return new F(function(){return err(B(_A(_bs,new T(function(){return B(_A(_bu,_br));},1))));});},_bv=new T(function(){return B(unCStr("foldl1"));}),_bw=new T(function(){return B(_bt(_bv));}),_bx=function(_by,_bz){while(1){var _bA=B((function(_bB,_bC){var _bD=E(_bB);if(!_bD[0]){return _bC;}else{var _bE=_bD[1],_bF=new T(function(){var _bG=E(_bC),_bH=new T(function(){var _bI=E(_bG[3]),_bJ=new T(function(){var _bK=E(_bI[3]),_bL=_bK[3],_bM=new T(function(){var _bN=E(_bK[2])[1],_bO=new T(function(){var _bP=function(_bQ,_bR){return new F(function(){return _bh(function(_bS){var _bT=E(_bS);if(!B(_9M(_bT[1],_bQ))){return false;}else{return new F(function(){return _9M(_bT[3],_bR);});}},_bN);});},_bU=function(_bV){var _bW=E(_bV);if(!_bW[0]){return [0];}else{var _bX=_bW[1],_bY=_bW[2];if(B(_bc(B(_bP(_bE,_bX)),0))>1){return new F(function(){return _A([1,new T(function(){var _bZ=B(_bP(_bE,_bX));if(!_bZ[0]){return E(_bw);}else{var _c0=E(_bZ[1]),_c1=B(_b5(_bZ[2],_c0[1],_c0[2],_c0[3]));return [0,_c1[1],_c1[2],_c1[3]];}}),_12],new T(function(){return B(_bU(_bY));},1));});}else{return new F(function(){return _A(B(_bP(_bE,_bX)),new T(function(){return B(_bU(_bY));},1));});}}};return B(_bU(E(E(E(_bL)[3])[2])[1]));}),_c2=function(_c3){while(1){var _c4=B((function(_c5){var _c6=E(_c5);if(!_c6[0]){return E(_bO);}else{var _c7=_c6[2],_c8=E(_c6[1]);if(!B(_f(_c8[1],_bE))){return [1,_c8,new T(function(){return B(_c2(_c7));})];}else{_c3=_c7;return null;}}})(_c3));if(_c4!=null){return _c4;}}};return B(_c2(_bN));});return [1,_,[0,_bM],_bL];});return [1,_,_bI[2],_bJ];});return [1,_,_bG[2],_bH];});_by=_bD[2];_bz=_bF;return null;}})(_by,_bz));if(_bA!=null){return _bA;}}},_c9=function(_ca,_cb,_cc,_cd,_ce){var _cf=E(_ca);if(!_cf[0]){return [1,_,_cc,_cd];}else{var _cg=_cf[1],_ch=new T(function(){var _ci=E(_cd),_cj=new T(function(){var _ck=E(_ci[3]),_cl=_ck[3],_cm=new T(function(){var _cn=E(_ck[2])[1],_co=new T(function(){var _cp=function(_cq,_cr){return new F(function(){return _bh(function(_cs){var _ct=E(_cs);if(!B(_9M(_ct[1],_cq))){return false;}else{return new F(function(){return _9M(_ct[3],_cr);});}},_cn);});},_cu=function(_cv){var _cw=E(_cv);if(!_cw[0]){return [0];}else{var _cx=_cw[1],_cy=_cw[2];if(B(_bc(B(_cp(_cg,_cx)),0))>1){return new F(function(){return _A([1,new T(function(){var _cz=B(_cp(_cg,_cx));if(!_cz[0]){return E(_bw);}else{var _cA=E(_cz[1]),_cB=B(_b5(_cz[2],_cA[1],_cA[2],_cA[3]));return [0,_cB[1],_cB[2],_cB[3]];}}),_12],new T(function(){return B(_cu(_cy));},1));});}else{return new F(function(){return _A(B(_cp(_cg,_cx)),new T(function(){return B(_cu(_cy));},1));});}}};return B(_cu(E(E(E(_cl)[3])[2])[1]));}),_cC=function(_cD){while(1){var _cE=B((function(_cF){var _cG=E(_cF);if(!_cG[0]){return E(_co);}else{var _cH=_cG[2],_cI=E(_cG[1]);if(!B(_f(_cI[1],_cg))){return [1,_cI,new T(function(){return B(_cC(_cH));})];}else{_cD=_cH;return null;}}})(_cD));if(_cE!=null){return _cE;}}};return B(_cC(_cn));});return [1,_,[0,_cm],_cl];});return [1,_,_ci[2],_cj];});return new F(function(){return _bx(_cf[2],[1,_,_cc,_ch]);});}},_cJ=function(_cK,_cL){while(1){var _cM=E(_cL);if(!_cM[0]){return false;}else{if(!B(A(_cK,[_cM[1]]))){_cL=_cM[2];continue;}else{return true;}}}},_cN=function(_cO,_cP,_cQ){while(1){var _cR=E(_cQ);if(!_cR[0]){return false;}else{if(!B(A(_7,[_cO,_cP,_cR[1]]))){_cQ=_cR[2];continue;}else{return true;}}}},_cS=new T(function(){return B(_n(_12,_12));}),_cT=function(_cU,_cV){var _cW=new T(function(){return E(E(E(E(E(E(_cU)[1])[3])[3])[2])[1]);}),_cX=new T(function(){return E(E(E(E(E(E(E(E(_cU)[1])[3])[3])[3])[3])[2])[1]);}),_cY=function(_cZ,_d0){while(1){var _d1=B((function(_d2,_d3){var _d4=E(_d3);if(!_d4[0]){return E(_d2);}else{var _d5=new T(function(){var _d6=function(_d7){var _d8=E(_d7);if(!_d8[0]){return [0];}else{var _d9=_d8[1],_da=new T(function(){return B(_d6(_d8[2]));}),_db=function(_dc){while(1){var _dd=B((function(_de){var _df=E(_de);if(!_df[0]){return E(_da);}else{var _dg=_df[2];if(!B(_cN(_af,[0,_df[1],_d4[1],_d9],_cW))){_dc=_dg;return null;}else{return [1,_d9,new T(function(){return B(_db(_dg));})];}}})(_dc));if(_dd!=null){return _dd;}}};return new F(function(){return _db(_d2);});}};return B(_d6(_cX));});_cZ=_d5;_d0=_d4[2];return null;}})(_cZ,_d0));if(_d1!=null){return _d1;}}},_dh=B(_cY([1,new T(function(){return E(E(E(E(E(_cU)[1])[3])[2])[1]);}),_12],_cV));if(!_dh[0]){return (!E(_cS))?true:false;}else{var _di=E(E(E(E(_cU)[1])[2])[1]);if(!_di[0]){return (!E(_cS))?true:false;}else{var _dj=function(_dk){while(1){var _dl=B((function(_dm){var _dn=E(_dm);if(!_dn[0]){return [0];}else{var _do=_dn[1],_dp=_dn[2];if(!B(_cJ(function(_6D){return new F(function(){return _9M(_do,_6D);});},_di))){_dk=_dp;return null;}else{return [1,_do,new T(function(){return B(_dj(_dp));})];}}})(_dk));if(_dl!=null){return _dl;}}},_dq=function(_dr,_ds){if(!B(_cJ(function(_6D){return new F(function(){return _9M(_dr,_6D);});},_di))){return new F(function(){return _dj(_ds);});}else{return [1,_dr,new T(function(){return B(_dj(_ds));})];}};return (!B(_n(B(_dq(_dh[1],_dh[2])),_12)))?true:false;}}},_dt=function(_du,_dv,_dw){while(1){var _dx=E(_dw);if(!_dx[0]){return false;}else{if(!B(A(_du,[_dx[1],_dv]))){_dw=_dx[2];continue;}else{return true;}}}},_dy=function(_dz,_dA){var _dB=function(_dC,_dD){while(1){var _dE=B((function(_dF,_dG){var _dH=E(_dF);if(!_dH[0]){return [0];}else{var _dI=_dH[1],_dJ=_dH[2];if(!B(_dt(_dz,_dI,_dG))){return [1,_dI,new T(function(){return B(_dB(_dJ,[1,_dI,_dG]));})];}else{var _dK=_dG;_dC=_dJ;_dD=_dK;return null;}}})(_dC,_dD));if(_dE!=null){return _dE;}}};return new F(function(){return _dB(_dA,_12);});},_dL=function(_dM,_dN,_dO){var _dP=function(_dQ){while(1){var _dR=B((function(_dS){var _dT=E(_dS);if(!_dT[0]){return [0];}else{var _dU=_dT[2],_dV=E(_dT[1]);if(!B(_cN(_s,_dV[1],_dN))){_dQ=_dU;return null;}else{var _dW=E(_dO);if(_dW!=E(_dV[2])){var _dX=function(_dY){while(1){var _dZ=B((function(_e0){var _e1=E(_e0);if(!_e1[0]){return [0];}else{var _e2=_e1[2],_e3=E(_e1[1]);if(!B(_cN(_s,_e3[1],_dN))){_dY=_e2;return null;}else{if(_dW!=E(_e3[2])){_dY=_e2;return null;}else{return [1,_e3[3],new T(function(){return B(_dX(_e2));})];}}}})(_dY));if(_dZ!=null){return _dZ;}}};return new F(function(){return _dX(_dU);});}else{var _e4=new T(function(){var _e5=function(_e6){while(1){var _e7=B((function(_e8){var _e9=E(_e8);if(!_e9[0]){return [0];}else{var _ea=_e9[2],_eb=E(_e9[1]);if(!B(_cN(_s,_eb[1],_dN))){_e6=_ea;return null;}else{if(_dW!=E(_eb[2])){_e6=_ea;return null;}else{return [1,_eb[3],new T(function(){return B(_e5(_ea));})];}}}})(_e6));if(_e7!=null){return _e7;}}};return B(_e5(_dU));});return [1,_dV[3],_e4];}}}})(_dQ));if(_dR!=null){return _dR;}}};return new F(function(){return _dy(_9M,B(_dP(E(E(E(E(_dM)[3])[3])[2])[1])));});},_ec=function(_ed,_ee,_ef){return new F(function(){return _dL(E(_ed)[1],_ee,_ef);});},_eg=new T(function(){return B(unCStr("</td>"));}),_eh=new T(function(){return B(unCStr("</tr>"));}),_ei=function(_ej){var _ek=E(_ej);if(!_ek[0]){return E(_eh);}else{return new F(function(){return _A(B(unAppCStr("<td>",new T(function(){return B(_A(_ek[1],_eg));}))),new T(function(){return B(_ei(_ek[2]));},1));});}},_el=function(_em,_en){return new F(function(){return _A(B(unAppCStr("<td>",new T(function(){return B(_A(_em,_eg));}))),new T(function(){return B(_ei(_en));},1));});},_eo=[1,_12,_12],_ep=function(_eq){var _er=E(_eq);if(!_er[0]){return E(_eo);}else{var _es=new T(function(){return B(_ep(_er[2]));}),_et=function(_eu){var _ev=E(_eu);if(!_ev[0]){return [0];}else{var _ew=new T(function(){return B(_et(_ev[2]));}),_ex=function(_ey){var _ez=E(_ey);return (_ez[0]==0)?E(_ew):[1,[1,_ev[1],_ez[1]],new T(function(){return B(_ex(_ez[2]));})];};return new F(function(){return _ex(_es);});}};return new F(function(){return _et(_er[1]);});}},_eA=function(_eB,_eC){if(0>=_eB){return E(_eo);}else{var _eD=function(_eE){var _eF=E(_eE);return (_eF==1)?[1,_eC,_12]:[1,_eC,new T(function(){return B(_eD(_eF-1|0));})];};return new F(function(){return _ep(B(_eD(_eB)));});}},_eG=function(_eH,_eI){return new F(function(){return _eA(E(_eH),_eI);});},_eJ=function(_eK){while(1){var _eL=E(_eK);if(!_eL[0]){_eK=[1,I_fromInt(_eL[1])];continue;}else{return new F(function(){return I_toString(_eL[1]);});}}},_eM=function(_eN,_eO){return new F(function(){return _A(fromJSStr(B(_eJ(_eN))),_eO);});},_eP=function(_eQ,_eR){var _eS=E(_eQ);if(!_eS[0]){var _eT=_eS[1],_eU=E(_eR);return (_eU[0]==0)?_eT<_eU[1]:I_compareInt(_eU[1],_eT)>0;}else{var _eV=_eS[1],_eW=E(_eR);return (_eW[0]==0)?I_compareInt(_eV,_eW[1])<0:I_compare(_eV,_eW[1])<0;}},_eX=[0,0],_eY=function(_eZ,_f0,_f1){if(_eZ<=6){return new F(function(){return _eM(_f0,_f1);});}else{if(!B(_eP(_f0,_eX))){return new F(function(){return _eM(_f0,_f1);});}else{return [1,_J,new T(function(){return B(_A(fromJSStr(B(_eJ(_f0))),[1,_I,_f1]));})];}}},_f2=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:360:7-14"));}),_f3=[0,_2Y,_2Z,_12,_f2,_2Y,_2Y],_f4=new T(function(){return B(_2W(_f3));}),_f5=function(_){return new F(function(){return die(_f4);});},_f6=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:381:7-14"));}),_f7=[0,_2Y,_2Z,_12,_f6,_2Y,_2Y],_f8=new T(function(){return B(_2W(_f7));}),_f9=function(_){return new F(function(){return die(_f8);});},_fa=",",_fb="[",_fc="]",_fd="{",_fe="}",_ff=":",_fg="\"",_fh="true",_fi="false",_fj="null",_fk=new T(function(){return JSON.stringify;}),_fl=function(_fm,_fn){var _fo=E(_fn);switch(_fo[0]){case 0:return [0,new T(function(){return jsShow(_fo[1]);}),_fm];case 1:return [0,new T(function(){var _fp=E(_fk)(_fo[1]);return String(_fp);}),_fm];case 2:return (!E(_fo[1]))?[0,_fi,_fm]:[0,_fh,_fm];case 3:var _fq=E(_fo[1]);if(!_fq[0]){return [0,_fb,[1,_fc,_fm]];}else{var _fr=new T(function(){var _fs=new T(function(){var _ft=function(_fu){var _fv=E(_fu);if(!_fv[0]){return [1,_fc,_fm];}else{var _fw=new T(function(){var _fx=B(_fl(new T(function(){return B(_ft(_fv[2]));}),_fv[1]));return [1,_fx[1],_fx[2]];});return [1,_fa,_fw];}};return B(_ft(_fq[2]));}),_fy=B(_fl(_fs,_fq[1]));return [1,_fy[1],_fy[2]];});return [0,_fb,_fr];}break;case 4:var _fz=E(_fo[1]);if(!_fz[0]){return [0,_fd,[1,_fe,_fm]];}else{var _fA=E(_fz[1]),_fB=new T(function(){var _fC=new T(function(){var _fD=function(_fE){var _fF=E(_fE);if(!_fF[0]){return [1,_fe,_fm];}else{var _fG=E(_fF[1]),_fH=new T(function(){var _fI=B(_fl(new T(function(){return B(_fD(_fF[2]));}),_fG[2]));return [1,_fI[1],_fI[2]];});return [1,_fa,[1,_fg,[1,_fG[1],[1,_fg,[1,_ff,_fH]]]]];}};return B(_fD(_fz[2]));}),_fJ=B(_fl(_fC,_fA[2]));return [1,_fJ[1],_fJ[2]];});return [0,_fd,[1,new T(function(){var _fK=E(_fk)(E(_fA[1]));return String(_fK);}),[1,_ff,_fB]]];}break;default:return [0,_fj,_fm];}},_fL=new T(function(){return toJSStr(_12);}),_fM=function(_fN){var _fO=B(_fl(_12,_fN)),_fP=jsCat([1,_fO[1],_fO[2]],E(_fL));return E(_fP);},_fQ=0,_fR=[1],_fS=function(_fT,_fU,_fV){var _fW=E(_fV);if(!_fW[0]){return [0];}else{var _fX=_fW[1],_fY=_fW[2];return (!B(A(_fT,[_fU,_fX])))?[1,_fX,new T(function(){return B(_fS(_fT,_fU,_fY));})]:E(_fY);}},_fZ=function(_g0,_g1,_g2){return new F(function(){return _fS(new T(function(){return B(_7(_g0));}),_g1,_g2);});},_g3=function(_g4,_g5,_g6){var _g7=_g6,_g8=_g5;while(1){var _g9=E(_g7);if(!_g9[0]){return E(_g8);}else{var _ga=B(_fZ(_g4,_g9[1],_g8));_g7=_g9[2];_g8=_ga;continue;}}},_gb="initial-state-select",_gc="change-initial",_gd="accept-check-button",_ge="accept-check-result",_gf="word-table-tbody",_gg="example-table-tbody",_gh="conversion-table-tbody",_gi="convert-1",_gj="convert-2",_gk="alert-area",_gl=new T(function(){return B(unCStr("__qf"));}),_gm=[1,_gl,_12],_gn=[0,_gm],_go="state-table-tbody",_gp="add-state",_gq="alphabet-table-tbody",_gr="add-alphabet",_gs=new T(function(){return B(unCStr("] },  layout: {    name: \'cose\',    directed: true,    roots: \'#a\'  }  });   "));}),_gt="transition-table-tbody",_gu="add-transition",_gv="export-button",_gw="import-button",_gx=(function(s){var x = eval(s);return (typeof x === 'undefined') ? 'undefined' : x.toString();}),_gy=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_gz=function(_gA){return new F(function(){return _56([0,new T(function(){return B(_5k(_gA,_gy));})],_4O);});},_gB=function(_gC){return new F(function(){return _gz("Main.hs:149:25-76|[(_, b, _)]");});},_gD="value",_gE=(function(e,p){return e[p].toString();}),_gF=function(_gG){return E(E(_gG)[1]);},_gH=function(_gI){return E(E(_gI)[2]);},_gJ=function(_gK){return new F(function(){return fromJSStr(E(_gK));});},_gL=function(_gM){return E(E(_gM)[1]);},_gN=function(_gO){return E(E(_gO)[2]);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){var _gV=function(_){var _gW=E(_gE)(B(A(_gL,[_gQ,_gS])),E(_gT));return new T(function(){return String(_gW);});};return E(_gV);});return new F(function(){return A(_gN,[_gR,_gU]);});},_gX=function(_gY){return E(E(_gY)[4]);},_gZ=function(_h0,_h1,_h2,_h3){var _h4=B(_gF(_h1)),_h5=new T(function(){return B(_gX(_h4));}),_h6=function(_h7){return new F(function(){return A(_h5,[new T(function(){return B(_gJ(_h7));})]);});},_h8=new T(function(){return B(_gP(_h0,_h1,_h2,new T(function(){return toJSStr(E(_h3));},1)));});return new F(function(){return A(_gH,[_h4,_h8,_h6]);});},_h9=function(_ha){var _hb=E(_ha);if(!_hb[0]){return [0];}else{return new F(function(){return _A(_hb[1],new T(function(){return B(_h9(_hb[2]));},1));});}},_hc=function(_hd,_he,_hf){var _hg=E(_he);if(!_hg[0]){return [0];}else{var _hh=E(_hf);if(!_hh[0]){return [0];}else{var _hi=function(_hj){while(1){var _hk=B((function(_hl){var _hm=E(_hl);if(!_hm[0]){return [0];}else{var _hn=_hm[1],_ho=_hm[2];if(!B(_cJ(new T(function(){return B(A(_hd,[_hn]));}),_hh))){_hj=_ho;return null;}else{return [1,_hn,new T(function(){return B(_hi(_ho));})];}}})(_hj));if(_hk!=null){return _hk;}}};return new F(function(){return _hi(_hg);});}}},_hp=(function(e,p,v){e[p] = v;}),_hq=new T(function(){return B(unCStr("</div>"));}),_hr=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:404:7-12"));}),_hs=[0,_2Y,_2Z,_12,_hr,_2Y,_2Y],_ht=new T(function(){return B(_2W(_hs));}),_hu=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:396:7-12"));}),_hv=[0,_2Y,_2Z,_12,_hu,_2Y,_2Y],_hw=new T(function(){return B(_2W(_hv));}),_hx=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:383:7-15"));}),_hy=[0,_2Y,_2Z,_12,_hx,_2Y,_2Y],_hz=new T(function(){return B(_2W(_hy));}),_hA=function(_hB){var _hC=E(_hB);return [0,_hC[1],[2,_hC[2]],_hC[3]];},_hD=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:380:7-15"));}),_hE=[0,_2Y,_2Z,_12,_hD,_2Y,_2Y],_hF=new T(function(){return B(_2W(_hE));}),_hG=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:377:7-15"));}),_hH=[0,_2Y,_2Z,_12,_hG,_2Y,_2Y],_hI=new T(function(){return B(_2W(_hH));}),_hJ=function(_hK,_hL){var _hM=E(_hK),_hN=E(_hL);if(!B(_9M(_hM[1],_hN[1]))){return false;}else{if(E(_hM[2])!=E(_hN[2])){return false;}else{return new F(function(){return _9M(_hM[3],_hN[3]);});}}},_hO=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-transition\">\u8ffd\u52a0</button>"));}),_hP=[1,_hO,_12],_hQ=new T(function(){return B(unCStr("</select>"));}),_hR=new T(function(){return B(unCStr("</option>"));}),_hS=new T(function(){return B(unCStr("innerHTML"));}),_hT=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:359:7-15"));}),_hU=[0,_2Y,_2Z,_12,_hT,_2Y,_2Y],_hV=new T(function(){return B(_2W(_hU));}),_hW=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:340:7-15"));}),_hX=[0,_2Y,_2Z,_12,_hW,_2Y,_2Y],_hY=new T(function(){return B(_2W(_hX));}),_hZ=new T(function(){return B(unCStr(">"));}),_i0=new T(function(){return B(unCStr(" checked=\"checked\""));}),_i1=new T(function(){return B(_A(_i0,_hZ));}),_i2=new T(function(){return B(_gz("Main.hs:426:15-68|Right auto"));}),_i3=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:310:7-14"));}),_i4=[0,_2Y,_2Z,_12,_i3,_2Y,_2Y],_i5=new T(function(){return B(_2W(_i4));}),_i6=new T(function(){return B(unCStr("\'#494\'}}"));}),_i7=new T(function(){return B(unCStr("\'#c4f\'}}"));}),_i8=new T(function(){return B(unCStr("\'#f94\'}}"));}),_i9=function(_ia,_ib){if(_ia<=_ib){var _ic=function(_id){return [1,_id,new T(function(){if(_id!=_ib){return B(_ic(_id+1|0));}else{return [0];}})];};return new F(function(){return _ic(_ia);});}else{return [0];}},_ie=new T(function(){return B(_i9(1,5));}),_if=new T(function(){return B(unCStr("<span class=\"label label-success\">O</span>"));}),_ig=new T(function(){return B(unCStr("<span class=\"label label-danger\">X</span>"));}),_ih=(function(id){return document.getElementById(id);}),_ii=function(_ij,_ik){var _il=function(_){var _im=E(_ih)(E(_ik)),_in=__eq(_im,E(_3l));return (E(_in)==0)?[1,_im]:_2Y;};return new F(function(){return A(_gN,[_ij,_il]);});},_io="accept-check-text",_ip=new T(function(){return B(_ii(_4u,_io));}),_iq=new T(function(){return B(_gz("Main.hs:398:11-64|Right auto"));}),_ir="import-text",_is=new T(function(){return B(_ii(_4u,_ir));}),_it=new T(function(){return B(unCStr("innerText"));}),_iu=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:391:7-12"));}),_iv="export-text",_iw=new T(function(){return B(_ii(_4u,_iv));}),_ix="select-target",_iy=new T(function(){return B(_ii(_4u,_ix));}),_iz="select-alphabet",_iA=new T(function(){return B(_ii(_4u,_iz));}),_iB="select-source",_iC=new T(function(){return B(_ii(_4u,_iB));}),_iD=function(_iE,_iF){while(1){var _iG=E(_iE);if(!_iG[0]){var _iH=_iG[1],_iI=E(_iF);if(!_iI[0]){var _iJ=_iI[1],_iK=addC(_iH,_iJ);if(!E(_iK[2])){return [0,_iK[1]];}else{_iE=[1,I_fromInt(_iH)];_iF=[1,I_fromInt(_iJ)];continue;}}else{_iE=[1,I_fromInt(_iH)];_iF=_iI;continue;}}else{var _iL=E(_iF);if(!_iL[0]){_iE=_iG;_iF=[1,I_fromInt(_iL[1])];continue;}else{return [1,I_add(_iG[1],_iL[1])];}}}},_iM=function(_iN,_iO){var _iP=E(_iN);return [0,_iP,new T(function(){var _iQ=B(_iM(B(_iD(_iP,_iO)),_iO));return [1,_iQ[1],_iQ[2]];})];},_iR=[0,1],_iS=new T(function(){var _iT=B(_iM(_iR,_iR));return [1,_iT[1],_iT[2]];}),_iU=new T(function(){return B(unCStr("\">\u524a\u9664</button>"));}),_iV=new T(function(){return B(unCStr("select-target"));}),_iW=new T(function(){return B(unCStr("select-source"));}),_iX="new-alphabet",_iY=new T(function(){return B(_ii(_4u,_iX));}),_iZ="new-state",_j0=new T(function(){return B(_ii(_4u,_iZ));}),_j1=new T(function(){return B(_5v("Main.hs:(333,9)-(335,58)|case"));}),_j2=new T(function(){return B(unCStr("true"));}),_j3=new T(function(){return B(unCStr("false"));}),_j4=new T(function(){return B(unCStr("checked"));}),_j5=new T(function(){return B(_ii(_4u,_gb));}),_j6=new T(function(){return B(unCStr(","));}),_j7=34,_j8=[1,_j7,_12],_j9=new T(function(){return B(unCStr("!!: negative index"));}),_ja=new T(function(){return B(_A(_bs,_j9));}),_jb=new T(function(){return B(err(_ja));}),_jc=new T(function(){return B(unCStr("!!: index too large"));}),_jd=new T(function(){return B(_A(_bs,_jc));}),_je=new T(function(){return B(err(_jd));}),_jf=function(_jg,_jh){while(1){var _ji=E(_jg);if(!_ji[0]){return E(_je);}else{var _jj=E(_jh);if(!_jj){return E(_ji[1]);}else{_jg=_ji[2];_jh=_jj-1|0;continue;}}}},_jk=function(_jl,_jm){if(_jm>=0){return new F(function(){return _jf(_jl,_jm);});}else{return E(_jb);}},_jn=new T(function(){return B(unCStr("ACK"));}),_jo=new T(function(){return B(unCStr("BEL"));}),_jp=new T(function(){return B(unCStr("BS"));}),_jq=new T(function(){return B(unCStr("SP"));}),_jr=[1,_jq,_12],_js=new T(function(){return B(unCStr("US"));}),_jt=[1,_js,_jr],_ju=new T(function(){return B(unCStr("RS"));}),_jv=[1,_ju,_jt],_jw=new T(function(){return B(unCStr("GS"));}),_jx=[1,_jw,_jv],_jy=new T(function(){return B(unCStr("FS"));}),_jz=[1,_jy,_jx],_jA=new T(function(){return B(unCStr("ESC"));}),_jB=[1,_jA,_jz],_jC=new T(function(){return B(unCStr("SUB"));}),_jD=[1,_jC,_jB],_jE=new T(function(){return B(unCStr("EM"));}),_jF=[1,_jE,_jD],_jG=new T(function(){return B(unCStr("CAN"));}),_jH=[1,_jG,_jF],_jI=new T(function(){return B(unCStr("ETB"));}),_jJ=[1,_jI,_jH],_jK=new T(function(){return B(unCStr("SYN"));}),_jL=[1,_jK,_jJ],_jM=new T(function(){return B(unCStr("NAK"));}),_jN=[1,_jM,_jL],_jO=new T(function(){return B(unCStr("DC4"));}),_jP=[1,_jO,_jN],_jQ=new T(function(){return B(unCStr("DC3"));}),_jR=[1,_jQ,_jP],_jS=new T(function(){return B(unCStr("DC2"));}),_jT=[1,_jS,_jR],_jU=new T(function(){return B(unCStr("DC1"));}),_jV=[1,_jU,_jT],_jW=new T(function(){return B(unCStr("DLE"));}),_jX=[1,_jW,_jV],_jY=new T(function(){return B(unCStr("SI"));}),_jZ=[1,_jY,_jX],_k0=new T(function(){return B(unCStr("SO"));}),_k1=[1,_k0,_jZ],_k2=new T(function(){return B(unCStr("CR"));}),_k3=[1,_k2,_k1],_k4=new T(function(){return B(unCStr("FF"));}),_k5=[1,_k4,_k3],_k6=new T(function(){return B(unCStr("VT"));}),_k7=[1,_k6,_k5],_k8=new T(function(){return B(unCStr("LF"));}),_k9=[1,_k8,_k7],_ka=new T(function(){return B(unCStr("HT"));}),_kb=[1,_ka,_k9],_kc=[1,_jp,_kb],_kd=[1,_jo,_kc],_ke=[1,_jn,_kd],_kf=new T(function(){return B(unCStr("ENQ"));}),_kg=[1,_kf,_ke],_kh=new T(function(){return B(unCStr("EOT"));}),_ki=[1,_kh,_kg],_kj=new T(function(){return B(unCStr("ETX"));}),_kk=[1,_kj,_ki],_kl=new T(function(){return B(unCStr("STX"));}),_km=[1,_kl,_kk],_kn=new T(function(){return B(unCStr("SOH"));}),_ko=[1,_kn,_km],_kp=new T(function(){return B(unCStr("NUL"));}),_kq=[1,_kp,_ko],_kr=92,_ks=new T(function(){return B(unCStr("\\DEL"));}),_kt=new T(function(){return B(unCStr("\\a"));}),_ku=new T(function(){return B(unCStr("\\\\"));}),_kv=new T(function(){return B(unCStr("\\SO"));}),_kw=new T(function(){return B(unCStr("\\r"));}),_kx=new T(function(){return B(unCStr("\\f"));}),_ky=new T(function(){return B(unCStr("\\v"));}),_kz=new T(function(){return B(unCStr("\\n"));}),_kA=new T(function(){return B(unCStr("\\t"));}),_kB=new T(function(){return B(unCStr("\\b"));}),_kC=function(_kD,_kE){if(_kD<=127){var _kF=E(_kD);switch(_kF){case 92:return new F(function(){return _A(_ku,_kE);});break;case 127:return new F(function(){return _A(_ks,_kE);});break;default:if(_kF<32){var _kG=E(_kF);switch(_kG){case 7:return new F(function(){return _A(_kt,_kE);});break;case 8:return new F(function(){return _A(_kB,_kE);});break;case 9:return new F(function(){return _A(_kA,_kE);});break;case 10:return new F(function(){return _A(_kz,_kE);});break;case 11:return new F(function(){return _A(_ky,_kE);});break;case 12:return new F(function(){return _A(_kx,_kE);});break;case 13:return new F(function(){return _A(_kw,_kE);});break;case 14:return new F(function(){return _A(_kv,new T(function(){var _kH=E(_kE);if(!_kH[0]){return [0];}else{if(E(_kH[1])==72){return B(unAppCStr("\\&",_kH));}else{return E(_kH);}}},1));});break;default:return new F(function(){return _A([1,_kr,new T(function(){return B(_jk(_kq,_kG));})],_kE);});}}else{return [1,_kF,_kE];}}}else{var _kI=new T(function(){var _kJ=jsShowI(_kD);return B(_A(fromJSStr(_kJ),new T(function(){var _kK=E(_kE);if(!_kK[0]){return [0];}else{var _kL=E(_kK[1]);if(_kL<48){return E(_kK);}else{if(_kL>57){return E(_kK);}else{return B(unAppCStr("\\&",_kK));}}}},1)));});return [1,_kr,_kI];}},_kM=39,_kN=[1,_kM,_12],_kO=new T(function(){return B(unCStr("}}"));}),_kP=new T(function(){return B(unCStr("\'\\\'\'"));}),_kQ=new T(function(){return B(_A(_kP,_12));}),_kR=new T(function(){return B(unCStr("\\\""));}),_kS=function(_kT,_kU){var _kV=E(_kT);if(!_kV[0]){return E(_kU);}else{var _kW=_kV[2],_kX=E(_kV[1]);if(_kX==34){return new F(function(){return _A(_kR,new T(function(){return B(_kS(_kW,_kU));},1));});}else{return new F(function(){return _kC(_kX,new T(function(){return B(_kS(_kW,_kU));}));});}}},_kY=function(_kZ,_l0,_l1){var _l2=new T(function(){var _l3=new T(function(){var _l4=new T(function(){var _l5=new T(function(){var _l6=new T(function(){var _l7=E(_l0);if(_l7==39){return B(_A(_kQ,_kO));}else{return B(_A([1,_kM,new T(function(){return B(_kC(_l7,_kN));})],_kO));}});return B(unAppCStr(", label: ",_l6));},1);return B(_A([1,_j7,new T(function(){return B(_kS(_l1,_j8));})],_l5));});return B(unAppCStr(", target: ",_l4));},1);return B(_A([1,_j7,new T(function(){return B(_kS(_kZ,_j8));})],_l3));});return new F(function(){return unAppCStr("{data: {source: ",_l2);});},_l8=function(_l9){var _la=E(_l9);return new F(function(){return _kY(_la[1],_la[2],_la[3]);});},_lb=function(_lc){return new F(function(){return _gz("Main.hs:178:25-90|[(_, b, _)]");});},_ld=new T(function(){return B(_lb(_));}),_le=function(_lf){return new F(function(){return _gz("Main.hs:185:11-97|[(_, b0, _)]");});},_lg=new T(function(){return B(_le(_));}),_lh=new T(function(){return B(unCStr("{\"final\":[\"q1\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q1\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\"]}"));}),_li=new T(function(){return B(unCStr("NFA"));}),_lj=new T(function(){return B(unCStr("a*b"));}),_lk=[0,_lj,_li,_lh],_ll=[1,_lk,_12],_lm=new T(function(){return B(unCStr("{\"final\":[\"q0\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"0\",\"q0\"],[\"q0\",\"1\",\"q1\"],[\"q1\",\"1\",\"q0\"],[\"q1\",\"0\",\"q2\"],[\"q2\",\"0\",\"q1\"],[\"q2\",\"1\",\"q2\"]],\"alphabet\":\"01\",\"state\":[\"q0\",\"q1\",\"q2\"]}"));}),_ln=new T(function(){return B(unCStr("DFA"));}),_lo=new T(function(){return B(unCStr("multiple of 3"));}),_lp=[0,_lo,_ln,_lm],_lq=[1,_lp,_ll],_lr=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"a\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q1\",\"b\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_ls=new T(function(){return B(unCStr("worst NFAtoDFA efficiency"));}),_lt=[0,_ls,_li,_lr],_lu=[1,_lt,_lq],_lv=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"b\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_lw=new T(function(){return B(unCStr("exmple2"));}),_lx=[0,_lw,_li,_lv],_ly=[1,_lx,_lu],_lz=new T(function(){return B(unCStr("{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q1\"],[\"q0\",\"b\",\"q2\"],[\"q1\",\"a\",\"q3\"],[\"q2\",\"a\",\"q2\"],[\"q2\",\"b\",\"q3\"],[\"q3\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"));}),_lA=new T(function(){return B(unCStr("exmple1"));}),_lB=[0,_lA,_li,_lz],_lC=[1,_lB,_ly],_lD=function(_lE,_lF,_lG){var _lH=E(_lF);return new F(function(){return A(_lE,[_lH,new T(function(){return B(_lD(_lE,B(_iD(_lH,_lG)),_lG));})]);});},_lI=function(_lJ,_lK,_lL){var _lM=E(_lL);return (_lM[0]==0)?[0]:[1,[0,_lJ,_lM[1]],new T(function(){return B(A(_lK,[_lM[2]]));})];},_lN=new T(function(){return B(_lD(_lI,_iR,_iR));}),_lO=new T(function(){return B(A(_lN,[_lC]));}),_lP=new T(function(){return B(unCStr("]"));}),_lQ=function(_lR,_lS){var _lT=E(_lS);return (_lT[0]==0)?[0]:[1,_lR,[1,_lT[1],new T(function(){return B(_lQ(_lR,_lT[2]));})]];},_lU=function(_lV){var _lW=new T(function(){var _lX=E(_lV);if(!_lX[0]){return E(_lP);}else{return B(_A(B(_h9([1,_lX[1],new T(function(){return B(_lQ(_j6,_lX[2]));})])),_lP));}});return new F(function(){return unAppCStr("[",_lW);});},_lY=function(_lZ){var _m0=E(_lZ);return [0,new T(function(){return B(_lU(_m0[1]));}),_m0[2],new T(function(){return B(_lU(_m0[3]));})];},_m1=new T(function(){return B(unCStr("\">Load</button>"));}),_m2=function(_m3,_m4,_m5){var _m6=E(_m5);if(!_m6[0]){return [0];}else{var _m7=new T(function(){var _m8=E(_m6[1]),_m9=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"load-",new T(function(){return B(_A(B(_eY(0,_m3,_12)),_m1));})));});return B(_el(_m8[1],[1,_m8[2],[1,_m9,_12]]));});return new F(function(){return _A(B(unAppCStr("<tr>",_m7)),new T(function(){return B(A(_m4,[_m6[2]]));},1));});}},_ma=new T(function(){return B(_lD(_m2,_iR,_iR));}),_mb=function(_mc){var _md=E(_mc);return [0,_md[1],_md[2]];},_me=new T(function(){return B(_6v(_mb,_lC));}),_mf=new T(function(){return B(A(_ma,[_me]));}),_mg=function(_mh){return new F(function(){return _gz("Main.hs:186:11-77|[(_, b1, c)]");});},_mi=new T(function(){return B(_mg(_));}),_mj=new T(function(){return B(unCStr("\">Go</button>"));}),_mk=function(_ml,_mm,_mn){var _mo=E(_mn);if(!_mo[0]){return [0];}else{var _mp=new T(function(){var _mq=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"convert-",new T(function(){return B(_A(B(_eY(0,_ml,_12)),_mj));})));});return B(_el(_mo[1],[1,_mq,_12]));});return new F(function(){return _A(B(unAppCStr("<tr>",_mp)),new T(function(){return B(A(_mm,[_mo[2]]));},1));});}},_mr=new T(function(){return B(_lD(_mk,_iR,_iR));}),_ms=new T(function(){return B(unCStr("NFAtoDFA"));}),_mt=new T(function(){return B(unCStr("NFAtoRegExp"));}),_mu=[1,_mt,_12],_mv=[1,_ms,_mu],_mw=new T(function(){return B(A(_mr,[_mv]));}),_mx=function(_my,_mz){var _mA=E(_my),_mB=E(_mz);if(!B(_n(_mA[1],_mB[1]))){return false;}else{if(E(_mA[2])!=E(_mB[2])){return false;}else{return new F(function(){return _n(_mA[3],_mB[3]);});}}},_mC=function(_mD){return E(E(_mD)[1]);},_mE=function(_mF){return E(E(_mF)[2]);},_mG=function(_mH){return E(E(_mH)[1]);},_mI=function(_){return new F(function(){return nMV(_2Y);});},_mJ=new T(function(){return B(_3h(_mI));}),_mK=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_mL=function(_mM){return E(E(_mM)[2]);},_mN=function(_mO,_mP,_mQ,_mR,_mS,_mT){var _mU=B(_mC(_mO)),_mV=B(_gF(_mU)),_mW=new T(function(){return B(_gN(_mU));}),_mX=new T(function(){return B(_gX(_mV));}),_mY=new T(function(){return B(A(_gL,[_mP,_mR]));}),_mZ=new T(function(){return B(A(_mG,[_mQ,_mS]));}),_n0=function(_n1){return new F(function(){return A(_mX,[[0,_mZ,_mY,_n1]]);});},_n2=function(_n3){var _n4=new T(function(){var _n5=new T(function(){var _n6=__createJSFunc(2,function(_n7,_){var _n8=B(A(E(_n3),[_n7,_]));return _3l;}),_n9=_n6;return function(_){return new F(function(){return E(_mK)(E(_mY),E(_mZ),_n9);});};});return B(A(_mW,[_n5]));});return new F(function(){return A(_gH,[_mV,_n4,_n0]);});},_na=new T(function(){var _nb=new T(function(){return B(_gN(_mU));}),_nc=function(_nd){var _ne=new T(function(){return B(A(_nb,[function(_){var _=wMV(E(_mJ),[1,_nd]);return new F(function(){return A(_mE,[_mQ,_mS,_nd,_]);});}]));});return new F(function(){return A(_gH,[_mV,_ne,_mT]);});};return B(A(_mL,[_mO,_nc]));});return new F(function(){return A(_gH,[_mV,_na,_n2]);});},_nf=new T(function(){return B(unCStr(" found!"));}),_ng=function(_nh){return new F(function(){return err(B(unAppCStr("No element with ID ",new T(function(){return B(_A(fromJSStr(E(_nh)),_nf));}))));});},_ni=function(_nj,_nk,_nl){var _nm=new T(function(){var _nn=function(_){var _no=E(_ih)(E(_nk)),_np=__eq(_no,E(_3l));return (E(_np)==0)?[1,_no]:_2Y;};return B(A(_gN,[_nj,_nn]));});return new F(function(){return A(_gH,[B(_gF(_nj)),_nm,function(_nq){var _nr=E(_nq);if(!_nr[0]){return new F(function(){return _ng(_nk);});}else{return new F(function(){return A(_nl,[_nr[1]]);});}}]);});},_ns=new T(function(){return B(unCStr("<input type=\"text\" class=\"form-control input-sm\" id=\"new-alphabet\">"));}),_nt=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-alphabet\">\u8ffd\u52a0</button>"));}),_nu=[1,_nt,_12],_nv=new T(function(){return B(_el(_ns,_nu));}),_nw=new T(function(){return B(unAppCStr("<tr>",_nv));}),_nx=new T(function(){return B(_A(_nw,_12));}),_ny=new T(function(){return B(unCStr("<input type=\"text\" class=\"form-control input-sm\" id=\"new-state\">"));}),_nz=new T(function(){return B(unCStr("<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-state\">\u8ffd\u52a0</button>"));}),_nA=[1,_nz,_12],_nB=new T(function(){return B(_el(_ny,_nA));}),_nC=new T(function(){return B(unAppCStr("<tr>",_nB));}),_nD=new T(function(){return B(_A(_nC,_12));}),_nE=function(_nF,_){var _nG=rMV(_nF),_nH=new T(function(){var _nI=E(E(_nG)[1]),_nJ=E(_nI[3]),_nK=E(_nJ[3]),_nL=new T(function(){var _nM=new T(function(){var _nN=B(_6v(_l8,E(_nK[2])[1]));if(!_nN[0]){return E(_gs);}else{return B(_A(B(_h9([1,_nN[1],new T(function(){return B(_lQ(_j6,_nN[2]));})])),_gs));}});return B(unAppCStr("], edges: [",_nM));}),_nO=function(_nP){var _nQ=new T(function(){var _nR=new T(function(){var _nS=new T(function(){var _nT=new T(function(){return B(unAppCStr(", color: ",new T(function(){if(!B(_cN(_s,_nP,E(_nI[2])[1]))){if(!B(_9M(_nP,E(_nJ[2])[1]))){return E(_i8);}else{return E(_i7);}}else{return E(_i6);}})));},1);return B(_A([1,_j7,new T(function(){return B(_kS(_nP,_j8));})],_nT));});return B(unAppCStr(", id: ",_nS));},1);return B(_A([1,_j7,new T(function(){return B(_kS(_nP,_j8));})],_nR));});return new F(function(){return unAppCStr("{data: {label: ",_nQ);});},_nU=B(_6v(_nO,E(E(E(_nK[3])[3])[2])[1]));if(!_nU[0]){return E(_nL);}else{return B(_A(B(_h9([1,_nU[1],new T(function(){return B(_lQ(_j6,_nU[2]));})])),_nL));}}),_nV=E(_gx)(toJSStr(B(unAppCStr("  var cy = cytoscape({  container: document.getElementById(\'cy\'),  style: cytoscape.stylesheet()    .selector(\'node\').css({      \'background-color\': \'data(color)\',      \'text-valign\': \'center\',      \'content\': \'data(id)\'    })    .selector(\'edge\').css({      \'target-arrow-shape\': \'triangle\',      \'line-color\': \'#a9f\',      \'target-arrow-color\': \'#a9f\',      \'text-valign\': \'top\',      \'width\': 3,      \'content\': \'data(label)\'    }),  elements: { nodes: [",_nH)))),_nW=function(_nX,_){var _nY=rMV(_nF),_nZ=E(E(E(_nY)[1])[3]),_o0=function(_o1){var _o2=E(_hp)(E(_nX),toJSStr(E(_hS)),toJSStr(_o1));return new F(function(){return _3O(_);});},_o3=E(E(E(E(E(_nZ[3])[3])[3])[2])[1]);if(!_o3[0]){return new F(function(){return _o0(_12);});}else{var _o4=_o3[1],_o5=_o3[2],_o6=E(_nZ[2])[1];if(!B(_9M(_o4,_o6))){var _o7=new T(function(){var _o8=function(_o9){var _oa=E(_o9);if(!_oa[0]){return [0];}else{var _ob=_oa[1],_oc=_oa[2];if(!B(_9M(_ob,_o6))){return new F(function(){return _A(B(unAppCStr("<option>",new T(function(){return B(_A(_ob,_hR));}))),new T(function(){return B(_o8(_oc));},1));});}else{return new F(function(){return _A(B(unAppCStr("<option selected=\"selected\">",new T(function(){return B(_A(_ob,_hR));}))),new T(function(){return B(_o8(_oc));},1));});}}};return B(_o8(_o5));},1);return new F(function(){return _o0(B(_A(B(unAppCStr("<option>",new T(function(){return B(_A(_o4,_hR));}))),_o7)));});}else{var _od=new T(function(){var _oe=function(_of){var _og=E(_of);if(!_og[0]){return [0];}else{var _oh=_og[1],_oi=_og[2];if(!B(_9M(_oh,_o6))){return new F(function(){return _A(B(unAppCStr("<option>",new T(function(){return B(_A(_oh,_hR));}))),new T(function(){return B(_oe(_oi));},1));});}else{return new F(function(){return _A(B(unAppCStr("<option selected=\"selected\">",new T(function(){return B(_A(_oh,_hR));}))),new T(function(){return B(_oe(_oi));},1));});}}};return B(_oe(_o5));},1);return new F(function(){return _o0(B(_A(B(unAppCStr("<option selected=\"selected\">",new T(function(){return B(_A(_o4,_hR));}))),_od)));});}}},_oj=B(A(_ni,[_4u,_gb,_nW,_])),_ok=function(_){var _ol=B(A(_j5,[_])),_om=E(_ol);if(!_om[0]){return new F(function(){return die(_i5);});}else{var _on=E(_gE)(E(_om[1]),E(_gD)),_oo=rMV(_nF),_op=[0,new T(function(){var _oq=E(E(_oo)[1]),_or=new T(function(){var _os=E(_oq[3]),_ot=E(_os[2]);return [1,_,[0,new T(function(){var _ou=String(_on);return fromJSStr(_ou);})],_os[3]];});return [1,_,_oq[2],_or];})],_=wMV(_nF,_op);return new F(function(){return _nE(_nF,_);});}},_ov=function(_ow,_){return new F(function(){return _ok(_);});},_ox=B(A(_ni,[_4u,_gc,function(_oy){return new F(function(){return _mN(_4v,_3T,_3M,_oy,_fQ,_ov);});},_])),_oz=function(_oA,_){var _oB=rMV(_nF),_oC=new T(function(){return E(E(E(E(_oB)[1])[2])[1]);}),_oD=function(_oE,_oF){var _oG=E(_oE);if(!_oG[0]){return E(_nD);}else{var _oH=_oG[1],_oI=E(_oF);if(!_oI[0]){return E(_nD);}else{var _oJ=_oI[1],_oK=new T(function(){var _oL=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-state-",new T(function(){return B(_A(B(_eY(0,_oH,_12)),_iU));})));}),_oM=new T(function(){var _oN=new T(function(){var _oO=new T(function(){return B(unAppCStr("\"",new T(function(){if(!B(_cN(_s,_oJ,_oC))){return E(_hZ);}else{return E(_i1);}})));},1);return B(_A(B(_eY(0,_oH,_12)),_oO));});return B(unAppCStr("<input type=\"checkbox\" id=\"state-final-",_oN));});return B(_el(_oJ,[1,_oM,[1,_oL,_12]]));});return new F(function(){return _A(B(unAppCStr("<tr>",_oK)),new T(function(){return B(_oD(_oG[2],_oI[2]));},1));});}}},_oP=E(_hp)(E(_oA),toJSStr(E(_hS)),toJSStr(B(_oD(_iS,new T(function(){return E(E(E(E(E(E(E(E(_oB)[1])[3])[3])[3])[3])[2])[1]);},1)))));return new F(function(){return _3O(_);});},_oQ=B(A(_ni,[_4u,_go,_oz,_])),_oR=rMV(_nF),_oS=function(_oT,_oU,_){while(1){var _oV=B((function(_oW,_oX,_){var _oY=E(_oW);if(!_oY[0]){return _3N;}else{var _oZ=_oY[1],_p0=E(_oX);if(!_p0[0]){return _3N;}else{var _p1=_p0[1],_p2=function(_){var _p3=rMV(_nF),_p4=[0,new T(function(){var _p5=E(E(_p3)[1]),_p6=new T(function(){var _p7=E(_p5[3]),_p8=new T(function(){var _p9=E(_p7[3]),_pa=new T(function(){var _pb=E(_p9[3]),_pc=new T(function(){var _pd=E(_pb[3]);return [1,_,[0,new T(function(){return B(_fS(_9M,_p1,E(_pd[2])[1]));})],_pd[3]];});return [1,_,_pb[2],_pc];});return [1,_,_p9[2],_pa];});return [1,_,_p7[2],_p8];});return [1,_,_p5[2],_p6];})],_=wMV(_nF,_p4),_pe=rMV(_nF),_pf=[0,new T(function(){var _pg=E(E(_pe)[1]),_ph=new T(function(){var _pi=E(_pg[3]),_pj=new T(function(){var _pk=E(_pi[3]),_pl=new T(function(){return B(_bh(function(_pm){var _pn=E(_pm);if(!B(_f(_p1,_pn[1]))){return new F(function(){return _k(_p1,_pn[3]);});}else{return false;}},E(_pk[2])[1]));});return [1,_,[0,_pl],_pk[3]];});return [1,_,_pi[2],_pj];});return [1,_,_pg[2],_ph];})],_=wMV(_nF,_pf),_po=rMV(_nF),_pp=[0,new T(function(){var _pq=E(E(_po)[1]);return [1,_,[0,new T(function(){return B(_fS(_9M,_p1,E(_pq[2])[1]));})],_pq[3]];})],_=wMV(_nF,_pp);return new F(function(){return _nE(_nF,_);});},_pr=function(_ps,_){return new F(function(){return _p2(_);});},_pt=new T(function(){return toJSStr(B(unAppCStr("delete-state-",new T(function(){return B(_eY(0,_oZ,_12));}))));}),_pu=B(A(_ni,[_4u,_pt,function(_pv){return new F(function(){return _mN(_4v,_3T,_3M,_pv,_fQ,_pr);});},_])),_pw=function(_px){var _py=function(_pz,_){var _pA=B(A(_gZ,[_3T,_4u,_px,_j4,_]));if(!B(_9M(_pA,_j3))){if(!B(_9M(_pA,_j2))){return E(_j1);}else{var _pB=rMV(_nF),_pC=[0,new T(function(){var _pD=E(E(_pB)[1]);return [1,_,[0,[1,_p1,new T(function(){return E(E(_pD[2])[1]);})]],_pD[3]];})],_=wMV(_nF,_pC);return new F(function(){return _nE(_nF,_);});}}else{var _pE=rMV(_nF),_pF=[0,new T(function(){var _pG=E(E(_pE)[1]);return [1,_,[0,new T(function(){return B(_fS(_9M,_p1,E(_pG[2])[1]));})],_pG[3]];})],_=wMV(_nF,_pF);return new F(function(){return _nE(_nF,_);});}};return new F(function(){return _mN(_4v,_3T,_3M,_px,_fQ,_py);});},_pH=new T(function(){return toJSStr(B(unAppCStr("state-final-",new T(function(){return B(_eY(0,_oZ,_12));}))));}),_pI=B(A(_ni,[_4u,_pH,_pw,_]));_oT=_oY[2];_oU=_p0[2];return null;}}})(_oT,_oU,_));if(_oV!=null){return _oV;}}},_pJ=B(_oS(_iS,new T(function(){return E(E(E(E(E(E(E(E(_oR)[1])[3])[3])[3])[3])[2])[1]);},1),_)),_pK=function(_){var _pL=B(A(_j0,[_])),_pM=E(_pL);if(!_pM[0]){return new F(function(){return die(_hY);});}else{var _pN=E(_gE)(E(_pM[1]),E(_gD)),_pO=rMV(_nF),_pP=[0,new T(function(){var _pQ=E(E(_pO)[1]),_pR=new T(function(){var _pS=E(_pQ[3]),_pT=new T(function(){var _pU=E(_pS[3]),_pV=new T(function(){var _pW=E(_pU[3]),_pX=new T(function(){var _pY=E(_pW[3]),_pZ=new T(function(){return B(_A(E(_pY[2])[1],[1,new T(function(){var _q0=String(_pN);return fromJSStr(_q0);}),_12]));});return [1,_,[0,_pZ],_pY[3]];});return [1,_,_pW[2],_pX];});return [1,_,_pU[2],_pV];});return [1,_,_pS[2],_pT];});return [1,_,_pQ[2],_pR];})],_=wMV(_nF,_pP);return new F(function(){return _nE(_nF,_);});}},_q1=function(_q2,_){return new F(function(){return _pK(_);});},_q3=B(A(_ni,[_4u,_gp,function(_q4){return new F(function(){return _mN(_4v,_3T,_3M,_q4,_fQ,_q1);});},_])),_q5=function(_q6,_){var _q7=rMV(_nF),_q8=function(_q9){var _qa=E(_q9);if(!_qa[0]){return E(_nx);}else{var _qb=_qa[1],_qc=new T(function(){return B(_el([1,_qb,_12],[1,new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-alphabet-",[1,_qb,_iU]));}),_12]));});return new F(function(){return _A(B(unAppCStr("<tr>",_qc)),new T(function(){return B(_q8(_qa[2]));},1));});}},_qd=E(_hp)(E(_q6),toJSStr(E(_hS)),toJSStr(B(_q8(E(E(E(E(E(E(_q7)[1])[3])[3])[3])[2])[1]))));return new F(function(){return _3O(_);});},_qe=B(A(_ni,[_4u,_gq,_q5,_])),_qf=rMV(_nF),_qg=function(_qh,_){while(1){var _qi=B((function(_qj,_){var _qk=E(_qj);if(!_qk[0]){return _3N;}else{var _ql=_qk[1],_qm=function(_){var _qn=rMV(_nF),_qo=[0,new T(function(){var _qp=E(E(_qn)[1]),_qq=new T(function(){var _qr=E(_qp[3]),_qs=new T(function(){var _qt=E(_qr[3]),_qu=new T(function(){var _qv=E(_qt[3]);return [1,_,[0,new T(function(){return B(_fS(_4,_ql,E(_qv[2])[1]));})],_qv[3]];});return [1,_,_qt[2],_qu];});return [1,_,_qr[2],_qs];});return [1,_,_qp[2],_qq];})],_=wMV(_nF,_qo),_qw=rMV(_nF),_qx=[0,new T(function(){var _qy=E(E(_qw)[1]),_qz=new T(function(){var _qA=E(_qy[3]),_qB=new T(function(){var _qC=E(_qA[3]),_qD=new T(function(){return B(_bh(function(_qE){return new F(function(){return _1(_ql,E(_qE)[2]);});},E(_qC[2])[1]));});return [1,_,[0,_qD],_qC[3]];});return [1,_,_qA[2],_qB];});return [1,_,_qy[2],_qz];})],_=wMV(_nF,_qx);return new F(function(){return _nE(_nF,_);});},_qF=function(_qG,_){return new F(function(){return _qm(_);});},_qH=B(A(_ni,[_4u,new T(function(){return toJSStr(B(unAppCStr("delete-alphabet-",[1,_ql,_12])));}),function(_qI){return new F(function(){return _mN(_4v,_3T,_3M,_qI,_fQ,_qF);});},_]));_qh=_qk[2];return null;}})(_qh,_));if(_qi!=null){return _qi;}}},_qJ=B(_qg(E(E(E(E(E(E(_qf)[1])[3])[3])[3])[2])[1],_)),_qK=function(_){var _qL=B(A(_iY,[_])),_qM=E(_qL);if(!_qM[0]){return new F(function(){return die(_hV);});}else{var _qN=E(_gE)(E(_qM[1]),E(_gD)),_qO=String(_qN),_qP=fromJSStr(_qO);if(!_qP[0]){return new F(function(){return _f5(_);});}else{if(!E(_qP[2])[0]){var _qQ=rMV(_nF),_qR=[0,new T(function(){var _qS=E(E(_qQ)[1]),_qT=new T(function(){var _qU=E(_qS[3]),_qV=new T(function(){var _qW=E(_qU[3]),_qX=new T(function(){var _qY=E(_qW[3]);return [1,_,[0,new T(function(){return B(_A(E(_qY[2])[1],[1,_qP[1],_12]));})],_qY[3]];});return [1,_,_qW[2],_qX];});return [1,_,_qU[2],_qV];});return [1,_,_qS[2],_qT];})],_=wMV(_nF,_qR);return new F(function(){return _nE(_nF,_);});}else{return new F(function(){return _f5(_);});}}}},_qZ=function(_r0,_){return new F(function(){return _qK(_);});},_r1=B(A(_ni,[_4u,_gr,function(_r2){return new F(function(){return _mN(_4v,_3T,_3M,_r2,_fQ,_qZ);});},_])),_r3=function(_r4,_){var _r5=rMV(_nF),_r6=new T(function(){var _r7=new T(function(){var _r8=new T(function(){var _r9=new T(function(){var _ra=function(_rb){var _rc=E(_rb);if(!_rc[0]){return [0];}else{return new F(function(){return _A(B(unAppCStr("<option>",new T(function(){return B(_A(_rc[1],_hR));}))),new T(function(){return B(_ra(_rc[2]));},1));});}};return B(_A(B(_ra(E(E(E(E(E(E(E(_r5)[1])[3])[3])[3])[3])[2])[1])),_hQ));});return B(unAppCStr("\">",_r9));}),_rd=function(_re){return new F(function(){return unAppCStr("<select class=\"form-control input-sm\" id=\"",new T(function(){return B(_A(_re,_r8));}));});},_rf=new T(function(){var _rg=new T(function(){var _rh=function(_ri){var _rj=E(_ri);if(!_rj[0]){return E(_hQ);}else{return new F(function(){return _A(B(unAppCStr("<option>",[1,_rj[1],_hR])),new T(function(){return B(_rh(_rj[2]));},1));});}};return B(_rh(E(E(E(E(E(E(_r5)[1])[3])[3])[3])[2])[1]));});return B(unAppCStr("<select class=\"form-control input-sm\" id=\"select-alphabet\">",_rg));});return B(_el(new T(function(){return B(_rd(_iW));}),[1,_rf,[1,new T(function(){return B(_rd(_iV));}),_hP]]));});return B(_A(B(unAppCStr("<tr>",_r7)),_12));}),_rk=function(_rl,_rm){var _rn=E(_rl);if(!_rn[0]){return E(_r6);}else{var _ro=E(_rm);if(!_ro[0]){return E(_r6);}else{var _rp=new T(function(){var _rq=E(_ro[1]),_rr=new T(function(){return B(unAppCStr("<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-transition-",new T(function(){return B(_A(B(_eY(0,_rn[1],_12)),_iU));})));});return B(_el(_rq[1],[1,[1,_rq[2],_12],[1,_rq[3],[1,_rr,_12]]]));});return new F(function(){return _A(B(unAppCStr("<tr>",_rp)),new T(function(){return B(_rk(_rn[2],_ro[2]));},1));});}}},_rs=E(_hp)(E(_r4),toJSStr(E(_hS)),toJSStr(B(_rk(_iS,new T(function(){return E(E(E(E(E(E(_r5)[1])[3])[3])[2])[1]);},1)))));return new F(function(){return _3O(_);});},_rt=B(A(_ni,[_4u,_gt,_r3,_])),_ru=rMV(_nF),_rv=function(_rw,_rx,_){while(1){var _ry=B((function(_rz,_rA,_){var _rB=E(_rz);if(!_rB[0]){return _3N;}else{var _rC=E(_rA);if(!_rC[0]){return _3N;}else{var _rD=function(_){var _rE=rMV(_nF),_rF=[0,new T(function(){var _rG=E(E(_rE)[1]),_rH=new T(function(){var _rI=E(_rG[3]),_rJ=new T(function(){var _rK=E(_rI[3]);return [1,_,[0,new T(function(){return B(_fS(_hJ,_rC[1],E(_rK[2])[1]));})],_rK[3]];});return [1,_,_rI[2],_rJ];});return [1,_,_rG[2],_rH];})],_=wMV(_nF,_rF);return new F(function(){return _nE(_nF,_);});},_rL=function(_rM,_){return new F(function(){return _rD(_);});},_rN=new T(function(){return toJSStr(B(unAppCStr("delete-transition-",new T(function(){return B(_eY(0,_rB[1],_12));}))));}),_rO=B(A(_ni,[_4u,_rN,function(_rP){return new F(function(){return _mN(_4v,_3T,_3M,_rP,_fQ,_rL);});},_]));_rw=_rB[2];_rx=_rC[2];return null;}}})(_rw,_rx,_));if(_ry!=null){return _ry;}}},_rQ=B(_rv(_iS,new T(function(){return E(E(E(E(E(E(_ru)[1])[3])[3])[2])[1]);},1),_)),_rR=function(_){var _rS=B(A(_iC,[_])),_rT=E(_rS);if(!_rT[0]){return new F(function(){return die(_hI);});}else{var _rU=E(_gE),_rV=E(_gD),_rW=_rU(E(_rT[1]),_rV),_rX=B(A(_iA,[_])),_rY=E(_rX);if(!_rY[0]){return new F(function(){return die(_hF);});}else{var _rZ=_rU(E(_rY[1]),_rV),_s0=String(_rZ),_s1=fromJSStr(_s0);if(!_s1[0]){return new F(function(){return _f9(_);});}else{if(!E(_s1[2])[0]){var _s2=B(A(_iy,[_])),_s3=E(_s2);if(!_s3[0]){return new F(function(){return die(_hz);});}else{var _s4=_rU(E(_s3[1]),_rV),_s5=rMV(_nF),_s6=[0,new T(function(){var _s7=E(E(_s5)[1]),_s8=new T(function(){var _s9=E(_s7[3]),_sa=new T(function(){var _sb=E(_s9[3]),_sc=new T(function(){return B(_dy(_hJ,B(_A(E(_sb[2])[1],[1,[0,new T(function(){var _sd=String(_rW);return fromJSStr(_sd);}),_s1[1],new T(function(){var _se=String(_s4);return fromJSStr(_se);})],_12]))));});return [1,_,[0,_sc],_sb[3]];});return [1,_,_s9[2],_sa];});return [1,_,_s7[2],_s8];})],_=wMV(_nF,_s6);return new F(function(){return _nE(_nF,_);});}}else{return new F(function(){return _f9(_);});}}}}},_sf=function(_sg,_){return new F(function(){return _rR(_);});},_sh=B(A(_ni,[_4u,_gu,function(_si){return new F(function(){return _mN(_4v,_3T,_3M,_si,_fQ,_sf);});},_])),_sj=function(_){var _sk=rMV(_nF),_sl=B(A(_iw,[_])),_sm=E(_sl);if(!_sm[0]){return new F(function(){return _4q(_iu,_);});}else{var _sn=E(_hp)(E(_sm[1]),toJSStr(E(_it)),toJSStr(fromJSStr(B(_fM([4,E(B(_8C(_8S,_7t,E(_sk)[1])))])))));return new F(function(){return _3O(_);});}},_so=function(_sp,_){return new F(function(){return _sj(_);});},_sq=B(A(_ni,[_4u,_gv,function(_sr){return new F(function(){return _mN(_4v,_3T,_3M,_sr,_fQ,_so);});},_])),_ss=function(_){var _st=B(A(_is,[_])),_su=E(_st);if(!_su[0]){return new F(function(){return die(_hw);});}else{var _sv=E(_gE)(E(_su[1]),E(_gD)),_sw=new T(function(){var _sx=String(_sv),_sy=jsParseJSON(toJSStr(fromJSStr(_sx)));if(!_sy[0]){return E(_iq);}else{var _sz=E(_sy[1]);if(_sz[0]==4){var _sA=E(_sz[1]);if(!_sA[0]){return E(_8l);}else{var _sB=B(_7f(_6g,E(_sA[1])[2]));if(!_sB[0]){return E(_iq);}else{var _sC=E(_sA[2]);if(!_sC[0]){return E(_8l);}else{var _sD=E(E(_sC[1])[2]);if(_sD[0]==1){var _sE=E(_sC[2]);if(!_sE[0]){return E(_8l);}else{var _sF=B(_5O(_7q,_6g,_7q,E(_sE[1])[2]));if(!_sF[0]){return E(_iq);}else{var _sG=E(_sE[2]);if(!_sG[0]){return E(_8l);}else{var _sH=E(E(_sG[1])[2]);if(_sH[0]==1){var _sI=E(_sG[2]);if(!_sI[0]){return E(_6m);}else{var _sJ=B(_7f(_6g,E(_sI[1])[2]));if(!_sJ[0]){return E(_iq);}else{if(!E(_sI[2])[0]){return [0,[1,_,[0,_sB[1]],[1,_,[0,new T(function(){return fromJSStr(_sD[1]);})],[1,_,[0,_sF[1]],[1,_,[0,new T(function(){return fromJSStr(_sH[1]);})],[1,_,[0,_sJ[1]],_0]]]]]];}else{return E(_6j);}}}}else{return E(_iq);}}}}}else{return E(_iq);}}}}}else{return E(_8l);}}}),_=wMV(_nF,_sw);return new F(function(){return _nE(_nF,_);});}},_sK=function(_sL,_){return new F(function(){return _ss(_);});},_sM=B(A(_ni,[_4u,_gw,function(_sN){return new F(function(){return _mN(_4v,_3T,_3M,_sN,_fQ,_sK);});},_])),_sO=function(_){var _sP=B(A(_ip,[_])),_sQ=E(_sP);if(!_sQ[0]){return new F(function(){return die(_ht);});}else{var _sR=E(_gE)(E(_sQ[1]),E(_gD)),_sS=rMV(_nF),_sT=new T(function(){var _sU=String(_sR);if(!B(_cT(_sS,fromJSStr(_sU)))){return E(_ig);}else{return E(_if);}});return new F(function(){return A(_ni,[_4u,_ge,function(_sV,_){var _sW=E(_hp)(E(_sV),toJSStr(E(_hS)),toJSStr(E(_sT)));return new F(function(){return _3O(_);});},_]);});}},_sX=function(_sY,_){return new F(function(){return _sO(_);});},_sZ=B(A(_ni,[_4u,_gd,function(_t0){return new F(function(){return _mN(_4v,_3T,_3M,_t0,_fQ,_sX);});},_])),_t1=function(_t2,_){var _t3=rMV(_nF),_t4=_t3,_t5=new T(function(){return E(E(E(E(E(E(E(_t4)[1])[3])[3])[3])[2])[1]);}),_t6=function(_t7,_t8){var _t9=E(_t7);if(!_t9[0]){return [0];}else{var _ta=function(_tb,_tc){var _td=E(_tb);if(!_td[0]){return new F(function(){return _t6(_t9[2],_tc);});}else{var _te=_td[1],_tf=E(_tc);if(_tf==1){var _tg=new T(function(){return B(_el(_te,[1,new T(function(){if(!B(_cT(_t4,_te))){return E(_ig);}else{return E(_if);}}),_12]));});return new F(function(){return _A(B(unAppCStr("<tr>",_tg)),_12);});}else{var _th=new T(function(){return B(_el(_te,[1,new T(function(){if(!B(_cT(_t4,_te))){return E(_ig);}else{return E(_if);}}),_12]));});return new F(function(){return _A(B(unAppCStr("<tr>",_th)),new T(function(){return B(_ta(_td[2],_tf-1|0));},1));});}}};return new F(function(){return _ta(B(_eG(_t9[1],_t5)),_t8);});}},_ti=E(_hp)(E(_t2),toJSStr(E(_hS)),toJSStr(B(_t6(_ie,50))));return new F(function(){return _3O(_);});},_tj=B(A(_ni,[_4u,_gf,_t1,_])),_tk=function(_tl,_){while(1){var _tm=B((function(_tn,_){var _to=E(_tn);if(!_to[0]){return _3N;}else{var _tp=E(_to[1]),_tq=function(_){var _tr=new T(function(){var _ts=jsParseJSON(toJSStr(E(E(_tp[2])[3])));if(!_ts[0]){return E(_i2);}else{var _tt=E(_ts[1]);if(_tt[0]==4){var _tu=E(_tt[1]);if(!_tu[0]){return E(_8l);}else{var _tv=B(_7f(_6g,E(_tu[1])[2]));if(!_tv[0]){return E(_i2);}else{var _tw=E(_tu[2]);if(!_tw[0]){return E(_8l);}else{var _tx=E(E(_tw[1])[2]);if(_tx[0]==1){var _ty=E(_tw[2]);if(!_ty[0]){return E(_8l);}else{var _tz=B(_5O(_7q,_6g,_7q,E(_ty[1])[2]));if(!_tz[0]){return E(_i2);}else{var _tA=E(_ty[2]);if(!_tA[0]){return E(_8l);}else{var _tB=E(E(_tA[1])[2]);if(_tB[0]==1){var _tC=E(_tA[2]);if(!_tC[0]){return E(_6m);}else{var _tD=B(_7f(_6g,E(_tC[1])[2]));if(!_tD[0]){return E(_i2);}else{if(!E(_tC[2])[0]){return [0,[1,_,[0,_tv[1]],[1,_,[0,new T(function(){return fromJSStr(_tx[1]);})],[1,_,[0,_tz[1]],[1,_,[0,new T(function(){return fromJSStr(_tB[1]);})],[1,_,[0,_tD[1]],_0]]]]]];}else{return E(_6j);}}}}else{return E(_i2);}}}}}else{return E(_i2);}}}}}else{return E(_8l);}}}),_=wMV(_nF,_tr);return new F(function(){return _nE(_nF,_);});},_tE=function(_tF,_){return new F(function(){return _tq(_);});},_tG=new T(function(){return toJSStr(B(unAppCStr("load-",new T(function(){return B(_eY(0,_tp[1],_12));}))));}),_tH=B(A(_ni,[_4u,_tG,function(_tI){return new F(function(){return _mN(_4v,_3T,_3M,_tI,_fQ,_tE);});},_]));_tl=_to[2];return null;}})(_tl,_));if(_tm!=null){return _tm;}}},_tJ=B(A(_ni,[_4u,_gg,function(_tK,_){var _tL=rMV(_nF),_tM=E(_hp)(E(_tK),toJSStr(E(_hS)),toJSStr(E(_mf)));return new F(function(){return _tk(_lO,_);});},_])),_tN=function(_){var _tO=rMV(_nF),_tP=_tO,_tQ=new T(function(){var _tR=new T(function(){return E(E(E(E(E(E(E(_tP)[1])[3])[3])[3])[2])[1]);}),_tS=new T(function(){return E(E(E(E(_tP)[1])[2])[1]);}),_tT=function(_tU,_tV,_tW,_tX){while(1){var _tY=B((function(_tZ,_u0,_u1,_u2){var _u3=E(_tZ);if(!_u3[0]){return [0,_u0,_u1,_u2];}else{var _u4=_u3[1],_u5=[1,_u4,_u0],_u6=function(_u7){while(1){var _u8=B((function(_u9){var _ua=E(_u9);if(!_ua[0]){return E(_u3[2]);}else{var _ub=_ua[1],_uc=_ua[2];if(!B(_cN(_w,new T(function(){return B(_dL(E(_tP)[1],_u4,_ub));}),_u5))){return [1,new T(function(){return B(_ec(_tP,_u4,_ub));}),new T(function(){return B(_u6(_uc));})];}else{_u7=_uc;return null;}}})(_u7));if(_u8!=null){return _u8;}}},_ud=new T(function(){var _ue=function(_uf){var _ug=E(_uf);if(!_ug[0]){return E(_u1);}else{var _uh=_ug[1];return [1,[0,_u4,_uh,new T(function(){return B(_ec(_tP,_u4,_uh));})],new T(function(){return B(_ue(_ug[2]));})];}};return B(_dy(_mx,B(_ue(_tR))));});_tU=B(_dy(_n,B(_u6(_tR))));_tV=_u5;_tW=_ud;_tX=new T(function(){if(!B(_n(B(_hc(_9M,_u4,_tS)),_12))){return [1,_u4,_u2];}else{return E(_u2);}});return null;}})(_tU,_tV,_tW,_tX));if(_tY!=null){return _tY;}}},_ui=function(_uj,_uk,_ul,_um,_un){var _uo=[1,_uj,_ul],_up=function(_uq){while(1){var _ur=B((function(_us){var _ut=E(_us);if(!_ut[0]){return E(_uk);}else{var _uu=_ut[1],_uv=_ut[2];if(!B(_cN(_w,new T(function(){return B(_dL(E(_tP)[1],_uj,_uu));}),_uo))){return [1,new T(function(){return B(_ec(_tP,_uj,_uu));}),new T(function(){return B(_up(_uv));})];}else{_uq=_uv;return null;}}})(_uq));if(_ur!=null){return _ur;}}},_uw=new T(function(){var _ux=function(_uy){var _uz=E(_uy);if(!_uz[0]){return E(_um);}else{var _uA=_uz[1];return [1,[0,_uj,_uA,new T(function(){return B(_ec(_tP,_uj,_uA));})],new T(function(){return B(_ux(_uz[2]));})];}};return B(_dy(_mx,B(_ux(_tR))));});return new F(function(){return _tT(B(_dy(_n,B(_up(_tR)))),_uo,_uw,new T(function(){if(!B(_n(B(_hc(_9M,_uj,_tS)),_12))){return [1,_uj,_un];}else{return E(_un);}}));});},_uB=B(_ui([1,new T(function(){return E(E(E(E(E(_tP)[1])[3])[2])[1]);}),_12],_12,_12,_12,_12));return [0,_uB[1],_uB[2],_uB[3]];}),_uC=new T(function(){return B(_lU([1,new T(function(){return E(E(E(E(E(_tP)[1])[3])[2])[1]);}),_12]));}),_=wMV(_nF,[0,[1,_,[0,new T(function(){return B(_6v(_lU,E(_tQ)[3]));})],[1,_,[0,_uC],[1,_,[0,new T(function(){return B(_6v(_lY,E(_tQ)[2]));})],[1,_,[0,new T(function(){return E(E(E(E(E(E(E(_tP)[1])[3])[3])[3])[2])[1]);})],[1,_,[0,new T(function(){return B(_6v(_lU,E(_tQ)[1]));})],_0]]]]]]);return new F(function(){return _nE(_nF,_);});},_uD=function(_uE,_){return new F(function(){return _tN(_);});},_uF=function(_uG){return new F(function(){return _mN(_4v,_3T,_3M,_uG,_fQ,_uD);});},_uH=function(_){var _uI=rMV(_nF),_uJ=new T(function(){var _uK=new T(function(){var _uL=E(E(_uI)[1]),_uM=E(_uL[3]),_uN=E(_uM[3]),_uO=_uN[3],_uP=E(_uN[2])[1],_uQ=function(_uR){return (!B(_9(_af,_12,B(_bh(function(_uS){var _uT=E(_uS);if(!B(_9M(_uT[1],_uR))){return false;}else{return new F(function(){return _9M(_uT[3],_uR);});}},_uP)))))?true:false;},_uU=new T(function(){return E(E(_uM[2])[1]);}),_uV=[1,_gl,new T(function(){return E(E(E(E(_uO)[3])[2])[1]);})],_uW=function(_uX,_uY){while(1){var _uZ=B((function(_v0,_v1){var _v2=E(_v0);if(!_v2[0]){return _v1;}else{var _v3=_v2[1],_v4=E(_v1),_v5=E(_v4[3]),_v6=new T(function(){var _v7=E(B(_c9(E(E(E(E(_v5[3])[3])[3])[2])[1],_,_v4[2],_v5,_))),_v8=new T(function(){var _v9=E(_v7[3]),_va=new T(function(){var _vb=E(_v9[3]),_vc=new T(function(){var _vd=E(_vb[2])[1],_ve=new T(function(){var _vf=new T(function(){var _vg=B(_bh(function(_vh){var _vi=E(_vh);if(!B(_9M(_vi[1],_v3))){return false;}else{return new F(function(){return _9M(_vi[3],_v3);});}},_vd));if(!_vg[0]){return E(_ld);}else{if(!E(_vg[2])[0]){return E(E(_vg[1])[2]);}else{return E(_ld);}}}),_vj=new T(function(){return B(_uQ(_v3));}),_vk=function(_vl){var _vm=E(_vl);if(!_vm[0]){return [0];}else{var _vn=E(_vm[1]),_vo=_vn[1],_vp=_vn[2],_vq=new T(function(){return B(_vk(_vm[2]));});if(!B(_f(_vo,_v3))){if(!B(_9M(_vn[3],_v3))){return E(_vq);}else{var _vr=function(_vs){while(1){var _vt=B((function(_vu){var _vv=E(_vu);if(!_vv[0]){return E(_vq);}else{var _vw=_vv[2],_vx=E(_vv[1]),_vy=_vx[2],_vz=_vx[3];if(!B(_9M(_vx[1],_v3))){_vs=_vw;return null;}else{if(!B(_f(_vz,_v3))){return [1,new T(function(){if(!E(_vj)){return [0,_vo,[3,_vp,_vy],_vz];}else{return [0,_vo,[3,[3,_vp,[5,_vf]],_vy],_vz];}}),new T(function(){return B(_vr(_vw));})];}else{_vs=_vw;return null;}}}})(_vs));if(_vt!=null){return _vt;}}};return new F(function(){return _vr(_vd);});}}else{return E(_vq);}}};return B(_vk(_vd));}),_vA=function(_vB){while(1){var _vC=B((function(_vD){var _vE=E(_vD);if(!_vE[0]){return E(_ve);}else{var _vF=_vE[2],_vG=E(_vE[1]);if(!B(_f(_vG[1],_v3))){if(!B(_f(_vG[3],_v3))){return [1,_vG,new T(function(){return B(_vA(_vF));})];}else{_vB=_vF;return null;}}else{_vB=_vF;return null;}}})(_vB));if(_vC!=null){return _vC;}}};return B(_vA(_vd));});return [1,_,[0,_vc],_vb[3]];});return [1,_,_v9[2],_va];});return [1,_,_v7[2],_v8];});_uX=_v2[2];_uY=_v6;return null;}})(_uX,_uY));if(_uZ!=null){return _uZ;}}},_vH=new T(function(){var _vI=new T(function(){return B(_6v(_hA,_uP));}),_vJ=function(_vK){var _vL=E(_vK);return (_vL[0]==0)?E(_vI):[1,[0,_vL[1],_fR,_gl],new T(function(){return B(_vJ(_vL[2]));})];};return B(_vJ(E(_uL[2])[1]));}),_vM=E(B(_uW(B(_g3(_s,_uV,[1,_uU,_gm])),[1,_,_gn,[1,_,[0,_uU],[1,_,[0,_vH],[1,_,[0,new T(function(){return E(E(E(_uO)[2])[1]);})],[1,_,[0,_uV],_0]]]]]))),_vN=E(_vM[3]),_vO=B(_c9(E(E(E(E(_vN[3])[3])[3])[2])[1],_,_vM[2],_vN,_));if(!B(_uQ(new T(function(){return E(E(E(E(_vO)[3])[2])[1]);})))){var _vP=E(E(E(E(E(_vO)[3])[3])[2])[1]);if(!_vP[0]){return B(_gB(_));}else{if(!E(_vP[2])[0]){return B(_A(B(_91(B(_aH(E(_vP[1])[2])))),_hq));}else{return B(_gB(_));}}}else{var _vQ=E(E(_vO)[3]),_vR=_vQ[2],_vS=E(E(_vQ[3])[2]),_vT=new T(function(){var _vU=B(_bh(function(_vV){return (!B(_f(E(_vV)[3],E(_vR)[1])))?true:false;},E(_vS)[1]));if(!_vU[0]){return E(_mi);}else{if(!E(_vU[2])[0]){return E(E(_vU[1])[2]);}else{return E(_mi);}}}),_vW=new T(function(){var _vX=B(_bh(function(_vY){var _vZ=E(_vY),_w0=E(_vR)[1];if(!B(_9M(_vZ[1],_w0))){return false;}else{return new F(function(){return _9M(_vZ[3],_w0);});}},E(_vS)[1]));if(!_vX[0]){return E(_lg);}else{if(!E(_vX[2])[0]){return E(E(_vX[1])[2]);}else{return E(_lg);}}});return B(_A(B(_91(B(_aQ([5,_vW],_vT)))),_hq));}});return B(unAppCStr("<div class=\"alert alert-warning alert-dismissible\" role=\"alert\"><button type=\"button\" class=\"close\" data-dismiss=\"alert\" aria-label=\"Close\"><span aria-hidden=\"true\">&times;</span></button><strong>RegExp:</strong> ",_uK));});return new F(function(){return A(_ni,[_4u,_gk,function(_w1,_){var _w2=E(_hp)(E(_w1),toJSStr(E(_hS)),toJSStr(E(_uJ)));return new F(function(){return _3O(_);});},_]);});},_w3=function(_w4,_){return new F(function(){return _uH(_);});},_w5=function(_w6){return new F(function(){return _mN(_4v,_3T,_3M,_w6,_fQ,_w3);});},_w7=B(A(_ni,[_4u,_gh,function(_w8,_){var _w9=rMV(_nF),_wa=E(_hp)(E(_w8),toJSStr(E(_hS)),toJSStr(E(_mw))),_wb=B(A(_ni,[_4u,_gi,_uF,_]));return new F(function(){return A(_ni,[_4u,_gj,_w5,_]);});},_]));return _3N;},_wc=function(_wd){return new F(function(){return _gz("Main.hs:470:7-93|Right auto");});},_we=new T(function(){var _wf=jsParseJSON(toJSStr(E(B(_jk(_lC,0))[3])));if(!_wf[0]){return B(_wc(_));}else{var _wg=E(_wf[1]);if(_wg[0]==4){var _wh=E(_wg[1]);if(!_wh[0]){return E(_8l);}else{var _wi=B(_7f(_6g,E(_wh[1])[2]));if(!_wi[0]){return B(_wc(_));}else{var _wj=E(_wh[2]);if(!_wj[0]){return E(_8l);}else{var _wk=E(E(_wj[1])[2]);if(_wk[0]==1){var _wl=E(_wj[2]);if(!_wl[0]){return E(_8l);}else{var _wm=B(_5O(_7q,_6g,_7q,E(_wl[1])[2]));if(!_wm[0]){return B(_wc(_));}else{var _wn=E(_wl[2]);if(!_wn[0]){return E(_8l);}else{var _wo=E(E(_wn[1])[2]);if(_wo[0]==1){var _wp=E(_wn[2]);if(!_wp[0]){return E(_6m);}else{var _wq=B(_7f(_6g,E(_wp[1])[2]));if(!_wq[0]){return B(_wc(_));}else{if(!E(_wp[2])[0]){return [0,[1,_,[0,_wi[1]],[1,_,[0,new T(function(){return fromJSStr(_wk[1]);})],[1,_,[0,_wm[1]],[1,_,[0,new T(function(){return fromJSStr(_wo[1]);})],[1,_,[0,_wq[1]],_0]]]]]];}else{return E(_6j);}}}}else{return B(_wc(_));}}}}}else{return B(_wc(_));}}}}}else{return E(_8l);}}}),_wr=function(_){var _ws=nMV(_we);return new F(function(){return _nE(_ws,_);});},_wt=function(_){return new F(function(){return _wr(_);});};
var hasteMain = function() {B(A(_wt, [0]));};window.onload = hasteMain;