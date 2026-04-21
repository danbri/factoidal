(function(a){typeof
globalThis!=="object"&&(this?b():(a.defineProperty(a.prototype,"_T_",{configurable:true,get:b}),_T_));function
b(){var
b=this||self;b.globalThis=b;delete
a.prototype._T_}}(Object));($=>async a=>{"use strict";const{link:k,src:Y,generated:M,disable_effects:J}=a,h=globalThis.process?.versions?.node,U={cos:Math.cos,sin:Math.sin,tan:Math.tan,acos:Math.acos,asin:Math.asin,atan:Math.atan,cosh:Math.cosh,sinh:Math.sinh,tanh:Math.tanh,acosh:Math.acosh,asinh:Math.asinh,atanh:Math.atanh,cbrt:Math.cbrt,exp:Math.exp,expm1:Math.expm1,log:Math.log,log1p:Math.log1p,log2:Math.log2,log10:Math.log10,atan2:Math.atan2,hypot:Math.hypot,pow:Math.pow,fmod:(a,b)=>a%b},z=[Float32Array,Float64Array,Int8Array,Uint8Array,Int16Array,Uint16Array,Int32Array,Int32Array,Int32Array,Int32Array,Float32Array,Float64Array,Uint8Array,Uint16Array,Uint8ClampedArray],f=h&&require("node:fs"),b=f?.constants,A=f?[b.R_OK,b.W_OK,b.X_OK,b.F_OK]:[],V=f?[b.O_RDONLY,b.O_WRONLY,b.O_RDWR,b.O_APPEND,b.O_CREAT,b.O_TRUNC,b.O_EXCL,b.O_NONBLOCK,b.O_NOCTTY,b.O_DSYNC,b.O_SYNC]:[];var
e={map:new
WeakMap(),set:new
Set(),finalization:new
FinalizationRegistry(a=>e.set.delete(a))};function
X(a){const
b=new
WeakRef(a);e.map.set(a,b);e.set.add(b);e.finalization.register(a,b,a)}function
Z(a){const
b=e.map.get(a);if(b){e.map.delete(a);e.set.delete(b);e.finalization.unregister(a)}}function
I(){return[...e.set].map(a=>a.deref()).filter(a=>a)}var
y;function
T(a){return WebAssembly?.Suspending?new
WebAssembly.Suspending(a):a}function
v(a){return!J&&WebAssembly?.promising&&a?WebAssembly.promising(a):a}const
o=new
TextDecoder("utf-8",{ignoreBOM:1}),K=new
TextEncoder();function
N(a,b){b=Math.imul(b,0xcc9e2d51|0);b=b<<15|b>>>17;b=Math.imul(b,0x1b873593);a^=b;a=a<<13|a>>>19;return(a+(a<<2)|0)+(0xe6546b64|0)|0}function
O(a,b){for(var
c=0;c<b.length;c++)a=N(a,b.charCodeAt(c));return a^b.length}function
u(a){if(h&&globalThis.process.env[a]!==undefined)return globalThis.process.env[a];return globalThis.jsoo_env?.[a]}let
l=0;for(const
a
of
u("OCAMLRUNPARAM")?.split(",")||[]){if(a==="b")l=1;if(a.startsWith("b="))l=+a.slice(2)?1:0}function
n(a,b){var
c;if(a.isFile())c=0;else if(a.isDirectory())c=1;else if(a.isCharacterDevice())c=2;else if(a.isBlockDevice())c=3;else if(a.isSymbolicLink())c=4;else if(a.isFIFO())c=5;else if(a.isSocket())c=6;return E(b,a.dev,a.ino|0,c,a.mode,a.nlink,a.uid,a.gid,a.rdev,BigInt(a.size),a.atimeMs/1000,a.mtimeMs/1000,a.ctimeMs/1000)}const
w=h&&globalThis.process.platform==="win32",d=Function.prototype.call,c=DataView.prototype,B={jstag:WebAssembly.JSTag||new
WebAssembly.Tag({parameters:["externref"],results:[]}),identity:a=>a,from_bool:a=>!!a,get:(a,b)=>a[b],set:(a,b,c)=>a[b]=c,delete:(a,b)=>delete
a[b],instanceof:(a,b)=>a
instanceof
b,typeof:a=>typeof
a,equals:(a,b)=>a==b,strict_equals:(a,b)=>a===b,fun_call:(a,b,c)=>a.apply(b,c),meth_call:(a,b,c)=>a[b].apply(a,c),new_array:a=>new
Array(a),new_obj:()=>({}),new:(a,b)=>new
a(...b),global_this:globalThis,iter_props:(a,b)=>{for(var
c
in
a)if(Object.hasOwn(a,c))b(c)},array_length:a=>a.length,array_get:(a,b)=>a[b],array_set:(a,b,c)=>a[b]=c,read_string:a=>o.decode(new
Uint8Array(j,0,a)),read_string_stream:(a,b)=>o.decode(new
Uint8Array(j,0,a),{stream:b}),append_string:(a,b)=>a+b,write_string:a=>{var
c=0,b=a.length;for(;;){const{read:d,written:e}=K.encodeInto(a.slice(c),W);b-=d;if(!b)return e;G(e);c+=d}},ta_create:(a,b)=>new
z[a](b),ta_normalize:a=>a
instanceof
Uint32Array?new
Int32Array(a.buffer,a.byteOffset,a.length):a,ta_kind:b=>z.findIndex(a=>b
instanceof
a),ta_length:a=>a.length,ta_get_i32:(a,b)=>a[b],ta_fill:(a,b)=>a.fill(b),ta_blit:(a,b)=>b.set(a),ta_subarray:(a,b,c)=>a.subarray(b,c),ta_set:(a,b,c)=>a.set(b,c),ta_new:a=>new
Uint8Array(a),ta_copy:(a,b,c,d)=>a.copyWithin(b,c,d),ta_bytes:a=>new
Uint8Array(a.buffer,a.byteOffset,a.length*a.BYTES_PER_ELEMENT),ta_blit_from_bytes:(a,b,c,d,e)=>{for(let
f=0;f<e;f++)c[d+f]=C(a,b+f)},ta_blit_to_bytes:(a,b,c,d,e)=>{for(let
f=0;f<e;f++)D(c,d+f,a[b+f])},dv_make:a=>new
DataView(a.buffer,a.byteOffset,a.byteLength),dv_get_f64:d.bind(c.getFloat64),dv_get_f32:d.bind(c.getFloat32),dv_get_i64:d.bind(c.getBigInt64),dv_get_i32:d.bind(c.getInt32),dv_get_i16:d.bind(c.getInt16),dv_get_ui16:d.bind(c.getUint16),dv_get_i8:d.bind(c.getInt8),dv_get_ui8:d.bind(c.getUint8),dv_set_f64:d.bind(c.setFloat64),dv_set_f32:d.bind(c.setFloat32),dv_set_i64:d.bind(c.setBigInt64),dv_set_i32:d.bind(c.setInt32),dv_set_i16:d.bind(c.setInt16),dv_set_i8:d.bind(c.setInt8),littleEndian:new
Uint8Array(new
Uint32Array([1]).buffer)[0],wrap_callback:b=>function(...a){if(a.length===0)a=[undefined];return g(b,a.length,a,1)},wrap_callback_args:b=>function(...a){return g(b,1,[a],0)},wrap_callback_strict:(c,b)=>function(...a){a.length=c;return g(b,c,a,0)},wrap_callback_unsafe:b=>function(...a){return g(b,a.length,a,2)},wrap_meth_callback:b=>function(...a){a.unshift(this);return g(b,a.length,a,1)},wrap_meth_callback_args:b=>function(...a){return g(b,2,[this,a],0)},wrap_meth_callback_strict:(c,b)=>function(...a){a.length=c;a.unshift(this);return g(b,a.length,a,0)},wrap_meth_callback_unsafe:b=>function(...a){a.unshift(this);return g(b,a.length,a,2)},wrap_fun_arguments:b=>function(...a){return b(a)},format_float:(a,b,c,d)=>{function
j(a,b){if(Math.abs(a)<1.0)return a.toFixed(b);else{var
c=Number.parseInt(a.toString().split("+")[1]);if(c>20){c-=20;a/=Math.pow(10,c);a+=new
Array(c+1).join("0");if(b>0)a=a+"."+new
Array(b+1).join("0");return a}else
return a.toFixed(b)}}switch(b){case
0:var
e=d.toExponential(a),f=e.length;if(e.charAt(f-3)==="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break;case
1:e=j(d,a);break;case
2:a=a?a:1;e=d.toExponential(a-1);var
i=e.indexOf("e"),h=+e.slice(i+1);if(h<-4||d>=1e21||d.toFixed(0).length>a){var
f=i-1;while(e.charAt(f)==="0")f--;if(e.charAt(f)===".")f--;e=e.slice(0,f+1)+e.slice(i);f=e.length;if(e.charAt(f-3)==="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break}else{var
g=a;if(h<0){g-=h+1;e=d.toFixed(g)}else
while(e=d.toFixed(g),e.length>a+1)g--;if(g){var
f=e.length-1;while(e.charAt(f)==="0")f--;if(e.charAt(f)===".")f--;e=e.slice(0,f+1)}}break}return c?" "+e:e},gettimeofday:()=>new
Date().getTime()/1000,times:()=>{if(globalThis.process?.cpuUsage){var
a=globalThis.process.cpuUsage();return q(a.user/1e6,a.system/1e6)}else{var
a=performance.now()/1000;return q(a,0)}},gmtime:a=>{var
b=new
Date(a*1000),c=b.getTime(),e=new
Date(Date.UTC(b.getUTCFullYear(),0,1)).getTime(),d=Math.floor((c-e)/86400000);return r(b.getUTCSeconds(),b.getUTCMinutes(),b.getUTCHours(),b.getUTCDate(),b.getUTCMonth(),b.getUTCFullYear()-1900,b.getUTCDay(),d,false)},localtime:a=>{var
b=new
Date(a*1000),c=b.getTime(),f=new
Date(b.getFullYear(),0,1).getTime(),d=Math.floor((c-f)/86400000),e=new
Date(b.getFullYear(),0,1),g=new
Date(b.getFullYear(),6,1),h=Math.max(e.getTimezoneOffset(),g.getTimezoneOffset());return r(b.getSeconds(),b.getMinutes(),b.getHours(),b.getDate(),b.getMonth(),b.getFullYear()-1900,b.getDay(),d,b.getTimezoneOffset()<h)},mktime:(a,b,c,d,e,f)=>new
Date(a,b,c,d,e,f).getTime(),random_seed:()=>crypto.getRandomValues(new
Int32Array(12)),access:(a,d)=>f.accessSync(a,A.reduce((a,b,c)=>d&1<<c?a|b:a,0)),open:(a,d,c)=>f.openSync(a,V.reduce((a,b,c)=>d&1<<c?a|b:a,0),c),close:a=>f.closeSync(a),write:(a,b,c,d,e)=>f?f.writeSync(a,b,c,d,e===null?e:Number(e)):(console[a===2?"error":"log"](typeof
b==="string"?b:o.decode(b.slice(c,c+d))),d),read:(a,b,c,d,e)=>f.readSync(a,b,c,d,e),fsync:a=>f.fsyncSync(a),file_size:a=>f.fstatSync(a,{bigint:true}).size,register_channel:X,unregister_channel:Z,channel_list:I,exit:a=>h&&globalThis.process.exit(a),argv:()=>h?globalThis.process.argv.slice(1):["a.out"],on_windows:+w,getenv:u,backtrace_status:()=>l,record_backtrace:a=>l=a,system:a=>{var
b=require("node:child_process").spawnSync(a,{shell:true,stdio:"inherit"});if(b.error)throw b.error;return b.signal?255:b.status},isatty:a=>+require("node:tty").isatty(a),time:()=>performance.now(),getcwd:()=>h?globalThis.process.cwd():"/static",chdir:a=>globalThis.process.chdir(a),mkdir:(a,b)=>f.mkdirSync(a,b),rmdir:a=>f.rmdirSync(a),link:(a,b)=>f.linkSync(a,b),symlink:(a,b,c)=>f.symlinkSync(a,b,[null,"file","dir"][c]),readlink:a=>f.readlinkSync(a),unlink:a=>f.unlinkSync(a),read_dir:a=>f.readdirSync(a),opendir:a=>f.opendirSync(a),readdir:a=>{var
b=a.readSync()?.name;return b===undefined?null:b},closedir:a=>a.closeSync(),stat:(a,b)=>n(f.statSync(a),b),lstat:(a,b)=>n(f.lstatSync(a),b),fstat:(a,b)=>n(f.fstatSync(a),b),chmod:(a,b)=>f.chmodSync(a,b),fchmod:(a,b)=>f.fchmodSync(a,b),file_exists:a=>+f.existsSync(a),is_directory:a=>+f.lstatSync(a).isDirectory(),is_file:a=>+f.lstatSync(a).isFile(),utimes:(a,b,c)=>f.utimesSync(a,b,c),truncate:(a,b)=>f.truncateSync(a,b),ftruncate:(a,b)=>f.ftruncateSync(a,b),rename:(a,b)=>{var
c;if(w&&(c=f.statSync(b,{throwIfNoEntry:false}))&&f.statSync(a,{throwIfNoEntry:false})?.isDirectory())if(c.isDirectory()){if(!b.startsWith(a))try{f.rmdirSync(b)}catch{}}else{var
d=new
Error(`ENOTDIR: not a directory, rename '${a}' -> '${b}'`);throw Object.assign(d,{errno:-20,code:"ENOTDIR",syscall:"rename",path:b})}f.renameSync(a,b)},tmpdir:()=>require("node:os").tmpdir(),start_fiber:a=>y(a),suspend_fiber:T((c,b)=>new
Promise(a=>c(a,b))),resume_fiber:(a,b)=>a(b),weak_new:a=>new
WeakRef(a),weak_deref:a=>{var
b=a.deref();return b===undefined?null:b},weak_map_new:()=>new
WeakMap(),map_new:()=>new
Map(),map_get:(a,b)=>{var
c=a.get(b);return c===undefined?null:c},map_set:(a,b,c)=>a.set(b,c),map_delete:(a,b)=>a.delete(b),hash_string:O,log:a=>console.log(a)},p={test:a=>+(typeof
a==="string"),compare:(a,b)=>a<b?-1:+(a>b),decodeStringFromUTF8Array:()=>"",encodeStringToUTF8Array:()=>0,fromCharCodeArray:()=>""},i=Object.assign({Math:U,bindings:B,js:$,"wasm:js-string":p,"wasm:text-decoder":p,"wasm:text-encoder":p,str:new
globalThis.Proxy({},{get(a,b){return b}}),env:{}},M),x={builtins:["js-string","text-decoder","text-encoder"],importedStringConstants:"str"};function
S(a){const
b=require("node:path"),c=b.join(b.dirname(require.main.filename),a);return require("node:fs/promises").readFile(c)}const
t=globalThis?.document?.currentScript?.src;function
L(a){const
b=t?new
URL(a,t):a;return fetch(b)}const
R=h?S:L;async function
Q(a){return h?WebAssembly.instantiate(await
a,i,x):WebAssembly.instantiateStreaming(a,i,x)}async function
P(){i.OCaml={};const
c=[];async function
b(a,b){const
f=a[1].constructor!==Array;async function
e(){const
d=R(Y+"/"+a[0]+".wasm");await
Promise.all(f?c:a[1].map(a=>c[a]));const
e=await
Q(d);Object.assign(b?i.env:i.OCaml,e.instance.exports)}const
d=e();c.push(d);return d}async function
a(a){for(const
c
of
a)await
b(c)}await
b(k[0],1);if(k.length>1){await
b(k[1]);const
c=new
Array(20).fill(k.slice(2).values()).map(a);await
Promise.all(c)}return{instance:{exports:Object.assign(i.env,i.OCaml)}}}const
_=await
P();var{caml_callback:g,caml_alloc_times:q,caml_alloc_tm:r,caml_alloc_stat:E,caml_start_fiber:H,caml_handle_uncaught_exception:s,caml_buffer:F,caml_extract_bytes:G,bytes_get:C,bytes_set:D,_initialize:m}=_.instance.exports,j=F?.buffer,W=j&&new
Uint8Array(j,0,j.length);y=v(H);var
m=v(m);if(globalThis.process?.on)globalThis.process.on("uncaughtException",(a,b)=>s(a));else if(globalThis.addEventListener)globalThis.addEventListener("error",a=>a.error&&s(a.error));await
m()})(function(a){"use strict";var
ai=a;function
n(a){return a>=0?a:-BigInt(a)}function
f(a){return a==BigInt.asIntN(31,a)?Number(a):a}function
o(a,b){return f(BigInt(a)+BigInt(b))}var
v="0",T=1000,j="-",l="",C="+",h=function(J){"use strict";var
m=1e7,i=m,ak=7,w=9007199254740992,M=s(w),W="0123456789abcdefghijklmnopqrstuvwxyz",b=ai.BigInt,I=typeof
b==="function";function
f(a,b,c,d){if(typeof
a==="undefined")return f[0];if(typeof
b!=="undefined")return+b===10&&!c?g(a):ao(a,b,c,d);return g(a)}var
K="_z";function
d(a,b){this.value=a;this.sign=b;this.isSmall=false;this.caml_custom=K}d.prototype=Object.create(f.prototype);function
e(a){this.value=a;this.sign=a<0;this.isSmall=true;this.caml_custom=K}e.prototype=Object.create(f.prototype);function
c(a){this.value=a;this.caml_custom=K}c.prototype=Object.create(f.prototype);function
r(a){return-w<a&&a<w}function
s(a){if(a<m)return[a];var
b=1e14;if(a<b)return[a%m,Math.floor(a/m)];return[a%m,Math.floor(a/m)%m,Math.floor(a/b)]}function
n(a){t(a);var
b=a.length;if(b<4&&o(a,M)<0)switch(b){case
0:return 0;case
1:return a[0];case
2:return a[0]+a[1]*i;default:return a[0]+(a[1]+a[2]*i)*i}return a}function
t(a){var
b=a.length;while(a[--b]===0);a.length=b+1}function
E(a){var
c=new
Array(a),b=-1;while(++b<a)c[b]=0;return c}function
u(a){if(a>0)return Math.floor(a);return Math.ceil(a)}function
X(a,b){var
h=a.length,j=b.length,g=new
Array(h),d=0,f=i,e,c;for(c=0;c<j;c++){e=a[c]+b[c]+d;d=e>=f?1:0;g[c]=e-d*f}while(c<h){e=a[c]+d;d=e===f?1:0;g[c++]=e-d*f}if(d>0)g.push(d);return g}function
x(a,b){if(a.length>=b.length)return X(a,b);return X(b,a)}function
D(a,b){var
g=a.length,e=new
Array(g),d=i,f,c;for(c=0;c<g;c++){f=a[c]-d+b;b=Math.floor(f/d);e[c]=f-b*d;b+=1}while(b>0){e[c++]=b%d;b=Math.floor(b/d)}return e}d.prototype.add=function(a){var
b=g(a);if(this.sign!==b.sign)return this.subtract(b.negate());var
c=this.value,e=b.value;if(b.isSmall)return new
d(D(c,Math.abs(e)),this.sign);return new
d(x(c,e),this.sign)};d.prototype.plus=d.prototype.add;e.prototype.add=function(a){var
f=g(a),b=this.value;if(b<0!==f.sign)return this.subtract(f.negate());var
c=f.value;if(f.isSmall){if(r(b+c))return new
e(b+c);c=s(Math.abs(c))}return new
d(D(c,Math.abs(b)),b<0)};e.prototype.plus=e.prototype.add;c.prototype.add=function(a){return new
c(this.value+g(a).value)};c.prototype.plus=c.prototype.add;function
A(a,b){var
g=a.length,h=b.length,e=new
Array(g),f=0,j=i,c,d;for(c=0;c<h;c++){d=a[c]-f-b[c];if(d<0){d+=j;f=1}else
f=0;e[c]=d}for(c=h;c<g;c++){d=a[c]-f;if(d<0)d+=j;else{e[c++]=d;break}e[c]=d}for(;c<g;c++)e[c]=a[c];t(e);return e}function
as(a,b,c){var
f;if(o(a,b)>=0)f=A(a,b);else{f=A(b,a);c=!c}f=n(f);if(typeof
f==="number"){if(c)f=-f;return new
e(f)}return new
d(f,c)}function
H(a,b,c){var
l=a.length,f=new
Array(l),k=-b,j=i,h,g;for(h=0;h<l;h++){g=a[h]+k;k=Math.floor(g/j);g%=j;f[h]=g<0?g+j:g}f=n(f);if(typeof
f==="number"){if(c)f=-f;return new
e(f)}return new
d(f,c)}d.prototype.subtract=function(a){var
b=g(a);if(this.sign!==b.sign)return this.add(b.negate());var
c=this.value,d=b.value;if(b.isSmall)return H(c,Math.abs(d),this.sign);return as(c,d,this.sign)};d.prototype.minus=d.prototype.subtract;e.prototype.subtract=function(a){var
c=g(a),b=this.value;if(b<0!==c.sign)return this.add(c.negate());var
d=c.value;if(c.isSmall)return new
e(b-d);return H(d,Math.abs(b),b>=0)};e.prototype.minus=e.prototype.subtract;c.prototype.subtract=function(a){return new
c(this.value-g(a).value)};c.prototype.minus=c.prototype.subtract;d.prototype.negate=function(){return new
d(this.value,!this.sign)};e.prototype.negate=function(){var
b=this.sign,a=new
e(-this.value);a.sign=!b;return a};c.prototype.negate=function(){return new
c(-this.value)};d.prototype.abs=function(){return new
d(this.value,false)};e.prototype.abs=function(){return new
e(Math.abs(this.value))};c.prototype.abs=function(){return new
c(this.value>=0?this.value:-this.value)};function
Q(a,b){var
j=a.length,l=b.length,n=j+l,e=E(n),m=i,g,f,c,h,k;for(c=0;c<j;++c){h=a[c];for(var
d=0;d<l;++d){k=b[d];g=h*k+e[c+d];f=Math.floor(g/m);e[c+d]=g-f*m;e[c+d+1]+=f}}t(e);return e}function
y(a,b){var
h=a.length,g=new
Array(h),e=i,c=0,f,d;for(d=0;d<h;d++){f=a[d]*b+c;c=Math.floor(f/e);g[d]=f-c*e}while(c>0){g[d++]=c%e;c=Math.floor(c/e)}return g}function
ae(a,b){var
c=[];while(b--
>0)c.push(0);return c.concat(a)}function
F(a,b){var
c=Math.max(a.length,b.length);if(c<=30)return Q(a,b);c=Math.ceil(c/2);var
f=a.slice(c),d=a.slice(0,c),i=b.slice(c),h=b.slice(0,c),e=F(d,h),g=F(f,i),k=F(x(d,f),x(h,i)),j=x(x(e,ae(A(A(k,e),g),c)),ae(g,2*c));t(j);return j}function
at(a,b){var
c=0.012;return-c*a-c*b+0.000015*a*b>0}d.prototype.multiply=function(a){var
h=g(a),c=this.value,b=h.value,j=this.sign!==h.sign,e;if(h.isSmall){if(b===0)return f[0];if(b===1)return this;if(b===-1)return this.negate();e=Math.abs(b);if(e<i)return new
d(y(c,e),j);b=s(e)}if(at(c.length,b.length))return new
d(F(c,b),j);return new
d(Q(c,b),j)};d.prototype.times=d.prototype.multiply;function
ab(a,b,c){if(a<i)return new
d(y(b,a),c);return new
d(Q(b,s(a)),c)}e.prototype._multiplyBySmall=function(a){if(r(a.value*this.value))return new
e(a.value*this.value);return ab(Math.abs(a.value),s(Math.abs(this.value)),this.sign!==a.sign)};d.prototype._multiplyBySmall=function(a){if(a.value===0)return f[0];if(a.value===1)return this;if(a.value===-1)return this.negate();return ab(Math.abs(a.value),this.value,this.sign!==a.sign)};e.prototype.multiply=function(a){return g(a)._multiplyBySmall(this)};e.prototype.times=e.prototype.multiply;c.prototype.multiply=function(a){return new
c(this.value*g(a).value)};c.prototype.times=c.prototype.multiply;function
ag(a){var
e=a.length,f=E(e+e),k=i,h,c,b,g,j;for(b=0;b<e;b++){g=a[b];c=0-g*g;for(var
d=b;d<e;d++){j=a[d];h=2*(g*j)+f[b+d]+c;c=Math.floor(h/k);f[b+d]=h-c*k}f[b+e]=c}t(f);return f}d.prototype.square=function(){return new
d(ag(this.value),false)};e.prototype.square=function(){var
a=this.value*this.value;if(r(a))return new
e(a);return new
d(ag(s(Math.abs(this.value))),false)};c.prototype.square=function(a){return new
c(this.value*this.value)};function
al(a,b){var
r=a.length,j=b.length,h=i,s=E(b.length),m=b[j-1],p=Math.ceil(h/(2*m)),d=y(a,p),k=y(b,p),l,f,e,g,c,o,q;if(d.length<=r)d.push(0);k.push(0);m=k[j-1];for(f=r-j;f>=0;f--){l=h-1;if(d[f+j]!==m)l=Math.floor((d[f+j]*h+d[f+j-1])/m);e=0;g=0;o=k.length;for(c=0;c<o;c++){e+=l*k[c];q=Math.floor(e/h);g+=d[f+c]-(e-q*h);e=q;if(g<0){d[f+c]=g+h;g=-1}else{d[f+c]=g;g=0}}while(g!==0){l-=1;e=0;for(c=0;c<o;c++){e+=d[f+c]-h+k[c];if(e<0){d[f+c]=e+h;e=0}else{d[f+c]=e;e=1}}g+=e}s[f]=l}d=Y(d,p)[0];return[n(s),n(d)]}function
am(a,b){var
l=a.length,h=b.length,f=[],c=[],j=i,d,g,e,m,k;while(l){c.unshift(a[--l]);t(c);if(o(c,b)<0){f.push(0);continue}g=c.length;e=c[g-1]*j+c[g-2];m=b[h-1]*j+b[h-2];if(g>h)e=(e+1)*j;d=Math.ceil(e/m);do{k=y(b,d);if(o(k,c)<=0)break;d--}while(d);f.push(d);c=A(c,k)}f.reverse();return[n(f),n(c)]}function
Y(a,b){var
g=a.length,h=E(g),j=i,c,f,d,e;d=0;for(c=g-1;c>=0;--c){e=d*j+a[c];f=u(e/b);d=e-f*b;h[c]=f|0}return[h,d|0]}function
p(a,b){var
p,k=g(b);if(I)return[new
c(a.value/k.value),new
c(a.value%k.value)];var
m=a.value,j=k.value,h;if(j===0)throw new
Error("Cannot divide by zero");if(a.isSmall){if(k.isSmall)return[new
e(u(m/j)),new
e(m%j)];return[f[0],a]}if(k.isSmall){if(j===1)return[a,f[0]];if(j==-1)return[a.negate(),f[0]];var
r=Math.abs(j);if(r<i){p=Y(m,r);h=n(p[0]);var
q=p[1];if(a.sign)q=-q;if(typeof
h==="number"){if(a.sign!==k.sign)h=-h;return[new
e(h),new
e(q)]}return[new
d(h,a.sign!==k.sign),new
e(q)]}j=s(r)}var
t=o(m,j);if(t===-1)return[f[0],a];if(t===0)return[f[a.sign===k.sign?1:-1],f[0]];if(m.length+j.length<=200)p=al(m,j);else
p=am(m,j);h=p[0];var
w=a.sign!==k.sign,l=p[1],v=a.sign;if(typeof
h==="number"){if(w)h=-h;h=new
e(h)}else
h=new
d(h,w);if(typeof
l==="number"){if(v)l=-l;l=new
e(l)}else
l=new
d(l,v);return[h,l]}d.prototype.divmod=function(a){var
b=p(this,a);return{quotient:b[0],remainder:b[1]}};c.prototype.divmod=e.prototype.divmod=d.prototype.divmod;d.prototype.divide=function(a){return p(this,a)[0]};c.prototype.over=c.prototype.divide=function(a){return new
c(this.value/g(a).value)};e.prototype.over=e.prototype.divide=d.prototype.over=d.prototype.divide;d.prototype.mod=function(a){return p(this,a)[1]};c.prototype.mod=c.prototype.remainder=function(a){return new
c(this.value%g(a).value)};e.prototype.remainder=e.prototype.mod=d.prototype.remainder=d.prototype.mod;d.prototype.pow=function(a){var
c=g(a),d=this.value,b=c.value,j,h,i;if(b===0)return f[1];if(d===0)return f[0];if(d===1)return f[1];if(d===-1)return c.isEven()?f[1]:f[-1];if(c.sign)return f[0];if(!c.isSmall)throw new
Error("The exponent "+c.toString()+" is too large.");if(this.isSmall)if(r(j=Math.pow(d,b)))return new
e(u(j));h=this;i=f[1];while(true){if(b&1===1){i=i.times(h);--b}if(b===0)break;b/=2;h=h.square()}return i};e.prototype.pow=d.prototype.pow;c.prototype.pow=function(a){var
j=g(a),i=this.value,d=j.value,e=b(0),h=b(1),m=b(2);if(d===e)return f[1];if(i===e)return f[0];if(i===h)return f[1];if(i===b(-1))return j.isEven()?f[1]:f[-1];if(j.isNegative())return new
c(e);var
k=this,l=f[1];while(true){if((d&h)===h){l=l.times(k);--d}if(d===e)break;d/=m;k=k.square()}return l};d.prototype.modPow=function(a,b){a=g(a);b=g(b);if(b.isZero())throw new
Error("Cannot take modPow with modulus 0");var
d=f[1],c=this.mod(b);if(a.isNegative()){a=a.multiply(f[-1]);c=c.modInv(b)}while(a.isPositive()){if(c.isZero())return f[0];if(a.isOdd())d=d.multiply(c).mod(b);a=a.divide(2);c=c.square().mod(b)}return d};c.prototype.modPow=e.prototype.modPow=d.prototype.modPow;function
o(a,b){if(a.length!==b.length)return a.length>b.length?1:-1;for(var
c=a.length-1;c>=0;c--)if(a[c]!==b[c])return a[c]>b[c]?1:-1;return 0}d.prototype.compareAbs=function(a){var
b=g(a),c=this.value,d=b.value;if(b.isSmall)return 1;return o(c,d)};e.prototype.compareAbs=function(a){var
d=g(a),c=Math.abs(this.value),b=d.value;if(d.isSmall){b=Math.abs(b);return c===b?0:c>b?1:-1}return-1};c.prototype.compareAbs=function(a){var
b=this.value,c=g(a).value;b=b>=0?b:-b;c=c>=0?c:-c;return b===c?0:b>c?1:-1};d.prototype.compare=function(a){if(a===Infinity)return-1;if(a===-Infinity)return 1;var
b=g(a),c=this.value,d=b.value;if(this.sign!==b.sign)return b.sign?1:-1;if(b.isSmall)return this.sign?-1:1;return o(c,d)*(this.sign?-1:1)};d.prototype.compareTo=d.prototype.compare;e.prototype.compare=function(a){if(a===Infinity)return-1;if(a===-Infinity)return 1;var
c=g(a),b=this.value,d=c.value;if(c.isSmall)return b==d?0:b>d?1:-1;if(b<0!==c.sign)return b<0?-1:1;return b<0?1:-1};e.prototype.compareTo=e.prototype.compare;c.prototype.compare=function(a){if(a===Infinity)return-1;if(a===-Infinity)return 1;var
b=this.value,c=g(a).value;return b===c?0:b>c?1:-1};c.prototype.compareTo=c.prototype.compare;d.prototype.equals=function(a){return this.compare(a)===0};c.prototype.eq=c.prototype.equals=e.prototype.eq=e.prototype.equals=d.prototype.eq=d.prototype.equals;d.prototype.notEquals=function(a){return this.compare(a)!==0};c.prototype.neq=c.prototype.notEquals=e.prototype.neq=e.prototype.notEquals=d.prototype.neq=d.prototype.notEquals;d.prototype.greater=function(a){return this.compare(a)>0};c.prototype.gt=c.prototype.greater=e.prototype.gt=e.prototype.greater=d.prototype.gt=d.prototype.greater;d.prototype.lesser=function(a){return this.compare(a)<0};c.prototype.lt=c.prototype.lesser=e.prototype.lt=e.prototype.lesser=d.prototype.lt=d.prototype.lesser;d.prototype.greaterOrEquals=function(a){return this.compare(a)>=0};c.prototype.geq=c.prototype.greaterOrEquals=e.prototype.geq=e.prototype.greaterOrEquals=d.prototype.geq=d.prototype.greaterOrEquals;d.prototype.lesserOrEquals=function(a){return this.compare(a)<=0};c.prototype.leq=c.prototype.lesserOrEquals=e.prototype.leq=e.prototype.lesserOrEquals=d.prototype.leq=d.prototype.lesserOrEquals;d.prototype.isEven=function(){return(this.value[0]&1)===0};e.prototype.isEven=function(){return(this.value&1)===0};c.prototype.isEven=function(){return(this.value&b(1))===b(0)};d.prototype.isOdd=function(){return(this.value[0]&1)===1};e.prototype.isOdd=function(){return(this.value&1)===1};c.prototype.isOdd=function(){return(this.value&b(1))===b(1)};d.prototype.isPositive=function(){return!this.sign};e.prototype.isPositive=function(){return this.value>0};c.prototype.isPositive=e.prototype.isPositive;d.prototype.isNegative=function(){return this.sign};e.prototype.isNegative=function(){return this.value<0};c.prototype.isNegative=e.prototype.isNegative;d.prototype.isUnit=function(){return false};e.prototype.isUnit=function(){return Math.abs(this.value)===1};c.prototype.isUnit=function(){return this.abs().value===b(1)};d.prototype.isZero=function(){return false};e.prototype.isZero=function(){return this.value===0};c.prototype.isZero=function(){return this.value===b(0)};d.prototype.isDivisibleBy=function(a){var
b=g(a);if(b.isZero())return false;if(b.isUnit())return true;if(b.compareAbs(2)===0)return this.isEven();return this.mod(b).isZero()};c.prototype.isDivisibleBy=e.prototype.isDivisibleBy=d.prototype.isDivisibleBy;function
$(a){var
b=a.abs();if(b.isUnit())return false;if(b.equals(2)||b.equals(3)||b.equals(5))return true;if(b.isEven()||b.isDivisibleBy(3)||b.isDivisibleBy(5))return false;if(b.lesser(49))return true}function
O(a,b){var
g=a.prev(),e=g,i=0,f,j,d,c;while(e.isEven())e=e.divide(2),i++;a:for(d=0;d<b.length;d++){if(a.lesser(b[d]))continue;c=h(b[d]).modPow(e,a);if(c.isUnit()||c.equals(g))continue;for(f=i-1;f!=0;f--){c=c.square().mod(a);if(c.isUnit())return false;if(c.equals(g))continue a}return false}return true}d.prototype.isPrime=function(a){var
f=$(this);if(f!==J)return f;var
c=this.abs(),e=c.bitLength();if(e<=64)return O(c,[2,3,5,7,11,13,17,19,23,29,31,37]);var
g=Math.log(2)*e.toJSNumber(),i=Math.ceil(a===true?2*Math.pow(g,2):g);for(var
d=[],b=0;b<i;b++)d.push(h(b+2));return O(c,d)};c.prototype.isPrime=e.prototype.isPrime=d.prototype.isPrime;d.prototype.isProbablePrime=function(a){var
d=$(this);if(d!==J)return d;var
e=this.abs(),f=a===J?5:a;for(var
b=[],c=0;c<f;c++)b.push(h.randBetween(2,e.minus(2)));return O(e,b)};c.prototype.isProbablePrime=e.prototype.isProbablePrime=d.prototype.isProbablePrime;d.prototype.modInv=function(a){var
b=h.zero,e=h.one,d=g(a),c=this.abs(),f,j,i;while(!c.isZero()){f=d.divide(c);j=b;i=d;b=e;d=c;e=j.subtract(f.multiply(e));c=i.subtract(f.multiply(c))}if(!d.isUnit())throw new
Error(this.toString()+" and "+a.toString()+" are not co-prime");if(b.compare(0)===-1)b=b.add(a);if(this.isNegative())return b.negate();return b};c.prototype.modInv=e.prototype.modInv=d.prototype.modInv;d.prototype.next=function(){var
a=this.value;if(this.sign)return H(a,1,this.sign);return new
d(D(a,1),this.sign)};e.prototype.next=function(){var
a=this.value;if(a+1<w)return new
e(a+1);return new
d(M,false)};c.prototype.next=function(){return new
c(this.value+b(1))};d.prototype.prev=function(){var
a=this.value;if(this.sign)return new
d(D(a,1),true);return H(a,1,this.sign)};e.prototype.prev=function(){var
a=this.value;if(a-1>-w)return new
e(a-1);return new
d(M,true)};c.prototype.prev=function(){return new
c(this.value-b(1))};var
k=[1];while(2*k[k.length-1]<=i)k.push(2*k[k.length-1]);var
z=k.length,q=k[z-1];function
af(a){return Math.abs(a)<=i}var
R=" is too large for shifting.";d.prototype.shiftLeft=function(a){var
b=g(a).toJSNumber();if(!af(b))throw new
Error(String(b)+R);if(b<0)return this.shiftRight(-b);var
c=this;if(c.isZero())return c;while(b>=z){c=c.multiply(q);b-=z-1}return c.multiply(k[b])};c.prototype.shiftLeft=e.prototype.shiftLeft=d.prototype.shiftLeft;d.prototype.shiftRight=function(a){var
b,c=g(a).toJSNumber();if(!af(c))throw new
Error(String(c)+R);if(c<0)return this.shiftLeft(-c);var
d=this;while(c>=z){if(d.isZero()||d.isNegative()&&d.isUnit())return d;b=p(d,q);d=b[1].isNegative()?b[0].prev():b[0];c-=z-1}b=p(d,k[c]);return b[1].isNegative()?b[0].prev():b[0]};c.prototype.shiftRight=e.prototype.shiftRight=d.prototype.shiftRight;function
N(a,b,c){b=g(b);var
m=a.isNegative(),r=b.isNegative(),l=m?a.not():a,o=r?b.not():b,d=0,e=0,k=null,n=null,i=[];while(!l.isZero()||!o.isZero()){k=p(l,q);d=k[1].toJSNumber();if(m)d=q-1-d;n=p(o,q);e=n[1].toJSNumber();if(r)e=q-1-e;l=k[0];o=n[0];i.push(c(d,e))}var
j=c(m?1:0,r?1:0)!==0?h(-1):h(0);for(var
f=i.length-1;f>=0;f-=1)j=j.multiply(q).add(h(i[f]));return j}d.prototype.not=function(){return this.negate().prev()};c.prototype.not=e.prototype.not=d.prototype.not;d.prototype.and=function(a){return N(this,a,function(a,b){return a&b})};c.prototype.and=e.prototype.and=d.prototype.and;d.prototype.or=function(a){return N(this,a,function(a,b){return a|b})};c.prototype.or=e.prototype.or=d.prototype.or;d.prototype.xor=function(a){return N(this,a,function(a,b){return a^b})};c.prototype.xor=e.prototype.xor=d.prototype.xor;var
L=1<<30,aj=(i&-i)*(i&-i)|L;function
G(a){var
c=a.value,d=typeof
c==="number"?c|L:typeof
c==="bigint"?c|b(L):c[0]+c[1]*i|aj;return d&-d}function
_(a,b){if(b.compareTo(a)<=0){var
f=_(a,b.square(b)),d=f.p,c=f.e,e=d.multiply(b);return e.compareTo(a)<=0?{p:e,e:c*2+1}:{p:d,e:c*2}}return{p:h(1),e:0}}d.prototype.bitLength=function(){var
a=this;if(a.compareTo(h(0))<0)a=a.negate().subtract(h(1));if(a.compareTo(h(0))===0)return h(0);return h(_(a,h(2)).e).add(h(1))};c.prototype.bitLength=e.prototype.bitLength=d.prototype.bitLength;function
aa(a,b){a=g(a);b=g(b);return a.greater(b)?a:b}function
P(a,b){a=g(a);b=g(b);return a.lesser(b)?a:b}function
Z(a,b){a=g(a).abs();b=g(b).abs();if(a.equals(b))return a;if(a.isZero())return b;if(b.isZero())return a;var
c=f[1],d,e;while(a.isEven()&&b.isEven()){d=P(G(a),G(b));a=a.divide(d);b=b.divide(d);c=c.multiply(d)}while(a.isEven())a=a.divide(G(a));do{while(b.isEven())b=b.divide(G(b));if(a.greater(b)){e=b;b=a;a=e}b=b.subtract(a)}while(!b.isZero());return c.isUnit()?a:a.multiply(c)}function
an(a,b){a=g(a).abs();b=g(b).abs();return a.divide(Z(a,b)).multiply(b)}function
aq(a,b){a=g(a);b=g(b);var
d=P(a,b),n=aa(a,b),e=n.subtract(d).add(1);if(e.isSmall)return d.add(Math.floor(Math.random()*e));var
j=B(e,i).value,l=[],k=true;for(var
c=0;c<j.length;c++){var
m=k?j[c]:i,h=u(Math.random()*m);l.push(h);if(h<m)k=false}return d.add(f.fromArray(l,i,false))}var
S=">",V=".",U="<";function
ao(a,b,c,d){c=c||W;a=String(a);if(!d){a=a.toLowerCase();c=c.toLowerCase()}var
m=a.length,e,k=Math.abs(b),h={};for(e=0;e<c.length;e++)h[c[e]]=e;for(e=0;e<m;e++){var
f=a[e];if(f===j)continue;if(f
in
h)if(h[f]>=k){if(f==="1"&&k===1)continue;throw new
Error(f+" is not a valid digit in base "+b+V)}}b=g(b);var
i=[],l=a[0]===j;for(e=l?1:0;e<a.length;e++){var
f=a[e];if(f
in
h)i.push(g(h[f]));else if(f===U){var
n=e;do
e++;while(a[e]!==S&&e<a.length);i.push(g(a.slice(n+1,e)))}else
throw new
Error(f+" is not a valid character")}return ac(i,b,l)}function
ac(a,b,c){var
e=f[0],g=f[1],d;for(d=a.length-1;d>=0;d--){e=e.add(a[d].times(g));g=g.times(b)}return c?e.negate():e}function
ar(a,b){b=b||W;if(a<b.length)return b[a];return U+a+S}function
B(a,b){b=h(b);if(b.isZero()){if(a.isZero())return{value:[0],isNegative:false};throw new
Error("Cannot convert nonzero numbers to base 0.")}if(b.equals(-1)){if(a.isZero())return{value:[0],isNegative:false};if(a.isNegative())return{value:[].concat.apply([],Array.apply(null,Array(-a.toJSNumber())).map(Array.prototype.valueOf,[1,0])),isNegative:false};var
i=Array.apply(null,Array(a.toJSNumber()-1)).map(Array.prototype.valueOf,[0,1]);i.unshift([1]);return{value:[].concat.apply([],i),isNegative:false}}var
f=false;if(a.isNegative()&&b.isPositive()){f=true;a=a.abs()}if(b.isUnit()){if(a.isZero())return{value:[0],isNegative:false};return{value:Array.apply(null,Array(a.toJSNumber())).map(Number.prototype.valueOf,1),isNegative:f}}var
g=[],c=a,e;while(c.isNegative()||c.compareAbs(b)>=0){e=c.divmod(b);c=e.quotient;var
d=e.remainder;if(d.isNegative()){d=b.minus(d).abs();c=c.next()}g.push(d.toJSNumber())}g.push(c.toJSNumber());return{value:g.reverse(),isNegative:f}}function
ah(a,b,c){var
d=B(a,b);return(d.isNegative?j:l)+d.value.map(function(a){return ar(a,c)}).join(l)}d.prototype.toArray=function(a){return B(this,a)};e.prototype.toArray=function(a){return B(this,a)};c.prototype.toArray=function(a){return B(this,a)};d.prototype.toString=function(a,b){if(a===J)a=10;if(a!==10)return ah(this,a,b);var
e=this.value,d=e.length,f=String(e[--d]),h="0000000",c;while(--d>=0){c=String(e[d]);f+=h.slice(c.length)+c}var
g=this.sign?j:l;return g+f};e.prototype.toString=function(a,b){if(a===J)a=10;if(a!=10)return ah(this,a,b);return String(this.value)};c.prototype.toString=e.prototype.toString;c.prototype.toJSON=d.prototype.toJSON=e.prototype.toJSON=function(){return this.toString()};d.prototype.valueOf=function(){return parseInt(this.toString(),10)};d.prototype.toJSNumber=d.prototype.valueOf;e.prototype.valueOf=function(){return this.value};e.prototype.toJSNumber=e.prototype.valueOf;c.prototype.valueOf=c.prototype.toJSNumber=function(){return parseInt(this.toString(),10)};function
ad(a){var
i="Invalid integer: ";if(r(+a)){var
n=+a;if(n===u(n))return I?new
c(b(n)):new
e(n);throw new
Error(i+a)}var
q=a[0]===j;if(q)a=a.slice(1);var
h=a.split(/e/i);if(h.length>2)throw new
Error(i+h.join("e"));if(h.length===2){var
f=h[1];if(f[0]===C)f=f.slice(1);f=+f;if(f!==u(f)||!r(f))throw new
Error(i+f+" is not a valid exponent.");var
g=h[0],k=g.indexOf(V);if(k>=0){f-=g.length-k-1;g=g.slice(0,k)+g.slice(k+1)}if(f<0)throw new
Error("Cannot include negative exponent part for integers");g+=new
Array(f+1).join(v);a=g}var
s=/^([0-9][0-9]*)$/.test(a);if(!s)throw new
Error(i+a);if(I)return new
c(b(q?j+a:a));var
p=[],l=a.length,o=ak,m=l-o;while(l>0){p.push(+a.slice(m,l));m-=o;if(m<0)m=0;l-=o}t(p);return new
d(p,q)}function
ap(a){if(I)return new
c(b(a));if(r(a)){if(a!==u(a))throw new
Error(a+" is not an integer.");return new
e(a)}return ad(a.toString())}function
g(a){if(typeof
a==="number")return ap(a);if(typeof
a==="string")return ad(a);if(typeof
a==="bigint")return new
c(a);return a}for(var
a=0;a<T;a++){f[a]=g(a);if(a>0)f[-a]=g(-a)}f.one=f[1];f.zero=f[0];f.minusOne=f[-1];f.max=aa;f.min=P;f.gcd=Z;f.lcm=an;f.isInstance=function(a){return a
instanceof
d||a
instanceof
e||a
instanceof
c};f.randBetween=aq;f.fromArray=function(a,b,c){return ac(a.map(g),g(b||10),c)};return f}();function
g(a){throw a}var
b=[0];function
i(){g(b.Division_by_zero)}function
d(a){var
b=a.toJSNumber()|0;if(a.equals(h(b)))return b;return a}function
c(a,b){b=h(b);if(b.equals(h(0)))i();return d(h(a).divide(h(b)))}function
k(a,b){return d(h(a).add(h(b)))}function
p(a,b){if(a==0)return 0;if(a>0==b>0)if(BigInt(a)%BigInt(b)!=0)return k(c(a,b),1n);return c(a,b)}function
q(a,b){return(a>b)-(a<b)}function
r(a,b,c,d){var
f=0n;for(var
g=0;g<d/4;g++){var
e=BigInt(a(b));e|=BigInt(a(b))<<8n;e|=BigInt(a(b))<<16n;e|=BigInt(a(b))<<24n;f|=e<<BigInt(32*g)}if(c)f=-f;return f}function
m(a,b){return d(h(a).subtract(h(b)))}function
s(a,b){if(a==0)return 0;if(a>0!=b>0)if(BigInt(a)%BigInt(b)!=0)return m(c(a,b),1n);return c(a,b)}function
t(a,b){b=BigInt(b);var
h=10,o=0,k=0,g=0,n=0,i=l,m=" ",f=m,d=0,e=l;while(a[d]=="%")d++;for(;;d++)if(a[d]=="#")g=1;else if(a[d]==v)f=v;else if(a[d]==j)n=1;else if(a[d]==m||a[d]==C)i=a[d];else
break;if(b<0){i=j;b=-b}for(;a[d]>=v&&a[d]<="9";d++)k=10*k+
+a[d];switch(a[d]){case"i":case"d":case"u":break;case"b":h=2;if(g)e="0b";break;case"o":h=8;if(g)e="0o";break;case"x":h=16;if(g)e="0x";break;case"X":h=16;if(g)e="0X";o=1;break;default:return-1}if(n)f=m;var
c=b.toString(h);if(o===1)c=c.toUpperCase();var
q=c.length;if(f==m)if(n){c=i+e+c;for(;c.length<k;)c=c+f}else{c=i+e+c;for(;c.length<k;)c=f+c}else{var
p=i+e;for(;c.length+p.length<k;)c=f+c;c=p+c}return c}var
e=32n;function
u(a,b){b=BigInt(b);var
f=b<0;if(f)b=-b;var
d=0,c=0;while(b){d++;c=a(c,Number(BigInt.asIntN(32,b)));b>>=e}if(d&1)c=a(c,0);if(f)c++;return c}function
w(a,b){return f(BigInt(a)*BigInt(b))}function
x(a,b){if(a==0){a=10;var
c=0,k=1;if(b[c]==j){k=-1;c++}else if(b[c]==C)c++;if(b[c]==v){c++;if(b.length==c)return 0;else{var
e=b[c];if(e=="o"||e=="O")a=8;else if(e=="x"||e=="X")a=16;else if(e=="b"||e=="B")a=2;if(a!=10){b=b.substring(c+1);if(k==-1)b=j+b}}}}function
n(a){if(a>=48&&a<=57)return a-48;if(a>=97&&a<=102)return a-97+10;if(a>=65&&a<=70)return a-65+10;return T}var
i=false,d=0;if(b[d]==C)b=b.substring(1);else if(b[d]==j){i=true;d++}if(b[d]=="_")return null;b=b.replace(/_/g,l);if(b==j||b==l)b=v;var
g=0n,m=BigInt(a);for(;d<b.length;d++){var
h=n(b.charCodeAt(d));if(h>=a)return null;g=g*m+BigInt(h)}if(i)g=-g;return f(g)}function
y(a){return a>=0}function
z(a,b){return f(BigInt(a)%BigInt(b))}function
A(a,b,c){if(c<0)c=-c;do{var
d=Number(BigInt.asIntN(32,c));a(b,d);a(b,d>>>8);a(b,d>>>16);a(b,d>>>24);c>>=e}while(c)}function
B(a){if(a<0)a=-a;var
b=0,c=1n;while(c<=a){b+=1;c<<=e}return b}function
D(a,b){return f(BigInt(a)-BigInt(b))}return{wasm_z_sub:D,wasm_z_size:B,wasm_z_serialize:A,wasm_z_rem:z,wasm_z_positive:y,wasm_z_of_js_string_base:x,wasm_z_mul:w,wasm_z_hash:u,wasm_z_format:t,wasm_z_fdiv:s,wasm_z_deserialize:r,wasm_z_compare:q,wasm_z_cdiv:p,wasm_z_add:o,wasm_z_abs:n}}(globalThis))({"link":[["code-fd7a0adb9dcd573afcbe",0]],"generated":(a=>{var
b=a,c=a?.module?.export||a;return{"env":{"uint64_max_int":(...a)=>a[0]!==undefined?a[0]:0,"int128_of_int":(...a)=>a[0]!==undefined?a[0]:0,"uint64_of_int":(...a)=>a[0]!==undefined?a[0]:0,"uint32_of_int":(...a)=>a[0]!==undefined?a[0]:0,"uint128_of_int":(...a)=>a[0]!==undefined?a[0]:0,"int56_of_int":(...a)=>a[0]!==undefined?a[0]:0,"int48_of_int":(...a)=>a[0]!==undefined?a[0]:0,"int40_of_int":(...a)=>a[0]!==undefined?a[0]:0,"uint64_init_custom_ops":(...a)=>a[0]!==undefined?a[0]:0,"uint56_of_int":(...a)=>a[0]!==undefined?a[0]:0,"uint48_of_int":(...a)=>a[0]!==undefined?a[0]:0,"uint40_of_int":(...a)=>a[0]!==undefined?a[0]:0,"uint32_sub":(...a)=>a[0]!==undefined?a[0]:0,"uint32_max_int":(...a)=>a[0]!==undefined?a[0]:0,"uint32_init_custom_ops":(...a)=>a[0]!==undefined?a[0]:0,"uint128_max_int":(...a)=>a[0]!==undefined?a[0]:0,"uint128_init_custom_ops":(...a)=>a[0]!==undefined?a[0]:0,"int56_min_int":(...a)=>a[0]!==undefined?a[0]:0,"int56_max_int":(...a)=>a[0]!==undefined?a[0]:0,"int48_min_int":(...a)=>a[0]!==undefined?a[0]:0,"int48_max_int":(...a)=>a[0]!==undefined?a[0]:0,"int40_min_int":(...a)=>a[0]!==undefined?a[0]:0,"int40_max_int":(...a)=>a[0]!==undefined?a[0]:0,"int128_min_int":(...a)=>a[0]!==undefined?a[0]:0,"int128_max_int":(...a)=>a[0]!==undefined?a[0]:0,"int128_init_custom_ops":(...a)=>a[0]!==undefined?a[0]:0}}})(globalThis),"src":"w3c-runner.wasm.assets"});
