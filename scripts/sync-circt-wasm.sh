#!/usr/bin/env bash
set -euo pipefail

SRC_DIR="${1:-vendor/circt/build-wasm/bin}"
DST_DIR="${2:-public/circt}"

TOOLS=("circt-bmc" "circt-sim" "circt-verilog")
missing=()

for tool in "${TOOLS[@]}"; do
  if [ ! -f "$SRC_DIR/$tool.js" ]; then
    missing+=("$tool.js")
  fi
  if [ ! -f "$SRC_DIR/$tool.wasm" ]; then
    missing+=("$tool.wasm")
  fi
done

if [ "${#missing[@]}" -ne 0 ]; then
  echo "Missing CIRCT wasm artifacts in $SRC_DIR" >&2
  echo "Missing files: ${missing[*]}" >&2
  exit 1
fi

mkdir -p "$DST_DIR"
for tool in "${TOOLS[@]}"; do
  cp -f "$SRC_DIR/$tool.js" "$DST_DIR/$tool.js"
  cp -f "$SRC_DIR/$tool.wasm" "$DST_DIR/$tool.wasm"
done

# Browser compatibility shim for circt-sim builds linked with NODERAWFS.
# Upstream sim wasm artifacts may include Node-only glue even when consumed
# from a web worker. Patch those sections to keep the tutorial runtime web-safe.
node - "$DST_DIR/circt-sim.js" <<'NODE'
const fs = require('fs');

const simPath = process.argv[2];
let source = fs.readFileSync(simPath, 'utf8');

const browserPathDef =
  'var PATH={isAbs:path=>path.charAt(0)==="/",splitPath:filename=>{var splitPathRe=/^(\\/?|)([\\s\\S]*?)((?:\\.{1,2}|[^\\/]+?|)(\\.[^.\\/]*|))(?:[\\/]*)$/;return splitPathRe.exec(filename).slice(1)},normalizeArray:(parts,allowAboveRoot)=>{var up=0;for(var i=parts.length-1;i>=0;i--){var last=parts[i];if(last==="."){parts.splice(i,1)}else if(last===".."){parts.splice(i,1);up++}else if(up){parts.splice(i,1);up--}}if(allowAboveRoot){for(;up;up--){parts.unshift("..")}}return parts},normalize:path=>{var isAbsolute=PATH.isAbs(path),trailingSlash=path.slice(-1)==="/";path=PATH.normalizeArray(path.split("/").filter(p=>!!p),!isAbsolute).join("/");if(!path&&!isAbsolute){path="."}if(path&&trailingSlash){path+="/"}return(isAbsolute?"/":"")+path},dirname:path=>{var result=PATH.splitPath(path),root=result[0],dir=result[1];if(!root&&!dir){return"."}if(dir){dir=dir.slice(0,-1)}return root+dir},basename:path=>path&&path.match(/([^\\/]+|\\/)\\/*$/)[1],join:(...paths)=>PATH.normalize(paths.join("/")),join2:(l,r)=>PATH.normalize(l+"/"+r)};';
const browserPathFsDef =
  'var PATH_FS={resolve:(...args)=>{var resolvedPath="",resolvedAbsolute=false;for(var i=args.length-1;i>=-1&&!resolvedAbsolute;i--){var path=i>=0?args[i]:FS.cwd();if(typeof path!="string"){throw new TypeError("Arguments to path.resolve must be strings")}else if(!path){return""}resolvedPath=path+"/"+resolvedPath;resolvedAbsolute=PATH.isAbs(path)}resolvedPath=PATH.normalizeArray(resolvedPath.split("/").filter(p=>!!p),!resolvedAbsolute).join("/");return(resolvedAbsolute?"/":"")+resolvedPath||"."},relative:(from,to)=>{from=PATH_FS.resolve(from).slice(1);to=PATH_FS.resolve(to).slice(1);function trim(arr){var start=0;for(;start<arr.length;start++){if(arr[start]!=="")break}var end=arr.length-1;for(;end>=0;end--){if(arr[end]!=="")break}if(start>end)return[];return arr.slice(start,end-start+1)}var fromParts=trim(from.split("/"));var toParts=trim(to.split("/"));var length=Math.min(fromParts.length,toParts.length);var samePartsLength=length;for(var i=0;i<length;i++){if(fromParts[i]!==toParts[i]){samePartsLength=i;break}}var outputParts=[];for(var i=samePartsLength;i<fromParts.length;i++){outputParts.push("..")}outputParts=outputParts.concat(toParts.slice(samePartsLength));return outputParts.join("/")}};';

const replaceExact = (regex, replacement, label) => {
  const next = source.replace(regex, replacement);
  if (next === source) {
    throw new Error(`failed to patch circt-sim.js (${label})`);
  }
  source = next;
};

replaceExact(
  /var nodePath=require\("path"\);var PATH=\{isAbs:nodePath\.isAbsolute,normalize:nodePath\.normalize,dirname:nodePath\.dirname,basename:nodePath\.basename,join:nodePath\.join,join2:nodePath\.join\};/,
  browserPathDef,
  'path definition'
);

replaceExact(
  /var PATH_FS=\{resolve:\(\.\.\.paths\)=>\{paths\.unshift\(FS\.cwd\(\)\);return nodePath\.posix\.resolve\(\.\.\.paths\)\},relative:\(from,to\)=>nodePath\.posix\.relative\(from\|\|FS\.cwd\(\),to\|\|FS\.cwd\(\)\)\};/,
  browserPathFsDef,
  'PATH_FS definition'
);

replaceExact(
  /if\(ENVIRONMENT_IS_NODE\)\{NODEFS\.staticInit\(\)\}if\(!ENVIRONMENT_IS_NODE\)\{throw new Error\("NODERAWFS is currently only supported on Node\.js environment\."\)\}var _wrapNodeError=function\(func\)\{return function\(\.\.\.args\)\{try\{return func\(\.\.\.args\)\}catch\(e\)\{if\(e\.code\)\{throw new FS\.ErrnoError\(ERRNO_CODES\[e\.code\]\)\}throw e\}\}\};var VFS=\{\.\.\.FS\};for\(var _key in NODERAWFS\)\{FS\[_key\]=_wrapNodeError\(NODERAWFS\[_key\]\)\}/,
  'var VFS={...FS};',
  'NODERAWFS bootstrap'
);

fs.writeFileSync(simPath, source);
console.log(`Patched browser compatibility in ${simPath}`);
NODE

cat >"$DST_DIR/package.json" <<'EOF'
{
  "type": "commonjs"
}
EOF

echo "Synced CIRCT wasm artifacts:"
for tool in "${TOOLS[@]}"; do
  ls -lh "$DST_DIR/$tool.js" "$DST_DIR/$tool.wasm"
done
