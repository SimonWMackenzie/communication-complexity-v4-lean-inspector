// Parse every inline classic script without executing a browser or the UI.
const fs=require('node:fs'),vm=require('node:vm');
const html=fs.readFileSync('dist/index.html','utf8');
let count=0;
for(const match of html.matchAll(/<script([^>]*)>([\s\S]*?)<\/script>/g)){
  if(/src=|application\/json/.test(match[1]))continue;
  new vm.Script(match[2],{filename:'index.html:inline-'+(++count)});
}
if(!count)throw new Error('No application script found');
new vm.Script(fs.readFileSync('trace.js','utf8'),{filename:'trace.js'});
for(const file of ['graph.js','graph-core.js'])new vm.Script(fs.readFileSync(file,'utf8'),{filename:file});
console.log('JavaScript syntax PASS: '+count+' inline application script, paper tracing and dependency explorer.');
