// User-authorized browser QA against our loopback preview; no authenticated session.
const {chromium}=require(process.argv[2]||'playwright');
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {createHash}=require('node:crypto');
const out=path.resolve('qa/browser'),checks=[];
const baseURL=process.argv[3]||'http://127.0.0.1:8764/';
function check(name,condition){assert.ok(condition,name);checks.push(name);console.log('PASS '+name);}
async function waitReady(page){await page.waitForFunction(()=>window.V4Graph&&window.V4Trace,null,{timeout:120000});}
async function showControl(page,id){
 // Resizing or changing text size moves controls on the next layout frame.
 await page.evaluate(()=>new Promise(r=>requestAnimationFrame(()=>requestAnimationFrame(r))));
 if(!await page.locator(id).isVisible())await page.locator('.more > summary').click();
}
async function checkPaperGeometry(page,label){
 await page.locator('.paper-highlight.selected').first().evaluate(async h=>{await h.parentElement.querySelector('img').decode();await new Promise(r=>requestAnimationFrame(()=>requestAnimationFrame(r)));});
 const result=await page.evaluate(()=>{
  const h=document.querySelector('.paper-highlight.selected'),b=h.getBoundingClientRect(),p=h.parentElement.getBoundingClientRect(),i=h.parentElement.querySelector('img').getBoundingClientRect(),f=document.getElementById('paper-scroll').getBoundingClientRect();
  return {aligned:Math.abs(b.top-(p.top+parseFloat(h.style.top)*p.height/100))<1&&Math.abs(b.height-parseFloat(h.style.height)*p.height/100)<1&&Math.abs(i.height-p.height)<1,visible:b.top>=f.top&&b.bottom<=f.bottom};
 });
 check(label+' highlights follow exact PDF coordinates',result.aligned);
 check(label+' selected theorem stays inside reading area',result.visible);
}
async function checkNestedEquations(page,label,paper='reader'){
 const anchor=paper==='reader'?'reader:thm:reader-main':'formal:thm:finite-main';
 const theorem=page.locator('.paper-highlight[data-anchor="'+anchor+'"]');
 for(const n of [3,4,5,6,7]){
  // Click the theorem heading itself, then an inner row using real pointer
  // hit-testing. Programmatic DOM clicks would miss an overlay interception.
  await theorem.click({position:{x:12,y:12},timeout:5000});
  const row=page.getByRole('button',{name:new RegExp('^Equation '+n+'—')});
  await row.click({timeout:5000});
  check(label+' equation '+n+' is clickable inside the selected theorem',
   await row.evaluate(e=>e.classList.contains('selected'))&&
   (await page.locator('#paper-detail h2').innerText()).includes('Equation '+n));
 }
 await theorem.click({position:{x:12,y:12},timeout:5000});
 check(label+' theorem remains selectable after its inner equations',await theorem.evaluate(e=>e.classList.contains('selected')));
}
(async()=>{
 fs.mkdirSync(out,{recursive:true});
 const browser=await chromium.launch({headless:true,channel:'msedge'});
 try{
  const context=await browser.newContext({viewport:{width:1600,height:1100},acceptDownloads:true});
  const page=await context.newPage(),errors=[];page.on('pageerror',e=>errors.push(e.message));
  await page.goto(baseURL,{waitUntil:'load',timeout:120000});
  await waitReady(page);
  await page.waitForFunction(()=>document.querySelector('.paper-highlight.selected'));
  check('landing is the reader paper at its main theorem',await page.locator('#paper-workspace').isVisible()&&/paper=reader&anchor=thm%3Areader-main/.test(page.url()));
  check('paper opens without fatal errors',!(await page.locator('#fatal').isVisible()));
  check('reader main theorem is on its actual PDF page',(await page.locator('#trace-page').inputValue())==='2');
  await checkPaperGeometry(page,'Desktop');
  check('selected paper highlight is in the reading viewport',await page.evaluate(()=>{const h=document.querySelector('.paper-highlight.selected').getBoundingClientRect(),f=document.getElementById('paper-scroll').getBoundingClientRect();return h.top>=f.top&&h.bottom<=f.bottom;}));
  await page.screenshot({path:path.join(out,'01-reader-desktop.jpg'),type:'jpeg',quality:88});
  await checkNestedEquations(page,'Desktop');
  await page.locator('#open-proof-map').click();
  check('dependency graph is prominent and opens',await page.locator('#graph-workspace').isVisible());
  check('all mathematical nodes rendered',await page.locator('.proof-node').count()===14);
  await page.screenshot({path:path.join(out,'02-map-desktop.jpg'),type:'jpeg',quality:88});
  await page.locator('[data-graph-node=source]').click();
  check('external input is labelled honestly',(await page.locator('#graph-detail').innerText()).includes('do not prove its existence'));
  await page.reload({waitUntil:'load'});await waitReady(page);
  check('shared curated selection survives reload',(await page.locator('#graph-detail h2').innerText())==='Source graphs');
  await page.locator('#graph-mode').selectOption('source');
  await page.reload({waitUntil:'load'});await waitReady(page);
  check('view dropdown is preserved in the URL',(await page.locator('#graph-mode').inputValue())==='source');
  check('source relation distinguished',(await page.locator('#graph-subtitle').innerText()).includes('not dependencies extracted from kernel proof terms'));
  // The source-mode controls live in a <details> that starts closed; open it before driving them.
  if(!await page.locator('#graph-grouped').isVisible())await page.locator('#source-controls-box > summary').click();
  await page.locator('#graph-origin-this-paper').uncheck();
  check('filtered module does not retain hidden declarations',await page.evaluate(()=>{const v=V4Graph.getView();return v.eligible.length===1&&v.nodes.length===1&&v.nodes[0].members.length===1&&v.edgePairs.length===0;}));
  await page.locator('#graph-origin-this-paper').check();
  await page.locator('#graph-grouped').uncheck();
  await page.locator('#graph-depth').selectOption('3');
  await page.locator('#graph-limit').selectOption('40');
  const counts=await page.locator('#graph-count').innerText();
  check('display cap and total are visible',/Showing 40 of/.test(counts));
  await page.screenshot({path:path.join(out,'03-source-graph.jpg'),type:'jpeg',quality:88});
  await page.locator('.proof-edge').first().focus();await page.keyboard.press('Enter');
  check('edge evidence shows source occurrences',(await page.locator('#graph-detail').innerText()).includes('recorded occurrence'));
  const edgePoint=await page.locator('.proof-edge-hit').first().evaluate(e=>{const p=e.getPointAtLength(e.getTotalLength()*.25),q=new DOMPoint(p.x,p.y).matrixTransform(e.getScreenCTM());return {x:q.x,y:q.y};});
  await page.mouse.click(edgePoint.x,edgePoint.y);
  check('wide arrow mouse target works',(await page.locator('#graph-detail').innerText()).includes('recorded occurrence'));
  await page.locator('#graph-search').fill('rationalCommonBridge');
  await page.locator('#graph-search-results button').first().click();
  check('graph search changes focus',(await page.locator('#graph-focus').innerText()).includes('rationalCommonBridge'));
  await page.reload({waitUntil:'load'});await waitReady(page);
  check('shared source focus survives reload',(await page.locator('#graph-focus').innerText()).includes('rationalCommonBridge'));
  await page.locator('#graph-detail').getByRole('button',{name:'Path from main theorem',exact:true}).click();
  check('root path is explained',(await page.locator('#graph-message').innerText()).includes('shortest recorded-reference path'));
  const old=await page.locator('#graph-zoom').innerText();
  await page.locator('.graph-statusbar').getByRole('button',{name:'+',exact:true}).click();
  check('graph zoom works',(await page.locator('#graph-zoom').innerText())!==old);
  await page.locator('#graph-detail').getByRole('button',{name:'Open statement',exact:true}).click();
  check('graph opens exact Lean statement',await page.locator('#workspace').isVisible());
  check('selected declaration matches graph',(await page.locator('#selected-title').innerText()).includes('rationalCommonBridge'));
  await page.locator('#tab-dependencies').click();
  check('Lean dependency tab offers deeper explorer',await page.getByRole('button',{name:'Open dependency explorer',exact:true}).isVisible());
  await page.getByRole('button',{name:'Open dependency explorer',exact:true}).click();
  check('deeper explorer opens from Lean',await page.locator('#graph-workspace').isVisible());
  await page.locator('#open-paper-trace').click();
  check('paper remains reachable from graph',await page.locator('#paper-workspace').isVisible());
  await page.locator('#trace-page').fill('2.5');await page.locator('.trace-pagebox').getByRole('button',{name:'Go',exact:true}).click();
  check('fractional PDF page input is normalized',(await page.locator('#trace-page').inputValue())==='2');
  await page.locator('#paper-detail').getByRole('button',{name:'Definition card',exact:true}).first().click();
  check('paper-linked definition card opens',await page.locator('.definition-card').isVisible());
  await page.keyboard.press('Escape');
  await page.locator('#paper-detail').getByRole('button',{name:'Statement',exact:true}).first().click();
  check('paper opens Lean',await page.locator('#workspace').isVisible());
  check('selected Lean navigation has readable contrast',await page.locator('.decl-row[aria-current=true]').evaluate(e=>{const s=getComputedStyle(e);return s.backgroundColor==='rgb(27, 36, 49)'&&s.color==='rgb(220, 227, 236)';}));
  await page.screenshot({path:path.join(out,'04-lean-desktop.jpg'),type:'jpeg',quality:88});
  await page.locator('.trace-source-links button').first().click();
  check('Lean reverse link returns to paper',await page.locator('#paper-workspace').isVisible());
  await page.setViewportSize({width:390,height:844});
  await page.locator('#open-proof-map').click();
  await page.keyboard.press('/');
  check('mobile search shortcut reveals folded controls',await page.locator('#top-search').isVisible()&&await page.locator('#top-search').evaluate(e=>document.activeElement===e));
  await page.keyboard.press('Escape');
  await page.locator('.more > summary').click();
  check('mobile has no page-level horizontal overflow',await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));
  await page.screenshot({path:path.join(out,'05-map-mobile.jpg'),type:'jpeg',quality:88,fullPage:true});
  await page.locator('#open-paper-trace').click();
  await page.locator('#trace-paper').selectOption('reader');
  await page.waitForFunction(()=>{const h=document.querySelector('.paper-highlight.selected').getBoundingClientRect(),f=document.getElementById('paper-scroll').getBoundingClientRect();return h.top>=f.top&&h.bottom<=f.bottom;});
  check('mobile selected theorem stays in view after resizing',true);
  await page.locator('#paper-page-2 img').evaluate(img=>img.decode());
  await checkPaperGeometry(page,'Mobile');
  await checkNestedEquations(page,'Mobile');
  check('mobile paper has no page-level overflow',await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));
  await page.locator('#paper-scroll').scrollIntoViewIfNeeded();
  await page.screenshot({path:path.join(out,'06-reader-mobile.jpg'),type:'jpeg',quality:88});
  await page.setViewportSize({width:1440,height:1000});
  for(let i=0;i<10;i++){await showControl(page,'#scale-up');await page.locator('#scale-up').click();}
  check('text enlargement reaches 200 percent',(await page.locator('#scale-value').innerText())==='200%');
  check('text enlargement keeps paper usable',await page.locator('#trace-paper').isVisible());
  check('200 percent text has no page-level overflow',await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));
  await page.locator('#paper-scroll').scrollIntoViewIfNeeded();
  await checkPaperGeometry(page,'200 percent text');
  await checkNestedEquations(page,'200 percent text');
  await page.screenshot({path:path.join(out,'07-reader-200-percent.jpg'),type:'jpeg',quality:88});
  await showControl(page,'#scale-reset');await page.locator('#scale-reset').click();
  await page.locator('#trace-paper').selectOption('formal');
  check('formal paper opens its main theorem on page 4',(await page.locator('#trace-page').inputValue())==='4');
  await checkPaperGeometry(page,'Formal paper');
  await page.locator('#trace-unmapped').check();
  await checkNestedEquations(page,'Formal paper with unmapped equations shown','formal');
  await page.locator('#trace-unmapped').uncheck();
  await page.locator('#paper-scroll').scrollIntoViewIfNeeded();
  await page.screenshot({path:path.join(out,'08-formal-desktop.jpg'),type:'jpeg',quality:88});
  await page.goto(baseURL+'#view=graph&graph=source',{waitUntil:'load',timeout:120000});
  await page.waitForFunction(()=>window.V4Graph,null,{timeout:120000});
  check('shared graph URL restores graph view',await page.locator('#graph-workspace').isVisible());
  for(const file of ['snapshot.json','graph.js','graph-core.js','trace.js','trace.css','design.css','proof-data.json.gz','papers/reader/paper.pdf','papers/formal/paper.pdf']){
   const response=await page.request.get(baseURL+file,{timeout:120000});
   const digest=b=>createHash('sha256').update(b).digest('hex');
   check('served asset matches reviewed build: '+file,response.ok()&&digest(await response.body())===digest(fs.readFileSync(path.join('dist',file))));
   await response.dispose();
  }
  check('no browser JavaScript errors',errors.length===0);
  fs.writeFileSync(path.join(out,'report.json'),JSON.stringify({success:true,baseURL,checks,errors},null,2));
  console.log(checks.length+' browser checks passed.');
 }finally{await browser.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
