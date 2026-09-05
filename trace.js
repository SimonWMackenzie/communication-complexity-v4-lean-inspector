/* Curated paper correspondence. Targets use verified PDF text and destinations,
 * not from the Lean compiler; Lean references retain their own original index. */
(() => {
  'use strict';
  let api, trace, activePaper, selectedAnchor, mode = 'paper', zoom = 100;
  const byAnchor = new Map(), byPaper = new Map();
  const kindText = {definition:'Definition correspondence',statement:'Statement correspondence',assembled:'Proved through several Lean results',external:'External mathematical input',context:'Context / evidence',unmapped:'No curated correspondence'};
  /* One colour per classification, shared by the page highlights, the index
   * ticks and the key above the page stack. */
  const tint = {statement:'var(--hl-statement)',definition:'var(--hl-statement)',assembled:'var(--hl-assembled)',external:'var(--hl-external)',unmapped:'var(--hl-unmapped)',context:'var(--hl-context)'};
  const keyRows = [['statement','statement / definition','Statement or definition correspondence'],['assembled','assembled proof','Proved through several Lean results'],['external','external input','An external mathematical input — not proved in Lean'],['unmapped','no correspondence','No curated Lean correspondence'],['context','context','Context / evidence']];
  const originTint = {'this-paper':'var(--proved)',companion:'var(--reused)','earlier-route':'var(--def)',library:'var(--faint)'};
  const originText = {'this-paper':'Proved in Lean in this paper.',companion:'Reused from the companion paper’s Lean formalization (vendored npcc-lean module).','earlier-route':'Reused from an earlier route in this repository (ParameterizedNP).',library:'Library declaration (Mathlib / Lean core).'};
  const originName = {'this-paper':'This paper',companion:'Companion paper',"earlier-route":'Earlier route',library:'Library'};
  const el = (tag, cls, text) => { const n = document.createElement(tag); if(cls)n.className=cls;if(text!==undefined)n.textContent=text;return n; };
  const button = (text, fn, cls) => {const b=el('button',cls,text);b.type='button';b.addEventListener('click',fn);return b;};
  const $ = id => document.getElementById(id);
  function alignSelectedLocation(){
    if(mode!=='paper'||!selectedAnchor)return;
    const frame=$('paper-scroll'),page=$('paper-page-'+selectedAnchor.page)?.querySelector('.paper-image'),rect=selectedAnchor.rectangles[0];
    if(frame&&page&&frame.clientHeight)frame.scrollTo({top:frame.scrollTop+page.getBoundingClientRect().top-frame.getBoundingClientRect().top+rect.y0*page.getBoundingClientRect().height-65,behavior:'instant'});
  }
  function setMode(next) {
    mode=next; $('workspace').hidden=next!=='lean'; $('paper-workspace').hidden=next!=='paper';
    $('open-paper-trace').setAttribute('aria-pressed',String(next==='paper'));
    /* Every view has a pressed top-bar button: the Lean view is entered through
     * "Main theorem", so that button reports the current view too. */
    $('show-root').setAttribute('aria-pressed',String(next==='lean'));
    document.dispatchEvent(new CustomEvent('v4-view-changed',{detail:{mode:next}}));
    /* The paper workspace may have been hidden, in which case the earlier
     * alignment was a no-op against a zero-height frame. Align once now that
     * layout exists, and again on the next frame after the images settle. */
    if(next==='paper'&&selectedAnchor){replaceHash(selectedAnchor);alignSelectedLocation();requestAnimationFrame(alignSelectedLocation);}
  }
  function replaceHash(anchor) {try{history.replaceState(null,'','#'+new URLSearchParams({paper:anchor.paperId,anchor:anchor.label}));}catch(_){}}
  function defaultAnchor(paper) {return trace.anchors.find(a=>a.paperId===paper&&(a.label==='thm:reader-main'||a.label==='thm:finite-main'))||trace.anchors.find(a=>a.paperId===paper);}
  /* Recorded location boxes are evidence: each one is placed from its stored
   * rectangle and is never moved. A box's height is a heuristic extension below
   * the line it anchors, so on aligned equation displays one box can cover the
   * top of the next, and a short final row can sit inside its predecessor. That
   * is resolved for DISPLAY ONLY: the covering box is clipped back to the next
   * box's top edge (or, for two boxes on one line, to the next box's left edge).
   * clip-path also clips hit-testing, so both the painted region and the click
   * target become disjoint, while the element's border box - which a regression
   * test compares against the stored coordinates - is left exactly as recorded.
   * A trim never removes more than 82% of a box, so every anchor keeps a
   * visible, clickable sliver; --depth additionally paints smaller boxes above
   * larger ones as a safety net for any residual overlap. */
  const OVERLAP_EPS=0.004,OVERLAP_GAP=0.002,MIN_VISIBLE=0.18;
  function separateHighlights(boxes) {
    const meet=(a,b)=>Math.min(a.x1,b.x1)>Math.max(a.x0,b.x0)&&Math.min(a.y1,b.y1)>Math.max(a.y0,b.y0);
    for(const box of boxes){box.cutBottom=box.rect.y1;box.cutRight=box.rect.x1;}
    for(const a of boxes)for(const b of boxes){
      if(a===b||!meet(a.rect,b.rect))continue;
      if(b.rect.y0-a.rect.y0>OVERLAP_EPS)a.cutBottom=Math.min(a.cutBottom,b.rect.y0-OVERLAP_GAP);
      else if(Math.abs(b.rect.y0-a.rect.y0)<=OVERLAP_EPS&&b.rect.x0-a.rect.x0>OVERLAP_EPS)a.cutRight=Math.min(a.cutRight,b.rect.x0-OVERLAP_GAP);
    }
    const area=box=>(box.rect.x1-box.rect.x0)*(box.rect.y1-box.rect.y0);
    [...boxes].sort((p,q)=>area(q)-area(p)).forEach((box,index)=>box.button.style.setProperty('--depth',String(2+Math.min(index,120))));
    for(const box of boxes){
      const r=box.rect,width=r.x1-r.x0,height=r.y1-r.y0;
      const bottom=Math.max(box.cutBottom,r.y0+MIN_VISIBLE*height),right=Math.max(box.cutRight,r.x0+MIN_VISIBLE*width);
      if(bottom>=r.y1&&right>=r.x1)continue;
      const cutBottom=Math.min(100,Math.max(0,100*(r.y1-bottom)/height)),cutRight=Math.min(100,Math.max(0,100*(r.x1-right)/width));
      box.button.style.clipPath='inset(0% '+cutRight.toFixed(3)+'% '+cutBottom.toFixed(3)+'% 0%)';
    }
  }
  function showPaper(id, target) {
    if(!byPaper.has(id))return;
    activePaper=byPaper.get(id);$('trace-paper').value=id;$('trace-page').max=String(activePaper.pages.length);$('trace-page-total').textContent='/ '+activePaper.pages.length;
    const stack=$('paper-stack');stack.replaceChildren();
    for(const page of activePaper.pages){
      const figure=el('figure','paper-page');figure.id='paper-page-'+page.page;figure.dataset.page=page.page;
      const plane=el('div','paper-image');plane.style.aspectRatio=page.width+'/'+page.height;
      const image=el('img');image.src=page.file;image.width=page.width;image.height=page.height;image.loading='lazy';image.decoding='async';image.alt=activePaper.title+', page '+page.page;
      plane.append(image);figure.append(plane,el('figcaption',null,'Page '+page.page));
      const boxes=[];
      for(const anchor of trace.anchors.filter(a=>a.paperId===id))for(const rect of anchor.rectangles.filter(r=>r.page===page.page)){
        const b=button('',()=>selectAnchor(anchor.id,false),'paper-highlight '+anchor.classification);b.dataset.anchor=anchor.id;
        b.style.left=(100*rect.x0)+'%';b.style.top=(100*rect.y0)+'%';b.style.width=(100*(rect.x1-rect.x0))+'%';b.style.height=(100*(rect.y1-rect.y0))+'%';
        b.setAttribute('aria-label',anchor.title+' — '+kindText[anchor.classification]);b.title=anchor.title+'\n'+kindText[anchor.classification];plane.append(b);
        boxes.push({anchor,rect,button:b});
      }
      separateHighlights(boxes);
      stack.append(figure);
    }
    applyZoom();renderIndex();filterHighlights();selectAnchor((target||defaultAnchor(id)).id,true);
  }
  function selectAnchor(id, scroll=true) {
    const anchor=byAnchor.get(id);if(!anchor)return;
    if(!activePaper||activePaper.id!==anchor.paperId){showPaper(anchor.paperId,anchor);return;}
    selectedAnchor=anchor;setMode('paper');replaceHash(anchor);$('trace-page').value=anchor.page;
    for(const n of document.querySelectorAll('[data-anchor]')){const on=n.dataset.anchor===id;n.classList.toggle('selected',on);if(n.classList.contains('trace-index-item'))n.setAttribute('aria-current',String(on));}
    renderDetail(anchor);
    if(scroll)alignSelectedLocation();
  }
  function renderIndex() {
    if(!activePaper)return;
    const query=$('trace-search').value.toLowerCase().trim().split(/\s+/).filter(Boolean),all=$('trace-unmapped').checked;
    const anchors=trace.anchors.filter(a=>a.paperId===activePaper.id&&(all||a.lean.length)&&query.every(s=>(a.title+' '+a.label+' '+a.note+' '+a.lean.join(' ')).toLowerCase().includes(s)));
    const list=$('paper-index-list');list.replaceChildren();
    for(const a of anchors){const b=button(a.title,()=>selectAnchor(a.id),'trace-index-item');b.dataset.anchor=a.id;b.dataset.classification=a.classification;b.style.setProperty('--tick',tint[a.classification]||'var(--hl-unmapped)');b.setAttribute('aria-current',String(selectedAnchor?.id===a.id));b.append(el('span','meta','Page '+a.page+' · '+kindText[a.classification]));list.append(b);}
    if(!anchors.length)list.append(el('p','paper-empty','No matching paper locations.'));
    $('trace-index-count').textContent=anchors.length+' paper locations';
  }
  function filterHighlights(){const all=$('trace-unmapped').checked;for(const b of document.querySelectorAll('.paper-highlight.unmapped,.paper-highlight.context'))b.hidden=!all;}
  const provFields=[['statedBy','Stated by'],['lean','In Lean'],['entersRoot','Enters the root'],['intendedSource','Intended source']];
  /* The provenance record of a curated map step, rendered identically in the
   * paper tracer and in the proof-map aside. */
  function provenanceCard(node){
    const box=el('section','prov '+(node.origin==='result'?'is-result':node.external?'is-external':'')),list=el('dl');
    box.append(el('div','eyebrow','Provenance'));
    for(const [key,label]of provFields)if(node.provenance&&node.provenance[key])list.append(el('dt',null,label),el('dd',null,node.provenance[key]));
    box.append(list);return box;
  }
  /* Called once the proof map and the origin model are loaded, so the paper
   * detail can show provenance and Lean-origin marks it could not show yet. */
  function refresh(){if(activePaper){renderIndex();if(selectedAnchor)renderDetail(selectedAnchor);}}
  function renderDetail(anchor) {
    const host=$('paper-detail');host.replaceChildren();
    host.append(el('div','eyebrow','Paper → Lean'),el('h2',null,anchor.title),el('span','trace-kind '+anchor.classification,kindText[anchor.classification]),el('p',null,anchor.note));
    if(anchor.classification==='external')host.append(el('p','trace-detail-note','The Lean links below state or consume this input. They do not prove its existence. The corresponding human argument remains in the paper.'));
    else if(anchor.classification==='assembled')host.append(el('p','trace-detail-note','These are proof components, not a claim of identical proof text. Intermediate hypotheses remain visible; the final theorem supplies the required ingredients.'));
    /* Where this paper location is a step of the curated mathematical map, its
     * provenance record — who states it, whether Lean proves it, how it enters
     * the root theorem, and its intended source — is shown here as well. */
    const step=(window.V4ProofMap?.nodes||[]).find(n=>n.paperAnchors.includes(anchor.id));
    if(step?.provenance)host.append(provenanceCard(step));
    if(step)host.append(button('Open “'+step.title+'” in the proof map',()=>window.V4Graph&&window.V4Graph.open('overview',step.id),'trace-map-link'));
    const related=el('section');related.append(el('h3',null,anchor.lean.length?'Corresponding Lean source':'Correspondence not yet curated'));
    for(const name of anchor.lean){
      const d=api.byId.get(name),card=el('article','trace-lean-item'),origin=window.V4Origin?window.V4Origin(d):null;
      if(origin)card.style.setProperty('--tick',originTint[origin]);
      card.append(el('div','mono',name));
      if(d.plainEnglish)card.append(el('p',null,typeof d.plainEnglish==='string'?d.plainEnglish:JSON.stringify(d.plainEnglish)));
      if(origin){const line=el('div','origin-line'),dot=el('span','origin-tick');dot.style.setProperty('--tick',originTint[origin]);line.append(dot,el('span',null,originName[origin]+' — '+originText[origin]));card.append(line);}
      const actions=el('div','trace-lean-actions');actions.append(button('Definition card',()=>api.openDeclarationCard(name)),button('Statement',()=>openLean(name,'statement')),button('Full source and proof',()=>openLean(name,'source')),button('References',()=>openLean(name,'dependencies')));card.append(actions);related.append(card);}
    host.append(related);
    const other=trace.anchors.filter(a=>a.paperId!==anchor.paperId&&a.lean.some(n=>anchor.lean.includes(n)));
    if(other.length){const details=el('details');details.append(el('summary',null,'Related locations in the other paper ('+other.length+')'));for(const a of other)details.append(button(a.title,()=>selectAnchor(a.id),'dep-link'));details.append(el('p','trace-tooltip','These locations share listed Lean components; this is navigation, not a separately certified equivalence.'));host.append(details);}
    const source=el('details');source.append(el('summary',null,'Location and provenance'));api.renderValue({paperLabel:anchor.label,physicalPdfPage:anchor.page,printedPage:anchor.printedPage,pdfDestination:anchor.destination,compiledDestinationPage:anchor.compiledDestinationPage,locationVerification:anchor.locationVerification,source:anchor.source,pdfSha256:activePaper.pdfSha256,auxSha256:activePaper.auxSha256},source);host.append(source);
    if(api.DATA.meta.paperRevision)source.append(el('p','trace-tooltip',api.DATA.meta.paperRevision.notice));
    host.append(el('p','trace-tooltip','Highlights mark the beginning/location of a labelled statement or equation. They do not delimit a whole proof. Where two recorded location boxes overlap, the upper box is trimmed at the next box\'s top edge for display; the recorded coordinates are unchanged. Paper-to-Lean correspondence is curated; compiler-derived references remain available in the Lean view.'));
    const a=el('a',null,'Open the original PDF (selectable and searchable text)');a.href=activePaper.pdf;a.target='_blank';a.rel='noopener';host.append(a);
  }
  function openLean(id,tab='statement'){setMode('lean');api.selectDeclaration(id,tab);$('main-content').scrollIntoView({block:'start'});}
  function addLinks(d,host){if(!api||!d.traceAnchors?.length)return;const links=el('div','trace-source-links');links.append(el('span','trace-links-label','Trace this declaration in the papers'));for(const id of d.traceAnchors){const a=byAnchor.get(id);if(a)links.append(button((a.paperId==='reader'?'Reader: ':'Formal: ')+a.title,()=>selectAnchor(id)));}host.append(links);}
  function applyZoom(){if(!$('paper-stack'))return;for(const p of $('paper-stack').children){p.style.width=zoom+'%';p.style.maxWidth=zoom===100?'1050px':'none';}$('trace-zoom-value').textContent=zoom+'%';}
  function fromHash(){const p=new URLSearchParams(location.hash.slice(1));if(p.has('anchor')){const a=byAnchor.get(p.get('paper')+':'+p.get('anchor'));if(a){selectAnchor(a.id);return true;}}if(p.has('decl')){setMode('lean');return true;}return false;}
  /* The three detail panels open the same way: eyebrow, title, kind badge,
   * prose. The Lean head is the one built in the offline template, so its
   * eyebrow is added and its badges are moved below the sub-line here; what
   * fills those elements is untouched. */
  function orderSelectedHead(){
    const head=document.querySelector('.selected-head'),badges=$('selected-badges'),sub=$('selected-sub');
    if(!head)return;
    if(!head.querySelector('.eyebrow'))head.prepend(el('div','eyebrow','Lean declaration'));
    if(badges&&sub)sub.after(badges);
  }
  function start(event){
    api=event.detail;orderSelectedHead();trace=api.DATA.trace;if(!trace)return;
    for(const a of trace.anchors)byAnchor.set(a.id,a);for(const p of trace.papers)byPaper.set(p.id,p);
    const main=el('section');main.id='paper-workspace';main.hidden=true;
    const toolbar=el('div','trace-toolbar'),paper=el('select');paper.id='trace-paper';paper.setAttribute('aria-label','Choose manuscript');for(const p of trace.papers){const o=el('option',null,p.title);o.value=p.id;paper.append(o);}paper.addEventListener('change',()=>showPaper(paper.value));
    const pageLabel=el('label',null,'Page '),page=el('input');page.id='trace-page';page.type='number';page.min='1';page.value='1';page.setAttribute('aria-label','PDF page');pageLabel.append(page);const total=el('span');total.id='trace-page-total';pageLabel.append(total);
    const go=()=>{const n=Math.max(1,Math.min(activePaper.pages.length,Number(page.value)||1));page.value=n;const target=$('paper-page-'+n),frame=$('paper-scroll');frame.scrollTo({top:frame.scrollTop+target.getBoundingClientRect().top-frame.getBoundingClientRect().top,behavior:'instant'});};page.addEventListener('keydown',e=>{if(e.key==='Enter')go();});
    const zoomValue=el('output');zoomValue.id='trace-zoom-value';
    const zoomGroup=el('div','control-group zb');zoomGroup.setAttribute('role','group');zoomGroup.setAttribute('aria-label','Page zoom');
    /* "Fit width" is the zoom's reset, so it sits inside the pill as a fourth
     * child, the way the top bar's text-size reset does. */
    zoomGroup.append(button('−',()=>{zoom=Math.max(60,zoom-10);applyZoom();}),zoomValue,button('+',()=>{zoom=Math.min(200,zoom+10);applyZoom();}),button('Fit width',()=>{zoom=100;applyZoom();}));
    const zoomBar=el('div','zoombar');zoomBar.append(zoomGroup);
    /* The classification key: what a highlight's colour means. */
    const key=el('div','tkey');key.setAttribute('aria-label','Highlight colour key');
    for(const [cls,text,title]of keyRows){const k=el('span','k is-'+cls),swatch=el('span','kb');swatch.style.setProperty('--tick',tint[cls]);k.title=title;k.append(swatch,el('span',null,text));key.append(k);}
    toolbar.append(paper,pageLabel,button('Go',go),key,el('span','trace-spacer'),zoomBar,button('Selected statement ↓',()=>{$('paper-detail').scrollIntoView({block:'start'});},'trace-mobile-detail'),button('Lean inspector',()=>openLean(api.DATA.root)));
    const layout=el('div','paper-layout'),index=el('nav','paper-index');index.setAttribute('aria-label','Paper statement index');const head=el('div','paper-index-head'),search=el('input');search.id='trace-search';search.type='search';search.placeholder='Find a paper statement…';search.setAttribute('aria-label','Search paper statements');search.addEventListener('input',renderIndex);
    const flag=el('label'),checkbox=el('input');checkbox.id='trace-unmapped';checkbox.type='checkbox';checkbox.addEventListener('change',()=>{renderIndex();filterHighlights();});flag.append(checkbox,document.createTextNode(' Show unmapped paper locations'));const count=el('div','trace-index-count');count.id='trace-index-count';head.append(search,flag,count);const list=el('div','paper-index-list');list.id='paper-index-list';index.append(head,list);
    const scroll=el('div','paper-scroll');scroll.id='paper-scroll';const stack=el('div','paper-stack');stack.id='paper-stack';scroll.append(stack);const detail=el('aside','paper-detail');detail.id='paper-detail';detail.setAttribute('aria-live','polite');layout.append(index,scroll,detail);main.append(toolbar,layout);$('workspace').before(main);
    const top=button('📄 Trace the paper',()=>{setMode('paper');if(!selectedAnchor)showPaper('reader');});top.id='open-paper-trace';top.title='Read the papers with every formalized statement highlighted';document.querySelector('.toolbar').prepend(top);
    for(const id of ['show-root','intro-root','show-provenance'])$(id).addEventListener('click',()=>setMode('lean'));
    window.addEventListener('hashchange',fromHash);
    new ResizeObserver(()=>requestAnimationFrame(alignSelectedLocation)).observe($('paper-scroll'));
    document.addEventListener('v4-declaration-selected',()=>setMode('lean'));
    document.addEventListener('keydown',e=>{if(e.key==='/'&&mode==='paper'&&!e.target.matches('input,textarea,select,[contenteditable=true]')){e.preventDefault();e.stopImmediatePropagation();$('trace-search').focus();}},true);
    const incoming=location.hash;showPaper('reader');
    if(incoming){try{history.replaceState(null,'',incoming);}catch(_){}}
    if(!fromHash())selectAnchor(defaultAnchor('reader').id);
    // Re-render statement once now that the reverse-link integration is ready.
    if(mode==='lean')api.selectDeclaration(new URLSearchParams(incoming.slice(1)).get('decl')||api.DATA.root,'statement',false);
  }
  window.V4Trace={addLinks,openLean,selectAnchor,setMode,refresh,provenanceCard};
  document.addEventListener('v4-inspector-ready',start,{once:true});
})();
