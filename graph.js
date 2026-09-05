/* Two intentionally different relations: mathematical inputs and source references. */
(() => {
  'use strict';
  const initialHash=location.hash, G=window.ProofGraphCore;
  const $=id=>document.getElementById(id);
  const el=(tag,cls,text)=>{const n=document.createElement(tag);if(cls)n.className=cls;if(text!==undefined)n.textContent=text;return n;};
  const btn=(text,fn,cls)=>{const b=el('button',cls,text);b.type='button';b.addEventListener('click',fn);return b;};
  const svgEl=(tag,attrs={})=>{const n=document.createElementNS('http://www.w3.org/2000/svg',tag);for(const [k,v]of Object.entries(attrs))n.setAttribute(k,v);return n;};
  const short=id=>id.split('.').slice(-2).join('.');
  let api,g,map,viewMode='overview',focus,selected,view,zoom=1,pathIds=null,svgSize,sequence=0;
  const options={direction:'out',depth:2,limit:80,libraries:false,grouped:true};
  function switchView(next){
    viewMode=next;$('graph-mode').value=next;$('source-controls').hidden=next!=='source';
    $('graph-subtitle').textContent=next==='overview'
      ?'Mathematical ingredients → results that use them. Select a step to read its explanation, paper statement and Lean components.'
      :'Declaration → name it references. These are compiler-recorded source references, not dependencies extracted from kernel proof terms.';
    render();
  }
  function open(mode='overview',id){
    if(!g)return;
    if(id&&g.cards.has(id)){focus=id;selected=id;pathIds=null;}
    window.V4Trace.setMode('graph');switchView(mode);
    try{history.replaceState(null,'','#'+new URLSearchParams({view:'graph',graph:mode,focus:focus}));}catch(_){}
  }
  function linkPaper(id,host){
    const a=api.DATA.trace.anchors.find(x=>x.id===id);if(!a)return;
    host.append(btn((a.paperId==='reader'?'Reader · ':'Formal · ')+a.title,()=>window.V4Trace.selectAnchor(id),'graph-paper-link'));
  }
  function detailCard(id){
    selected=id;const d=g.cards.get(id),host=$('graph-detail');host.replaceChildren();
    host.append(el('div','eyebrow','Lean source'),el('h2',null,short(id)),el('p','graph-full-name',id));
    const prose=typeof d.plainEnglish==='string'?d.plainEnglish:d.plainEnglish?.summary;
    if(prose)host.append(el('p',null,prose));
    host.append(el('p','graph-detail-note',G.isTerminal(d)?'This is a terminal reference card: its standalone source body is not embedded. That does not mean it has no mathematical dependencies.':'A source-indexed declaration. Its exact statement, surrounding definitions and available axiom evidence are in the Lean inspector.'));
    const counts=el('div','graph-stat-row');
    counts.append(el('span',null,g.out.get(id).length+' outgoing references'),el('span',null,g.incoming.get(id).length+' incoming references'));host.append(counts);
    const actions=el('div','graph-actions');
    actions.append(btn('Explore from here',()=>{focus=id;pathIds=null;options.grouped=false;$('graph-grouped').checked=false;render();}),
      btn('Open statement',()=>window.V4Trace.openLean(id,'statement')),
      btn('Full source and proof',()=>window.V4Trace.openLean(id,'source')),
      btn('Definition card',()=>api.openDeclarationCard(id)),
      btn('Path from main theorem',()=>findPath(id)));
    host.append(actions);
    if(d.traceAnchors?.length){host.append(el('h3',null,'In the papers'));for(const a of d.traceAnchors)linkPaper(a,host);}
    const references=el('details');references.append(el('summary',null,'All direct references ('+g.out.get(id).length+')'));
    for(const target of g.out.get(id))references.append(btn(short(target),()=>detailEdge({source:id,target,pairs:[[id,target]]}),'graph-paper-link'));
    host.append(references);highlight(id);
  }
  function detailOverview(id){
    const n=map.nodes.find(n=>n.id===id);if(!n)return;selected=id;const host=$('graph-detail');host.replaceChildren();
    host.append(el('div','eyebrow',n.external?'External mathematical input':'Mathematical proof step'),el('h2',null,n.title),el('p',null,n.summary));
    if(n.external)host.append(el('p','graph-detail-note','The paper supplies or cites this mathematical input. The linked Lean declarations state or consume its contract; they do not prove its existence.'));
    host.append(el('h3',null,'Read this step'));for(const id of n.paperAnchors)linkPaper(id,host);
    host.append(el('h3',null,'Lean components'));
    for(const id of n.lean){const item=el('article','graph-component');item.append(el('div','graph-full-name',id),btn('Source',()=>window.V4Trace.openLean(id,'source')),btn('Dependencies',()=>open('source',id)));host.append(item);}
    const incoming=map.edges.filter(e=>e.target===id),outgoing=map.edges.filter(e=>e.source===id);
    for(const [title,edges,field]of [['Uses',incoming,'source'],['Used for',outgoing,'target']])if(edges.length){
      host.append(el('h3',null,title));for(const e of edges){const other=map.nodes.find(n=>n.id===e[field]);host.append(btn(other.title,()=>detailOverview(other.id),'graph-paper-link'),el('p','graph-edge-meaning',e.meaning));}
    }
    highlight(id);
  }
  function detailGroup(node){
    const host=$('graph-detail');host.replaceChildren();selected=node.id;
    host.append(el('div','eyebrow','Grouped source references'),el('h2',null,short(node.id)),el('p','graph-full-name',node.id),
      el('p',null,node.members.length+' reached declarations in this module. A grouped edge means that at least one declaration references a declaration in the other group. This is not a module-import edge.'));
    const input=el('input');input.type='search';input.placeholder='Filter declarations in this group';input.setAttribute('aria-label','Filter grouped declarations');
    const list=el('div','graph-group-list'),draw=()=>{list.replaceChildren();const items=node.members.filter(id=>id.toLowerCase().includes(input.value.toLowerCase()));for(const id of items)list.append(btn(short(id),()=>detailCard(id),'graph-paper-link'));};
    input.addEventListener('input',draw);host.append(input,list);draw();highlight(node.id);
  }
  function detailEdge(edge){
    const host=$('graph-detail');host.replaceChildren();
    if(viewMode==='overview'){host.append(el('div','eyebrow','Mathematical dependence'),el('h2',null,map.nodes.find(n=>n.id===edge.source).title+' → '+map.nodes.find(n=>n.id===edge.target).title),el('p',null,edge.meaning),el('p','graph-detail-note','This arrow is a curated explanation of the mathematical proof, not a compiler-derived edge.'));return;}
    host.append(el('div','eyebrow','Recorded reference evidence'),el('h2',null,edge.pairs.length+' declaration pair'+(edge.pairs.length===1?'':'s')));
    const list=el('div','graph-edge-evidence');
    for(const [source,target]of edge.pairs){
      const d=g.cards.get(source),item=el('article','graph-component');item.append(el('p','graph-full-name',source+' → '+target));
      const occurrences=(d.referenceOccurrences||[]).filter(r=>r.target===target);
      item.append(el('p','graph-edge-meaning',occurrences.length+' recorded occurrence'+(occurrences.length===1?'':'s')));
      for(const r of occurrences){const line=(d.source||'').slice(r.offset,r.endOffset),p=el('p','graph-occurrence');p.append(el('strong',null,'Line '+r.line+', column '+(r.column+1)+' · '),el('code',null,line||target));item.append(p);}
      item.append(btn('Open referring source',()=>window.V4Trace.openLean(source,'source')),btn('Inspect referenced name',()=>detailCard(target)));list.append(item);
    }host.append(list);
  }
  function highlight(id){for(const n of document.querySelectorAll('#graph-canvas [data-graph-node]'))n.classList.toggle('selected',n.dataset.graphNode===id);}
  function words(text,max=29){const parts=text.replaceAll('_',' ').split(/\s+/),lines=[];let current='';for(const p of parts){if((current+' '+p).trim().length>max&&current){lines.push(current);current=p;}else current=(current+' '+p).trim();}if(current)lines.push(current);return lines.slice(0,2).map(s=>s.length>max?s.slice(0,max-1)+'…':s);}
  function drawGraph(nodes,edges,layout,overview){
    const frame=$('graph-canvas');frame.replaceChildren();svgSize=layout;
    const svg=svgEl('svg',{viewBox:'0 0 '+layout.width+' '+layout.height,role:'img','aria-label':overview?'Mathematical proof map':'Source reference graph'}),defs=svgEl('defs'),marker=svgEl('marker',{id:'proof-arrow-'+(++sequence),viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:7,markerHeight:7,orient:'auto-start-reverse'});marker.append(svgEl('path',{d:'M 0 0 L 10 5 L 0 10 z',fill:'#7894ae'}));defs.append(marker);svg.append(defs);
    for(const edge of edges){
      const a=layout.positions.get(edge.source),b=layout.positions.get(edge.target);if(!a||!b)continue;
      let d;
      if(overview){const x1=a.x+a.width/2,y1=a.y+a.height,x2=b.x+b.width/2,y2=b.y;d='M '+x1+' '+y1+' C '+x1+' '+(y1+38)+', '+x2+' '+(y2-38)+', '+x2+' '+y2;}
      else {const forward=b.x>a.x,x1=forward?a.x+a.width:a.x,y1=a.y+a.height/2,x2=forward?b.x:b.x+b.width,y2=b.y+b.height/2,bend=forward?48:-48;d='M '+x1+' '+y1+' C '+(x1+bend)+' '+y1+', '+(x2-bend)+' '+y2+', '+x2+' '+y2;}
      const edgeGroup=svgEl('g',{class:'proof-edge',tabindex:0,role:'button','aria-label':overview?edge.meaning:edge.pairs.length+' recorded declaration references'});
      const line=svgEl('path',{d,class:'proof-edge-line','marker-end':'url(#'+marker.id+')'}),hit=svgEl('path',{d,class:'proof-edge-hit'});
      edgeGroup.addEventListener('click',()=>detailEdge(edge));edgeGroup.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();detailEdge(edge);}});const title=svgEl('title');title.textContent=overview?edge.meaning:edge.source+' → '+edge.target;edgeGroup.append(title,line,hit);svg.append(edgeGroup);
    }
    for(const node of nodes){
      const p=layout.positions.get(node.id),group=svgEl('g',{class:'proof-node'+(node.external?' external':'')+(node.id==='result'?' conclusion':'')+(node.id===selected?' selected':''),transform:'translate('+p.x+','+p.y+')',tabindex:0,role:'button','aria-label':overview?node.title:node.label});group.dataset.graphNode=node.id;
      const rect=svgEl('rect',{width:p.width,height:p.height,rx:9});group.append(rect);
      const title=svgEl('title');title.textContent=overview?node.title:node.label;group.append(title);
      const label=overview?node.title:node.label.split('.').at(-1).replace(/([a-z0-9])([A-Z])/g,'$1 $2');const lines=words(label);
      lines.forEach((text,i)=>{const t=svgEl('text',{x:17,y:27+i*20,class:'proof-node-title'});t.textContent=text;group.append(t);});
      const caption=svgEl('text',{x:17,y:p.height-14,class:'proof-node-caption'});caption.textContent=overview?(node.external?'EXTERNAL INPUT':node.id==='result'?'MAIN THEOREM':'PROOF STEP'):node.members.length>1?node.members.length+' declarations':g.cards.get(node.members[0]).kind;group.append(caption);
      const action=()=>overview?detailOverview(node.id):options.grouped&&!pathIds?detailGroup(node):detailCard(node.members[0]);group.addEventListener('click',action);group.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();action();}});svg.append(group);
    }
    frame.append(svg);applyZoom();
  }
  function applyZoom(){const svg=$('graph-canvas').querySelector('svg');if(!svg||!svgSize)return;svg.style.width=svgSize.width*zoom+'px';svg.style.height=svgSize.height*zoom+'px';$('graph-zoom').textContent=Math.round(zoom*100)+'%';}
  function fit(){if(!svgSize)return;zoom=Math.max(.5,Math.min(1,($('graph-canvas').clientWidth-24)/svgSize.width));applyZoom();}
  function findPath(id){
    const p=G.path(g,g.root,id);if(!p){$('graph-message').textContent='No recorded source-reference path from the main theorem to this name. This does not establish mathematical independence.';return;}
    viewMode='source';$('graph-mode').value='source';$('source-controls').hidden=false;focus=g.root;pathIds=p;selected=id;render();$('graph-message').textContent='A shortest recorded-reference path: '+(p.length-1)+' edges. It is not a kernel proof-term trace.';detailCard(id);
  }
  function render(){
    $('graph-message').textContent='';const listing=$('graph-node-list');listing.replaceChildren();
    if(viewMode==='overview'){
      const positions=new Map(map.nodes.map(n=>[n.id,{x:32+n.lane*330,y:42+n.level*137,width:294,height:84}]));drawGraph(map.nodes,map.edges,{positions,width:1030,height:1300},true);
      $('graph-count').textContent=map.nodes.length+' mathematical steps · '+map.edges.length+' explanatory arrows · two direct external inputs';
      for(const n of map.nodes)listing.append(btn(n.title,()=>detailOverview(n.id),'graph-paper-link'));
      detailOverview(map.nodes.some(n=>n.id===selected)?selected:'result');
    }else{
      view=G.view(g,focus,{...options,pathIds,libraries:!!pathIds||options.libraries,grouped:!pathIds&&options.grouped,limit:pathIds?Infinity:options.limit});
      drawGraph(view.nodes,view.edges,G.layout(view.nodes),false);
      $('graph-focus').textContent=focus;
      $('graph-count').textContent='Showing '+view.nodes.length+' of '+view.groupCount+(view.grouped?' module groups':' cards')+' · '+view.edges.length+' visible / '+view.allEdges.length+(view.grouped?' eligible grouped arrows':' eligible edges')+' · '+view.edgePairs.length+' declaration-reference pairs (including within groups) · '+view.reached+' cards reached · '+view.filteredCards+' terminal cards filtered';
      for(const id of view.eligible)listing.append(btn(short(id),()=>detailCard(id),'graph-paper-link'));
      const full=g.cards.get(selected)?selected:focus;detailCard(full);
    }
    fit();
  }
  function download(){
    const payload=viewMode==='overview'?map:{relation:'compiler-recorded source references',focus,options,pathIds,eligibleDeclarations:view.eligible,edges:view.edgePairs,displayedNodes:view.nodes.map(n=>n.id),hiddenEdges:view.hiddenEdges};
    const blob=new Blob([JSON.stringify(payload,null,2)],{type:'application/json'}),a=el('a');a.href=URL.createObjectURL(blob);a.download=viewMode==='overview'?'mathematical-proof-map.json':'source-reference-neighborhood.json';a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);
  }
  function selectControl(id,label,values,value,action){
    const wrap=el('label','graph-control',label+' '),select=el('select');select.id=id;
    for(const [v,text]of values){const o=el('option',null,text);o.value=String(v);select.append(o);}select.value=String(value);select.addEventListener('change',()=>action(select.value));wrap.append(select);return wrap;
  }
  async function start(event){
    api=event.detail;g=G.index(api.DATA);focus=g.root;selected='result';
    try{const r=await fetch('proof-map.json');if(!r.ok)throw new Error('Proof map could not load');map=await r.json();}catch(error){console.error(error);return;}
    const main=el('section','graph-workspace');main.id='graph-workspace';main.hidden=true;
    const heading=el('div','graph-heading-row'),titles=el('div');titles.append(el('div','eyebrow','Explore the proof'),el('h2',null,'How the result fits together'));const sub=el('p');sub.id='graph-subtitle';titles.append(sub);
    const mode=selectControl('graph-mode','View',[['overview','Mathematical proof map'],['source','Lean source references']],'overview',switchView);heading.append(titles,mode);main.append(heading);
    const controls=el('div','source-controls');controls.id='source-controls';controls.hidden=true;
    const searchWrap=el('div','graph-search-wrap'),search=el('input'),results=el('div','graph-search-results');search.id='graph-search';search.type='search';search.placeholder='Find a theorem or definition…';search.setAttribute('aria-label','Find graph declaration');results.id='graph-search-results';results.hidden=true;
    const choose=id=>{focus=id;selected=id;pathIds=null;results.hidden=true;search.value='';render();};
    search.addEventListener('input',()=>{const query=search.value.toLowerCase().trim();results.replaceChildren();results.hidden=!query;if(!query)return;const matches=[...g.cards.values()].filter(d=>(d.id+' '+(d.plainEnglish||'')).toLowerCase().includes(query)).slice(0,30);for(const d of matches)results.append(btn(d.id,()=>choose(d.id),'graph-paper-link'));if(!matches.length)results.append(el('p',null,'No matching declaration.'));});
    search.addEventListener('keydown',e=>{if(e.key==='Escape')results.hidden=true;if(e.key==='Enter'){const first=results.querySelector('button');if(first)first.click();}});searchWrap.append(search,results);controls.append(searchWrap);
    controls.append(selectControl('graph-direction','Follow',[['out','References used'],['in','Declarations using this'],['both','Both directions']],'out',v=>{options.direction=v;pathIds=null;render();}),
      selectControl('graph-depth','Depth',[[1,'1 step'],[2,'2 steps'],[3,'3 steps'],[Infinity,'All reachable']],2,v=>{options.depth=Number(v);pathIds=null;render();}),
      selectControl('graph-limit','Display cap',[[40,'40'],[80,'80'],[160,'160']],80,v=>{options.limit=Number(v);render();}));
    for(const [id,text,key]of [['graph-grouped','Group by module','grouped'],['graph-libraries','Include terminal references','libraries']]){const label=el('label','graph-check'),input=el('input');input.id=id;input.type='checkbox';input.checked=options[key];input.addEventListener('change',()=>{options[key]=input.checked;pathIds=null;render();});label.append(input,document.createTextNode(text));controls.append(label);}
    controls.append(btn('Main theorem',()=>{choose(g.root);}),btn('Path from main theorem',()=>findPath(g.cards.has(selected)?selected:focus)));const name=el('div','graph-focus');name.id='graph-focus';controls.append(name);main.append(controls);
    const bar=el('div','graph-statusbar'),count=el('div');count.id='graph-count';count.setAttribute('role','status');bar.append(count);const zoomText=el('output');zoomText.id='graph-zoom';
    const zoomGroup=el('div','control-group');zoomGroup.setAttribute('role','group');zoomGroup.setAttribute('aria-label','Graph zoom');
    zoomGroup.append(btn('−',()=>{zoom=Math.max(.3,zoom-.1);applyZoom();}),zoomText,btn('+',()=>{zoom=Math.min(2.5,zoom+.1);applyZoom();}));
    bar.append(zoomGroup,btn('Fit width',fit),btn('Export this graph',download));main.append(bar);
    const message=el('p','graph-message');message.id='graph-message';message.setAttribute('role','status');main.append(message);
    const layout=el('div','graph-layout'),canvas=el('div','graph-canvas'),detail=el('aside','graph-detail');canvas.id='graph-canvas';canvas.tabIndex=0;canvas.setAttribute('aria-label','Graph canvas. Scroll to move, or drag empty canvas space.');detail.id='graph-detail';detail.setAttribute('aria-live','polite');layout.append(canvas,detail);main.append(layout);
    let pan=null;canvas.addEventListener('pointerdown',e=>{if(e.target.closest('[data-graph-node],.proof-edge'))return;pan={x:e.clientX,y:e.clientY,left:canvas.scrollLeft,top:canvas.scrollTop};canvas.setPointerCapture(e.pointerId);});canvas.addEventListener('pointermove',e=>{if(pan){canvas.scrollLeft=pan.left+pan.x-e.clientX;canvas.scrollTop=pan.top+pan.y-e.clientY;}});canvas.addEventListener('pointerup',()=>pan=null);canvas.addEventListener('pointercancel',()=>pan=null);
    const complete=el('details','graph-complete-list');complete.append(el('summary',null,'Complete eligible node list and graph data'));const list=el('div');list.id='graph-node-list';const full=el('a',null,'Download complete proof and reference index (.gz)');full.href='proof-data.json.gz';full.download='communication-complexity-proof-index.json.gz';complete.append(el('p',null,'The display cap affects only the drawing. This list includes every eligible declaration in the selected traversal; the full download also contains declarations outside that traversal.'),full,list);main.append(complete);
    $('workspace').before(main);const nav=btn('Dependency graph',()=>open('overview'));nav.id='open-proof-map';$('open-paper-trace').after(nav);
    document.addEventListener('v4-view-changed',e=>{const on=e.detail.mode==='graph';main.hidden=!on;nav.setAttribute('aria-pressed',String(on));});
    window.addEventListener('hashchange',()=>{const p=new URLSearchParams(location.hash.slice(1));if(p.get('view')==='graph')open(p.get('graph')==='source'?'source':'overview',p.get('focus'));});
    window.V4Graph={open,graph:g,getView:()=>view};
    const p=new URLSearchParams(initialHash.slice(1));if(p.get('view')==='graph')open(p.get('graph')==='source'?'source':'overview',p.get('focus'));
  }
  document.addEventListener('v4-inspector-ready',start,{once:true});
})();
