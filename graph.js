/* Two intentionally different relations: mathematical inputs and source
 * references — and, over both of them, one provenance model.
 *
 * PROVENANCE. Every Lean declaration in this index has exactly one origin,
 * read off its module:
 *
 *   this-paper     EthInapproximability.V4.*            proved in Lean here
 *   earlier-route  EthInapproximability.ParameterizedNP.*  reused from an
 *                                                       earlier route in this
 *                                                       repository
 *   companion      NPCC.* Workspace.* EthBridge.*       reused from the
 *                  LegacyNPCC.*                         companion paper's Lean
 *                                                       formalization
 *   library        Mathlib / Init / Lean / Batteries    library
 *
 * A fifth category is not a Lean declaration at all: an EXTERNAL INPUT, a
 * mathematical statement that no Lean proof in this project establishes. Those
 * are drawn dashed amber and always name where they come from.
 *
 * Colour carries origin and nothing else; the kind (theorem, def, …) is a mono
 * badge. */
(() => {
  'use strict';
  const initialHash=location.hash, G=window.ProofGraphCore;
  const $=id=>document.getElementById(id);
  const el=(tag,cls,text)=>{const n=document.createElement(tag);if(cls)n.className=cls;if(text!==undefined)n.textContent=text;return n;};
  const btn=(text,fn,cls)=>{const b=el('button',cls,text);b.type='button';b.addEventListener('click',fn);return b;};
  const svgEl=(tag,attrs={})=>{const n=document.createElementNS('http://www.w3.org/2000/svg',tag);for(const [k,v]of Object.entries(attrs))n.setAttribute(k,v);return n;};
  const short=id=>id.split('.').slice(-2).join('.');
  const count=n=>n.toLocaleString('en-GB');

  /* ------------------------------------------------------------------ *
   * The provenance model                                                *
   * ------------------------------------------------------------------ */
  const COMPANION=/^(NPCC|Workspace|EthBridge|LegacyNPCC)(\.|$)/;
  const ORIGIN_ORDER=['this-paper','companion','earlier-route','library'];
  const ORIGINS={
    'this-paper':{name:'This paper',mark:'THIS PAPER',colour:'var(--proved)',
      short:'Proved in Lean in this paper.',
      sentence:'Proved in Lean in this paper (EthInapproximability.V4.*). Kernel-checked as part of this development.'},
    companion:{name:'Companion paper',mark:'COMPANION PAPER',colour:'var(--reused)',
      short:'Reused from the companion paper’s Lean formalization.',
      /* %s is a specific vendored module where one is known, and the family of
       * vendored modules where the sentence describes the origin as a whole —
       * never an empty interpolation. */
      family:'modules NPCC.*, Workspace.*, EthBridge.* and LegacyNPCC.*',
      sentence:'Reused from the companion paper’s Lean formalization (vendored npcc-lean %s). Kernel-checked; not authored for this paper.'},
    'earlier-route':{name:'Earlier route',mark:'EARLIER ROUTE',colour:'var(--def)',
      short:'Reused from an earlier route in this repository.',
      sentence:'Reused from an earlier ETH-inapproximability route in this repository (EthInapproximability.ParameterizedNP.*), used here as a library.'},
    library:{name:'Library',mark:'LIBRARY',colour:'var(--faint)',
      short:'Library declaration (Mathlib / Lean core).',
      sentence:'A library declaration (Mathlib, Lean core or Batteries). Not authored for either paper.'},
    external:{name:'External input',mark:'EXTERNAL INPUT',colour:'var(--axiom)',
      short:'An external mathematical input — not proved in Lean.',
      sentence:'An external mathematical input. No Lean proof in this project establishes it; it enters the root theorem as an explicit hypothesis.'}
  };
  /* The module decides. `_private.` prefixes occur in declaration names, never
   * in module names, so the name is only a fallback. */
  function originOf(decl){
    const module=(decl&&decl.module)||((decl&&decl.id)||'').replace(/^_private\.([^.]+\.)*?/,'');
    if(module.startsWith('EthInapproximability.V4.'))return 'this-paper';
    if(module.startsWith('EthInapproximability.ParameterizedNP.'))return 'earlier-route';
    if(COMPANION.test(module))return 'companion';
    return 'library';
  }
  const originSentence=(origin,module)=>ORIGINS[origin].sentence.replace('%s',module?'module '+module:(ORIGINS[origin].family||''));
  /* A curated map node's origin is one of four presentation classes. */
  const nodeOrigin=node=>node.origin||(node.external?'external-companion':node.id==='result'?'result':'this-paper');
  const nodeClass=node=>({'this-paper':'o-this-paper','external-companion':'o-external','external-this-paper':'o-external',result:'o-result'})[nodeOrigin(node)];
  const nodeTick=node=>({'this-paper':'var(--proved)','external-companion':'var(--axiom)','external-this-paper':'var(--axiom)',result:'var(--headline)'})[nodeOrigin(node)];

  let api,g,map,viewMode='overview',focus,selected,view,zoom=1,pathIds=null,svgSize,sequence=0,closure,originTotals;
  const options={direction:'out',depth:2,limit:80,libraries:false,grouped:true};
  const originShown={'this-paper':true,'earlier-route':true,companion:true,library:false};
  const companionCache=new Map();

  /* Every companion-paper declaration a map step's Lean components reach
   * through compiler-recorded source references, grouped by vendored module. */
  function companionReach(node){
    if(companionCache.has(node.id))return companionCache.get(node.id);
    const hit=new Set();
    for(const id of node.lean||[]){
      if(!g.cards.has(id))continue;
      for(const reached of G.walk(g,id).keys())if(originOf(g.cards.get(reached))==='companion')hit.add(reached);
    }
    const modules=new Map();
    for(const name of [...hit].sort()){const m=g.cards.get(name).module;if(!modules.has(m))modules.set(m,[]);modules.get(m).push(name);}
    const result={count:hit.size,modules:[...modules.entries()].sort((a,b)=>a[0].localeCompare(b[0]))};
    companionCache.set(node.id,result);return result;
  }
  function originCounts(ids){
    const totals={'this-paper':0,companion:0,'earlier-route':0,library:0};
    for(const id of ids)totals[originOf(g.cards.get(id))]++;
    return totals;
  }
  /* The audited axiom footprint of the root theorem, read from the published
   * verification logs rather than asserted. */
  function rootAxioms(){
    const root=api.DATA.root,logs=(api.DATA.meta&&api.DATA.meta.verification&&api.DATA.meta.verification.logs)||[];
    for(const log of logs){
      const text=log.text||'',at=text.indexOf("'"+root+"' depends on axioms:");
      if(at<0)continue;
      const open=text.indexOf('[',at),close=text.indexOf(']',open);
      if(open<0||close<0)continue;
      return text.slice(open+1,close).split(',').map(s=>s.trim()).filter(Boolean);
    }
    return [];
  }

  /* ------------------------------------------------------------------ *
   * Views                                                               *
   * ------------------------------------------------------------------ */
  /* The hint states the reading direction of the drawing actually on screen.
   * The curated map is laid out by level, top to bottom: the two external
   * inputs are level 0 and the headline theorem is the last level. The source
   * graph is laid out by distance from the focused declaration, left to right,
   * one column per traversal step in whichever direction is selected. */
  function setHint(next){
    const hint=document.querySelector('#graph-workspace .hint');if(!hint)return;
    const lines=next==='overview'
      ?['drag to pan · scroll to zoom · click a step to inspect it','external inputs at the top → headline theorem at the bottom']
      :['drag to pan · scroll to zoom · click a card to inspect it','the focused declaration on the left → one traversal step per column to the right'];
    hint.replaceChildren(document.createTextNode(lines[0]),el('br'),document.createTextNode(lines[1]));
  }
  function switchView(next){
    viewMode=next;$('graph-mode').value=next;$('source-controls').hidden=next!=='source';
    setHint(next);
    /* The caption is a status-bar line now, not a heading paragraph: it names
     * the relation the arrows draw and nothing else. What the view is for is
     * said by the drawing; how to read it is said by the hint. */
    $('graph-subtitle').textContent=next==='overview'
      ?'arrows: curated mathematical dependence between steps of the papers'
      :'arrows: compiler-recorded source references, not dependencies extracted from kernel proof terms';
    for(const [id,mode]of [['route-curated','overview'],['route-source','source']])
      if($(id))$(id).setAttribute('aria-pressed',String(next===mode));
    render();
  }
  function open(mode='overview',id){
    if(!g)return;
    if(id&&(map.nodes.some(n=>n.id===id)||g.cards.has(id))){focus=g.cards.has(id)?id:focus;selected=id;pathIds=null;}
    window.V4Trace.setMode('graph');switchView(mode);
    try{history.replaceState(null,'','#'+new URLSearchParams({view:'graph',graph:mode,focus:focus}));}catch(_){}
  }
  function linkPaper(id,host){
    const a=api.DATA.trace.anchors.find(x=>x.id===id);if(!a)return;
    host.append(btn((a.paperId==='reader'?'Reader · ':'Formal · ')+a.title,()=>window.V4Trace.selectAnchor(id),'graph-paper-link'));
  }
  /* A Lean identifier in a heading breaks where the name breaks — after a '.'
   * or a '_' — rather than wherever the line happens to run out. Only a single
   * segment too long for the column is broken inside. */
  function leanHeading(text){
    const node=el('h2','lean-name');let piece='';
    for(const ch of text){
      piece+=ch;
      if(ch==='.'||ch==='_'){node.append(document.createTextNode(piece),document.createElement('wbr'));piece='';}
    }
    if(piece)node.append(document.createTextNode(piece));
    return node;
  }
  function originBadge(origin,host){
    const badge=el('span','badge o-'+origin,ORIGINS[origin].mark);host.append(badge);return badge;
  }
  function originLine(origin,module,host){
    const line=el('div','origin-line'),dot=el('span','origin-tick');
    dot.style.setProperty('--tick',ORIGINS[origin].colour);
    line.append(dot,el('span',null,ORIGINS[origin].name+' — '+originSentence(origin,module)));
    host.append(line);return line;
  }

  /* ---- detail: one Lean declaration in the source-reference relation ---- */
  function detailCard(id){
    selected=id;const d=g.cards.get(id),host=$('graph-detail'),origin=originOf(d);host.replaceChildren();
    host.append(el('div','eyebrow','Lean source · '+ORIGINS[origin].mark),leanHeading(short(id)));
    const badges=el('div','badges');originBadge(origin,badges);badges.append(el('span','badge',d.kind||'declaration'));host.append(badges);
    host.append(el('p','graph-full-name',id));
    originLine(origin,d.module,host);
    const prose=typeof d.plainEnglish==='string'?d.plainEnglish:d.plainEnglish&&d.plainEnglish.summary;
    if(prose)host.append(el('p',null,prose));
    host.append(el('p','graph-detail-note'+(origin==='companion'?' is-companion':''),G.isTerminal(d)?'This is a terminal reference card: its standalone source body is not embedded. That does not mean it has no mathematical dependencies.':'A source-indexed declaration. Its exact statement, surrounding definitions and available axiom evidence are in the Lean inspector.'));
    const counts=el('div','graph-stat-row');
    counts.append(el('span',null,g.out.get(id).length+' outgoing references'),el('span',null,g.incoming.get(id).length+' incoming references'));host.append(counts);
    const actions=el('div','graph-actions');
    actions.append(btn('Explore from here',()=>{focus=id;pathIds=null;options.grouped=false;$('graph-grouped').checked=false;render();}),
      btn('Open statement',()=>window.V4Trace.openLean(id,'statement')),
      btn('Full source and proof',()=>window.V4Trace.openLean(id,'source')),
      btn('Definition card',()=>api.openDeclarationCard(id)),
      btn('Path from main theorem',()=>findPath(id)));
    host.append(actions);
    if(d.traceAnchors&&d.traceAnchors.length){host.append(el('h3',null,'In the papers'));for(const a of d.traceAnchors)linkPaper(a,host);}
    const references=el('details');references.append(el('summary',null,'All direct references ('+g.out.get(id).length+')'));
    for(const target of g.out.get(id)){
      const row=btn(short(target),()=>detailEdge({source:id,target,pairs:[[id,target]]}),'graph-paper-link is-lean');
      const to=originOf(g.cards.get(target));row.dataset.origin=to;row.style.setProperty('--tick',ORIGINS[to].colour);
      references.append(row);
    }
    host.append(references);highlight(id);
  }

  /* ---- detail: one step of the curated mathematical map ---- */
  function detailOverview(id){
    const n=map.nodes.find(n=>n.id===id);if(!n)return;selected=id;const host=$('graph-detail'),origin=nodeOrigin(n);host.replaceChildren();
    host.append(el('div','eyebrow',map.originCaptions[origin]),el('h2',null,n.title));
    const badges=el('div','badges');
    if(n.external){originBadge('external',badges);badges.append(el('span','badge o-'+(origin==='external-companion'?'companion':'this-paper'),origin==='external-companion'?'INTENDED SOURCE · COMPANION PAPER':'PROVED ON PAPER · THIS PAPER'));}
    else if(origin==='result'){badges.append(el('span','badge o-result','ROOT THEOREM'),el('span','badge o-external','CONDITIONAL'));}
    else originBadge('this-paper',badges);
    host.append(badges,el('p',null,n.summary));
    if(n.external)host.append(el('p','graph-detail-note is-external','The paper supplies or cites this mathematical input. The linked Lean declarations state or consume its contract; they do not prove its existence.'));
    if(n.provenance)host.append(window.V4Trace.provenanceCard(n));
    host.append(el('h3',null,'Read this step'));for(const anchor of n.paperAnchors)linkPaper(anchor,host);
    host.append(el('h3',null,'Lean components'));
    for(const name of n.lean){
      const d=g.cards.get(name),origin=d?originOf(d):'library',item=el('article','graph-component');
      item.style.setProperty('--tick',ORIGINS[origin].colour);
      item.append(el('div','graph-full-name',name));
      const marks=el('div','badges');originBadge(origin,marks);if(d&&d.kind)marks.append(el('span','badge',d.kind));item.append(marks);
      item.append(btn('Open statement',()=>window.V4Trace.openLean(name,'statement')),btn('Source',()=>window.V4Trace.openLean(name,'source')),btn('Dependencies',()=>open('source',name)));
      host.append(item);
    }
    const reach=companionReach(n);
    if(reach.count){
      host.append(el('h3',null,'Uses companion-paper Lean · '+reach.count));
      const note=el('p','graph-detail-note is-companion',n.companionNote||'Following compiler-recorded source references from this step’s Lean components reaches '+reach.count+' declarations of the companion paper’s vendored Lean formalization, in '+reach.modules.length+' modules. They are reused, not proved here.');
      host.append(note,el('p','graph-full-name',map.companionPaper.citation));
      const list=el('div','companion-modules');
      for(const [module,names]of reach.modules){
        const block=el('details'),body=el('div','cm-body');
        const summary=el('summary',null,module);summary.append(el('span','cm-count','· '+names.length));
        block.append(summary,body);
        block.addEventListener('toggle',()=>{
          if(!block.open||body.childElementCount)return;
          for(const name of names){
            const row=el('div','cm-decl');row.append(el('span','n',name),btn('Open statement',()=>window.V4Trace.openLean(name,'statement')));
            body.append(row);
          }
        },false);
        list.append(block);
      }
      host.append(list);
    }
    const incoming=map.edges.filter(e=>e.target===id),outgoing=map.edges.filter(e=>e.source===id);
    for(const [title,edges,field]of [['Uses',incoming,'source'],['Used for',outgoing,'target']])if(edges.length){
      host.append(el('h3',null,title));
      for(const e of edges){
        const other=map.nodes.find(n=>n.id===e[field]),row=btn(other.title,()=>detailOverview(other.id),'graph-paper-link');
        row.dataset.origin=nodeOrigin(other);row.style.setProperty('--tick',nodeTick(other));
        host.append(row,el('p','graph-edge-meaning',e.meaning));
      }
    }
    highlight(id);markShortcut(id);
  }
  function detailGroup(node){
    const host=$('graph-detail');host.replaceChildren();selected=node.id;
    const origin=originOf(g.cards.get(node.members[0]));
    host.append(el('div','eyebrow','Grouped source references · '+ORIGINS[origin].mark),leanHeading(short(node.id)));
    const badges=el('div','badges');originBadge(origin,badges);badges.append(el('span','badge',node.members.length+' declarations'));host.append(badges);
    host.append(el('p','graph-full-name',node.id));
    originLine(origin,node.id,host);
    host.append(el('p',null,node.members.length+' reached declarations in this module. A grouped edge means that at least one declaration references a declaration in the other group. This is not a module-import edge.'));
    const input=el('input');input.type='search';input.placeholder='Filter declarations in this group';input.setAttribute('aria-label','Filter grouped declarations');
    const list=el('div','graph-group-list'),draw=()=>{list.replaceChildren();const items=node.members.filter(id=>id.toLowerCase().includes(input.value.toLowerCase()));for(const id of items){const row=btn(short(id),()=>detailCard(id),'graph-paper-link is-lean');row.dataset.origin=origin;row.style.setProperty('--tick',ORIGINS[origin].colour);list.append(row);}};
    input.addEventListener('input',draw);host.append(input,list);draw();highlight(node.id);
  }
  function detailEdge(edge){
    const host=$('graph-detail');host.replaceChildren();
    if(viewMode==='overview'){host.append(el('div','eyebrow','Curated mathematical dependence'),el('h2',null,map.nodes.find(n=>n.id===edge.source).title+' → '+map.nodes.find(n=>n.id===edge.target).title),el('p',null,edge.meaning),el('p','graph-detail-note','This arrow is a curated explanation of the mathematical proof, not a compiler-derived edge.'));return;}
    host.append(el('div','eyebrow','Recorded reference evidence'),el('h2',null,edge.pairs.length+' declaration pair'+(edge.pairs.length===1?'':'s')));
    const list=el('div','graph-edge-evidence');
    for(const [source,target]of edge.pairs){
      const d=g.cards.get(source),item=el('article','graph-component'),to=originOf(g.cards.get(target));
      item.style.setProperty('--tick',ORIGINS[to].colour);
      item.append(el('p','graph-full-name',source+' → '+target));
      const marks=el('div','badges');marks.append(el('span','badge o-'+originOf(d),ORIGINS[originOf(d)].mark),el('span','faint','→'),el('span','badge o-'+to,ORIGINS[to].mark));item.append(marks);
      const occurrences=(d.referenceOccurrences||[]).filter(r=>r.target===target);
      item.append(el('p','graph-edge-meaning',occurrences.length+' recorded occurrence'+(occurrences.length===1?'':'s')));
      for(const r of occurrences){const line=(d.source||'').slice(r.offset,r.endOffset),p=el('p','graph-occurrence');p.append(el('strong',null,'Line '+r.line+', column '+(r.column+1)+' · '),el('code',null,line||target));item.append(p);}
      item.append(btn('Open referring source',()=>window.V4Trace.openLean(source,'source')),btn('Inspect referenced name',()=>detailCard(target)));list.append(item);
    }host.append(list);
  }
  function highlight(id){for(const n of document.querySelectorAll('#graph-canvas [data-graph-node]'))n.classList.toggle('selected',n.dataset.graphNode===id);}
  function markShortcut(id){for(const b of document.querySelectorAll('.proofmap button[data-step]'))b.setAttribute('aria-pressed',String(b.dataset.step===id));}

  /* ------------------------------------------------------------------ *
   * Drawing                                                             *
   * ------------------------------------------------------------------ */
  const NODE_W=336,NODE_H=132,LANE=360,ROW=168,PAD=17;
  const CHIP_H=16,CHIP_CHAR=5.4,CHIP_PAD=7;
  function words(text,max=29){const parts=text.replaceAll('_',' ').split(/\s+/),lines=[];let current='';for(const p of parts){if((current+' '+p).trim().length>max&&current){lines.push(current);current=p;}else current=(current+' '+p).trim();}if(current)lines.push(current);return lines.slice(0,2).map(s=>s.length>max?s.slice(0,max-1)+'…':s);}
  /* A Lean identifier is a name, not prose, and a hard slice at column 30 cut
   * it mid-token ("…ExternalBala/ncednessRoot") or left a one-letter orphan.
   * It is broken where the name itself breaks — after a '.' or '_', or at a
   * camelCase boundary — the separator staying with the segment it closes. A
   * segment that still will not fit is middle-ellipsized rather than truncated,
   * so both ends stay readable; the complete name is always in the node's
   * <title> and in the aside. */
  function camelSplit(part){
    const out=[];let start=0;
    for(let i=1;i<part.length;i++){
      const previous=part[i-1],here=part[i];
      if(here>='A'&&here<='Z'&&((previous>='a'&&previous<='z')||(previous>='0'&&previous<='9'))){out.push(part.slice(start,i));start=i;}
    }
    out.push(part.slice(start));return out;
  }
  function middleClip(text,max){
    if(text.length<=max)return text;
    const head=Math.ceil((max-1)/2);
    return text.slice(0,head)+'…'+text.slice(text.length-(max-1-head));
  }
  function leanWrap(text,max=30,rows=2){
    const atoms=[];
    for(const segment of text.match(/[._]*[^._]+[._]*/g)||[text])for(const atom of camelSplit(segment))if(atom)atoms.push(atom);
    const lines=[];let line='';
    /* An atom of one or two characters never starts a line: it joins the one
     * before it even when that overruns by a character or two. */
    for(const atom of atoms){
      if(line&&line.length+atom.length>max&&atom.length>2){lines.push(line);line=atom;}
      else line+=atom;
    }
    if(line)lines.push(line);
    if(lines.length<=rows)return lines.map(l=>middleClip(l,max));
    return [...lines.slice(0,rows-1).map(l=>middleClip(l,max)),middleClip(lines.slice(rows-1).join(''),max)];
  }
  function chip(group,item,x,y){
    const width=Math.round(item.text.length*CHIP_CHAR)+2*CHIP_PAD;
    const box=svgEl('g',{class:'chip'+(item.cls?' '+item.cls:''),transform:'translate('+x+','+y+')'});
    box.append(svgEl('rect',{width,height:CHIP_H,rx:CHIP_H/2}));
    const text=svgEl('text',{x:CHIP_PAD,y:CHIP_H-5});text.textContent=item.text;box.append(text);
    if(item.title){const title=svgEl('title');title.textContent=item.title;box.append(title);}
    group.append(box);return width;
  }
  function paperChips(node){
    const chips=[];
    for(const paper of ['formal','reader']){
      const anchors=node.paperAnchors.map(id=>api.DATA.trace.anchors.find(a=>a.id===id)).filter(a=>a&&a.paperId===paper);
      if(!anchors.length)continue;
      const first=anchors[0],page=first.printedPage||first.page,extra=anchors.length-1;
      chips.push({text:(paper==='formal'?'Formal':'Reader')+' p.'+page+(extra?' +'+extra:''),title:anchors.map(a=>a.title+' (page '+a.page+')').join('\n')});
    }
    return chips;
  }
  function drawGraph(nodes,edges,layout,overview){
    const frame=$('graph-canvas');frame.replaceChildren();svgSize=layout;
    frame.classList.toggle('rel-source',!overview);
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
      const p=layout.positions.get(node.id);
      const origin=overview?nodeClass(node):'o-'+originOf(g.cards.get(node.members[0]));
      const group=svgEl('g',{class:'proof-node '+origin+(overview&&node.external?' external':'')+(overview&&node.id==='result'?' conclusion':'')+(node.id===selected?' selected':''),transform:'translate('+p.x+','+p.y+')',tabindex:0,role:'button','aria-label':overview?node.title+' — '+map.originCaptions[nodeOrigin(node)]:node.label});
      group.dataset.graphNode=node.id;
      group.append(svgEl('rect',{class:'card',width:p.width,height:p.height,rx:8}));
      const title=svgEl('title');title.textContent=overview?node.title+'\n'+map.originCaptions[nodeOrigin(node)]:node.label;group.append(title);
      const caption=svgEl('text',{x:PAD,y:22,class:'proof-node-caption'});
      caption.textContent=overview?map.originCaptions[nodeOrigin(node)]
        :ORIGINS[originOf(g.cards.get(node.members[0]))].mark+' · '+(node.members.length>1?node.members.length+' declarations':(g.cards.get(node.members[0]).kind||'declaration'));
      group.append(caption);
      const lines=overview?words(node.title,36):leanWrap(short(node.id),30);
      lines.forEach((text,i)=>{const t=svgEl('text',{x:PAD,y:48+i*21,class:'proof-node-title'+(overview?'':' is-lean')});t.textContent=text;group.append(t);});
      if(overview){
        let x=PAD;
        for(const item of paperChips(node))x+=chip(group,item,x,82)+6;
        const reach=companionReach(node);
        if(reach.count)chip(group,{text:'uses companion-paper Lean · '+reach.count,cls:'companion',title:map.companionPaper.citation+'\n'+reach.modules.length+' vendored modules reached'},PAD,104);
      }
      const action=()=>overview?detailOverview(node.id):options.grouped&&!pathIds?detailGroup(node):detailCard(node.members[0]);
      group.addEventListener('click',action);group.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();action();}});svg.append(group);
    }
    frame.append(svg);applyZoom();
  }
  function applyZoom(){const svg=$('graph-canvas').querySelector('svg');if(!svg||!svgSize)return;svg.style.width=svgSize.width*zoom+'px';svg.style.height=svgSize.height*zoom+'px';$('graph-zoom').textContent=Math.round(zoom*100)+'%';}
  function fit(){if(!svgSize)return;zoom=Math.max(.4,Math.min(1,($('graph-canvas').clientWidth-24)/svgSize.width));applyZoom();}
  function findPath(id){
    const p=G.path(g,g.root,id);if(!p){$('graph-message').textContent='No recorded source-reference path from the main theorem to this name. This does not establish mathematical independence.';return;}
    viewMode='source';$('graph-mode').value='source';$('source-controls').hidden=false;focus=g.root;pathIds=p;selected=id;render();$('graph-message').textContent='A shortest recorded-reference path: '+(p.length-1)+' edges. It is not a kernel proof-term trace.';detailCard(id);
  }
  function originSummary(ids,host){
    const totals=originCounts(ids);
    for(const origin of ORIGIN_ORDER){
      if(!totals[origin])continue;
      host.append(document.createTextNode(' · '));
      const mark=el('span','o o-'+origin,count(totals[origin])+' '+ORIGINS[origin].name.toLowerCase());
      mark.title=originSentence(origin,'');host.append(mark);
    }
  }
  function render(){
    $('graph-message').textContent='';const listing=$('graph-node-list');listing.replaceChildren();
    const counter=$('graph-count');counter.replaceChildren();
    if(viewMode==='overview'){
      const positions=new Map(map.nodes.map(n=>[n.id,{x:24+n.lane*LANE,y:36+n.level*ROW,width:NODE_W,height:NODE_H}]));
      drawGraph(map.nodes,map.edges,{positions,width:24+2*LANE+NODE_W+24,height:36+8*ROW+NODE_H+40},true);
      counter.append(document.createTextNode(map.nodes.length+' mathematical steps · '+map.edges.length+' curated arrows · 2 external inputs, both named'));
      for(const n of map.nodes){const row=btn(n.title,()=>detailOverview(n.id),'graph-paper-link');row.dataset.origin=nodeOrigin(n);row.style.setProperty('--tick',nodeTick(n));listing.append(row);}
      detailOverview(map.nodes.some(n=>n.id===selected)?selected:'result');
    }else{
      markShortcut(null);
      const raw=G.view(g,focus,{...options,pathIds,libraries:!!pathIds||options.libraries,grouped:!pathIds&&options.grouped,limit:Infinity});
      /* The origin filter runs before the display cap, so "Showing N of M"
       * keeps meaning "N drawn out of M that passed the filters". */
      const filtering=!pathIds;
      const eligible=filtering?raw.eligible.filter(id=>id===focus||originShown[originOf(g.cards.get(id))]):raw.eligible;
      const kept=new Set(eligible);
      const groups=filtering?raw.nodes.filter(n=>n.selected||n.members.some(id=>kept.has(id))):raw.nodes;
      const nodes=pathIds?groups:groups.slice(0,options.limit);
      const visible=new Set(nodes.map(n=>n.id)),eligibleGroups=new Set(groups.map(n=>n.id));
      const allEdges=raw.allEdges.filter(e=>(!filtering)||(eligibleGroups.has(e.source)&&eligibleGroups.has(e.target)));
      const edges=allEdges.filter(e=>visible.has(e.source)&&visible.has(e.target));
      const edgePairs=filtering?raw.edgePairs.filter(([s,t])=>kept.has(s)&&kept.has(t)):raw.edgePairs;
      view={nodes,edges,allEdges,eligible,edgePairs,reached:raw.reached,groupCount:groups.length,grouped:raw.grouped,hiddenEdges:allEdges.length-edges.length,filteredCards:raw.reached-eligible.length};
      drawGraph(nodes,edges,G.layout(nodes,{width:300,height:96}),false);
      $('graph-focus').textContent=focus;
      counter.append(document.createTextNode('Showing '+nodes.length+' of '+groups.length+(raw.grouped?' module groups':' cards')+' · '+edges.length+' visible / '+allEdges.length+(raw.grouped?' eligible grouped arrows':' eligible edges')+' · '+edgePairs.length+' declaration-reference pairs (including within groups) · '+raw.reached+' cards reached · '+(raw.reached-eligible.length)+' cards filtered out'));
      originSummary(eligible,counter);
      for(const id of eligible){const row=btn(short(id),()=>detailCard(id),'graph-paper-link is-lean'),origin=originOf(g.cards.get(id));row.dataset.origin=origin;row.style.setProperty('--tick',ORIGINS[origin].colour);listing.append(row);}
      const full=g.cards.get(selected)?selected:focus;detailCard(full);
    }
    fit();
  }
  function download(){
    const payload=viewMode==='overview'?map:{relation:'compiler-recorded source references',focus,options,originShown,pathIds,eligibleDeclarations:view.eligible,edges:view.edgePairs,displayedNodes:view.nodes.map(n=>n.id),hiddenEdges:view.hiddenEdges};
    const blob=new Blob([JSON.stringify(payload,null,2)],{type:'application/json'}),a=el('a');a.href=URL.createObjectURL(blob);a.download=viewMode==='overview'?'mathematical-proof-map.json':'source-reference-neighborhood.json';a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);
  }
  function selectControl(id,label,values,value,action){
    const wrap=el('label','graph-control',label+' '),select=el('select');select.id=id;
    for(const [v,text]of values){const o=el('option',null,text);o.value=String(v);select.append(o);}select.value=String(value);select.addEventListener('change',()=>action(select.value));wrap.append(select);return wrap;
  }

  /* ------------------------------------------------------------------ *
   * The command bar, shortcut strip, legend and footer                  *
   * ------------------------------------------------------------------ */
  function pill(cls,label){const box=el('div',cls);if(label)box.append(el('span','rlbl',label));return box;}
  function buildHeader(){
    const brand=document.querySelector('.brand'),bar=document.querySelector('.toolbar');
    brand.querySelector('.eyebrow').textContent='Lean-checked finite theorem · Lean 4';
    const sub=brand.querySelector('.small')||el('div','sub');sub.className='sub';
    sub.textContent=api.DATA.trace.papers.map(p=>p.title).join(' · ')+' — Communication complexity — paper ⇄ Lean inspector';
    if(!sub.parentElement)brand.append(sub);
    const caveat=el('div','sub scopecaveat');
    caveat.append(el('b',null,'Scope of the machine check: '),
      document.createTextNode('Lean proves the finite fixed-k gap and same-matrix size bound, conditional on two explicit external inputs: '),
      el('span','ext','the composed source theorem'),document.createTextNode(' (intended source: '),
      el('span','cmp','the companion paper'),document.createTextNode(') and '),
      el('span','ext','the balanced-family theorem'),
      document.createTextNode(' (proved in this paper, outside Lean). Runtime, effectivity and the ETH consequence are outside the formalized scope.'));
    /* Narrow headers clamp this to two lines, so the full sentence has to stay
     * reachable rather than silently truncated. */
    caveat.title=caveat.textContent;
    brand.append(caveat);

    const modes=pill('modes');modes.setAttribute('role','group');modes.setAttribute('aria-label','View');
    $('show-root').textContent='Lean source';$('show-root').title='Read the exact Lean declarations and their recorded references';
    $('open-paper-trace').textContent='📄 Papers';
    $('show-provenance').textContent='Verification';$('show-provenance').title='The verification record: proof snapshot, published logs and the audited axiom footprint';
    modes.append($('open-proof-map'),$('show-root'),$('open-paper-trace'));
    const routes=pill('routes','arrows');routes.setAttribute('role','group');routes.setAttribute('aria-label','Which arrows the graph draws');
    const curated=btn('curated',()=>open('overview'));curated.id='route-curated';curated.title='Arrows are the curated mathematical dependence between steps of the papers';
    const source=btn('source',()=>open('source'));source.id='route-source';source.title='Arrows are compiler-recorded source references between Lean declarations';
    routes.append(curated,source);

    const scale=document.querySelector('.scale-controls');scale.classList.add('uical');scale.prepend(el('span','ul','UI size'));

    const download=proofIndexButton();

    const search=el('div','searchbox');
    const input=el('input');input.id='top-search';input.type='search';input.autocomplete='off';input.spellcheck=false;
    input.placeholder='step, lemma, p.11…';input.setAttribute('aria-label','Search steps, paper locations and Lean declarations');
    const results=el('div','results');results.hidden=true;
    search.append(el('span','mark','⌕'),input,el('kbd',null,'/'),results);
    input.addEventListener('input',()=>runSearch(input,results));
    input.addEventListener('keydown',e=>{if(e.key==='Escape'){results.hidden=true;input.blur();}if(e.key==='Enter'){const first=results.querySelector('button');if(first)first.click();}});
    input.addEventListener('blur',()=>setTimeout(()=>{results.hidden=true;},180));

    /* One wrapping control row, not a row plus a nested group that wrapped
     * again: the record, help and navigation buttons are ordinary members. */
    bar.replaceChildren(modes,routes,scale,search,download,$('show-provenance'),$('show-help'),document.querySelector('.mobile-toggle'));

    const stats=el('div','stats');
    const rows=[['s-this-paper',closure['this-paper'],'this paper','Declarations proved in Lean in this paper (EthInapproximability.V4.*) and reached from the root theorem'],
      ['s-companion',closure.companion,'companion','Declarations reused from the companion paper’s vendored Lean formalization'],
      ['s-earlier-route',closure['earlier-route'],'earlier route','Declarations reused from EthInapproximability.ParameterizedNP.*'],
      ['s-library',closure.library,'library','Mathlib, Lean core and Batteries declarations'],
      ['s-external',2,'external inputs','The composed source theorem and the balanced-family theorem — neither is proved in Lean'],
      ['s-axioms',rootAxioms().length,'axioms','The audited axiom footprint of the root theorem: '+(rootAxioms().join(' · ')||'not recorded')]];
    for(const [cls,value,label,title]of rows){
      const stat=el('div','stat '+cls);stat.title=title;
      stat.append(el('b',null,count(value)),el('span',null,label));stats.append(stat);
    }
    /* The four provenance counts are a partition; say of what. */
    const denominator=el('span','stats-note','of '+count(closure.total)+' declarations in the root’s source-reference closure');
    denominator.title='Every declaration reachable from '+api.DATA.root+' through compiler-recorded source references. The external inputs and the axioms to its right are not part of that count.';
    stats.append(denominator);
    document.querySelector('.topbar').append(stats);
  }
  /* The compressed proof index, offered as a file. Its size is the transfer the
   * page itself already made, not a number typed into the markup; where the
   * server does not report one, the size is simply left out. */
  function indexSize(){
    if(!performance.getEntriesByType)return '';
    const entry=performance.getEntriesByType('resource').find(r=>/proof-data\.json\.gz$/.test(r.name));
    const bytes=entry&&(entry.encodedBodySize||entry.transferSize);
    return bytes?(bytes/1048576).toFixed(1)+' MB':'';
  }
  function proofIndexButton(){
    const link=el('a','dlbtn'),axioms=rootAxioms(),text=el('span','dl-tx');
    link.href='proof-data.json.gz';link.download='communication-complexity-proof-index.json.gz';
    text.append(el('b',null,'Proof index'),
      el('span',null,['.json.gz',indexSize(),axioms.length+' axioms'].filter(Boolean).join(' · ')));
    link.append(el('span','dl-ic','⬇'),text);
    link.title='Download the complete compiled proof and source-reference index this page reads: '+count(api.DATA.declarations.length)+' declarations, their exact Lean source and the published verification records. Audited axiom footprint of '+api.DATA.root+': '+(axioms.join(' · ')||'not recorded')+'.';
    return link;
  }
  function runSearch(input,results){
    const query=input.value.toLowerCase().trim();results.replaceChildren();results.hidden=!query;if(!query)return;
    const page=query.match(/^p\.?\s*(\d+)$/);
    const add=(label,items)=>{if(!items.length)return;results.append(el('div','rgroup',label));for(const item of items)results.append(item);};
    add('Proof map steps',map.nodes.filter(n=>(n.title+' '+n.summary+' '+n.id).toLowerCase().includes(query)).slice(0,6)
      .map(n=>{const row=btn(n.title,()=>{input.value='';results.hidden=true;open('overview',n.id);},'graph-paper-link');row.dataset.origin=nodeOrigin(n);row.style.setProperty('--tick',nodeTick(n));row.append(el('span','meta',map.originCaptions[nodeOrigin(n)]));return row;}));
    add('Paper locations',api.DATA.trace.anchors.filter(a=>page?a.page===Number(page[1]):(a.title+' '+a.label).toLowerCase().includes(query)).slice(0,8)
      .map(a=>{const row=btn(a.title,()=>{input.value='';results.hidden=true;window.V4Trace.selectAnchor(a.id);},'trace-index-item');row.dataset.classification=a.classification;row.style.setProperty('--tick',a.classification==='external'?'var(--hl-external)':a.classification==='assembled'?'var(--hl-assembled)':a.classification==='unmapped'?'var(--hl-unmapped)':a.classification==='context'?'var(--hl-context)':'var(--hl-statement)');row.append(el('span','meta',(a.paperId==='reader'?'Reader':'Formal')+' · page '+a.page));return row;}));
    add('Lean declarations',[...g.cards.values()].filter(d=>d.id.toLowerCase().includes(query)).slice(0,10)
      .map(d=>{const origin=originOf(d),row=btn(short(d.id),()=>{input.value='';results.hidden=true;open('source',d.id);},'graph-paper-link is-lean');row.dataset.origin=origin;row.style.setProperty('--tick',ORIGINS[origin].colour);row.append(el('span','meta',ORIGINS[origin].name+' · '+d.module));return row;}));
    if(!results.childElementCount)results.append(el('p','none','Nothing matches that.'));
  }
  function buildShortcuts(){
    const strip=document.querySelector('.scope-strip');if(!strip)return;
    strip.className='proofmap';strip.setAttribute('role','navigation');strip.setAttribute('aria-label','Shortcuts through the curated proof map');strip.replaceChildren();
    const label=el('span','pm-label');label.append(el('b',null,'Proof shortcuts'),el('small',null,'external inputs → headline'));
    strip.append(label);
    const order=[...map.nodes].sort((a,b)=>a.level-b.level||a.lane-b.lane);
    order.forEach((n,i)=>{
      const b=btn('',()=>open('overview',n.id));b.dataset.step=n.id;b.dataset.origin=nodeOrigin(n);
      b.setAttribute('aria-pressed','false');b.title=n.title+' — '+map.originCaptions[nodeOrigin(n)];
      const copy=el('span','pm-copy');copy.append(el('b',null,n.milestone.label),el('small',null,n.milestone.note));
      b.append(el('span','pm-num',String(i+1)),copy);strip.append(b);
    });
  }
  /* A key, not a paragraph: one short label per row, the full sentence on the
   * row's own tooltip, and the standing caveat on the box. It sits over the
   * canvas, so every line it grows costs drawing area. */
  function buildLegend(){
    const box=el('div','legend');box.setAttribute('aria-label','What the colours and arrows mean');
    box.title='Colour carries provenance and nothing else; the kind of declaration is a badge. A dashed amber card is an external input — stated, consumed, and not proved in Lean.';
    box.append(el('div','lg-t','Provenance'));
    const rows=[['var(--proved)','This paper',false,'Proved in Lean in this paper (EthInapproximability.V4.*).'],
      ['var(--reused)','Companion paper',true,'Reused from the companion paper’s vendored Lean formalization (NPCC.*, Workspace.*, EthBridge.*, LegacyNPCC.*).'],
      ['var(--def)','Earlier route',false,'Reused from an earlier route in this repository (EthInapproximability.ParameterizedNP.*).'],
      ['var(--axiom)','External input',true,'A mathematical input no Lean proof here establishes; it enters the root theorem as an explicit hypothesis.'],
      ['var(--faint)','Library',false,'Mathlib, Lean core or Batteries.']];
    for(const [colour,text,dashed,title]of rows){
      const row=el('div','row'+(dashed?' is-dashed':'')),swatch=el('span','sw');
      row.title=title;swatch.style.setProperty('--tick',colour);row.append(swatch,el('span',null,text));box.append(row);
    }
    const arrows=el('div','rt');
    for(const [cls,text,title]of [['','Curated mathematics','An arrow of the curated mathematical map: an ingredient of the step it points to.'],
      ['dashed','Source reference','A compiler-recorded source reference between Lean declarations, not a kernel proof-term dependency.']]){
      const row=el('div','row');row.title=title;row.append(el('span','rule '+cls),el('span',null,text));arrows.append(row);
    }
    box.append(arrows);return box;
  }
  function buildFooter(){
    const axioms=rootAxioms(),foot=el('footer','sitefoot');
    foot.append(el('b',null,'Axiom footprint:'),el('span','axfoot',axioms.join(' · ')||'not recorded'),
      el('b',null,'External inputs:'),el('span','extfoot','composed source theorem · balanced-family theorem'),
      el('span',null,map.nodes.length+' map steps · '+count(closure.total)+' declarations in the root closure'),
      el('span','spacer'),
      btn('Verification record',()=>$('show-provenance').click()));
    foot.title='Recorded by #print axioms on '+api.DATA.root;
    document.body.append(foot);
  }
  /* The Lean navigation rows are built by the offline template; the origin
   * tick is added here as they appear. */
  function decorateNavigation(){
    const list=$('nav-list');if(!list)return;
    const tag=()=>{for(const row of list.querySelectorAll('.decl-row[data-id]')){
      const d=g.cards.get(row.dataset.id);if(!d||row.dataset.origin)continue;
      const origin=originOf(d);row.dataset.origin=origin;row.style.setProperty('--tick',ORIGINS[origin].colour);
      row.title=row.title+'\n'+originSentence(origin,d.module);
    }};
    tag();new MutationObserver(tag).observe(list,{childList:true});
  }

  async function start(event){
    api=event.detail;g=G.index(api.DATA);focus=g.root;selected='result';
    window.V4Origin=originOf;
    const reachable=[...G.walk(g,g.root).keys()];
    closure=originCounts(reachable);closure.total=reachable.length;
    try{const r=await fetch('proof-map.json');if(!r.ok)throw new Error('Proof map could not load');map=await r.json();}catch(error){console.error(error);return;}
    window.V4ProofMap=map;
    const main=el('section','graph-workspace');main.id='graph-workspace';main.hidden=true;
    /* No page heading between the shortcut strip and the drawing — the
     * reference spends none, and an eyebrow, an h2 and a paragraph measured
     * 154px of chrome that the canvas had to give up at short viewports. The
     * view selector and the relation caption move into the status bar, which
     * is the one line of chrome this view keeps above the canvas. */
    const mode=selectControl('graph-mode','View',[['overview','Mathematical proof map'],['source','Lean source references']],'overview',switchView);
    const controls=el('div','source-controls');controls.id='source-controls';controls.hidden=true;
    const searchWrap=el('div','graph-search-wrap'),search=el('input'),results=el('div','graph-search-results');search.id='graph-search';search.type='search';search.placeholder='Find a theorem or definition…';search.setAttribute('aria-label','Find graph declaration');results.id='graph-search-results';results.hidden=true;
    const choose=id=>{focus=id;selected=id;pathIds=null;results.hidden=true;search.value='';render();};
    search.addEventListener('input',()=>{const query=search.value.toLowerCase().trim();results.replaceChildren();results.hidden=!query;if(!query)return;const matches=[...g.cards.values()].filter(d=>(d.id+' '+(d.plainEnglish||'')).toLowerCase().includes(query)).slice(0,30);for(const d of matches){const origin=originOf(d),row=btn(d.id,()=>choose(d.id),'graph-paper-link');row.dataset.origin=origin;row.style.setProperty('--tick',ORIGINS[origin].colour);results.append(row);}if(!matches.length)results.append(el('p',null,'No matching declaration.'));});
    search.addEventListener('keydown',e=>{if(e.key==='Escape')results.hidden=true;if(e.key==='Enter'){const first=results.querySelector('button');if(first)first.click();}});searchWrap.append(search,results);controls.append(searchWrap);
    controls.append(selectControl('graph-direction','Follow',[['out','References used'],['in','Declarations using this'],['both','Both directions']],'out',v=>{options.direction=v;pathIds=null;render();}),
      selectControl('graph-depth','Depth',[[1,'1 step'],[2,'2 steps'],[3,'3 steps'],[Infinity,'All reachable']],2,v=>{options.depth=Number(v);pathIds=null;render();}),
      selectControl('graph-limit','Display cap',[[40,'40'],[80,'80'],[160,'160']],80,v=>{options.limit=Number(v);render();}));
    const grouped=el('label','graph-check'),groupedInput=el('input');groupedInput.id='graph-grouped';groupedInput.type='checkbox';groupedInput.checked=options.grouped;
    groupedInput.addEventListener('change',()=>{options.grouped=groupedInput.checked;pathIds=null;render();});
    grouped.append(groupedInput,document.createTextNode('Group by module'));controls.append(grouped);
    /* The origin filter. "Library" is also the terminal-reference switch the
     * traversal itself takes, so the two stay one control. */
    const filter=el('div','origin-filter');filter.setAttribute('role','group');filter.setAttribute('aria-label','Filter by provenance');
    filter.append(el('span','oflabel','origin'));
    for(const origin of ORIGIN_ORDER){
      const wrap=el('label','graph-check'),box=el('input'),dot=el('span','origin-tick');
      box.type='checkbox';box.checked=originShown[origin];
      box.id=origin==='library'?'graph-libraries':'graph-origin-'+origin;
      dot.style.setProperty('--tick',ORIGINS[origin].colour);
      wrap.title=originSentence(origin,'');
      box.addEventListener('change',()=>{originShown[origin]=box.checked;if(origin==='library')options.libraries=box.checked;pathIds=null;render();});
      wrap.append(box,dot,document.createTextNode(origin==='library'?'library and terminal references':ORIGINS[origin].name.toLowerCase()));
      filter.append(wrap);
    }
    controls.append(filter);
    controls.append(btn('Main theorem',()=>{choose(g.root);}),btn('Path from main theorem',()=>findPath(g.cards.has(selected)?selected:focus)));const name=el('div','graph-focus');name.id='graph-focus';controls.append(name);main.append(controls);
    const bar=el('div','graph-statusbar'),counter=el('div');counter.id='graph-count';counter.setAttribute('role','status');
    const sub=el('p','graph-subtitle');sub.id='graph-subtitle';
    /* View selector, then what is drawn, then the caption saying what the
     * arrows mean, then the zoom pill and the export. One strip. */
    bar.append(mode,counter,sub);const zoomText=el('output');zoomText.id='graph-zoom';
    const zoomGroup=el('div','control-group');zoomGroup.setAttribute('role','group');zoomGroup.setAttribute('aria-label','Graph zoom');
    /* "Fit width" resets the zoom, so it joins the pill as a fourth child. */
    zoomGroup.append(btn('−',()=>{zoom=Math.max(.3,zoom-.1);applyZoom();}),zoomText,btn('+',()=>{zoom=Math.min(2.5,zoom+.1);applyZoom();}),btn('Fit width',fit));
    bar.append(zoomGroup,btn('Export this graph',download));main.append(bar);
    const message=el('p','graph-message');message.id='graph-message';message.setAttribute('role','status');main.append(message);
    const layout=el('div','graph-layout'),wrap=el('div','canvas-wrap'),canvas=el('div','graph-canvas'),detail=el('aside','graph-detail');canvas.id='graph-canvas';canvas.tabIndex=0;canvas.setAttribute('aria-label','Graph canvas. Scroll to move, or drag empty canvas space.');detail.id='graph-detail';detail.setAttribute('aria-live','polite');
    const fab=el('div','fab');fab.append(btn('Fit',fit),btn('Headline theorem →',()=>{if(viewMode==='overview')detailOverview('result');else choose(g.root);}));
    wrap.append(canvas,el('div','hint','drag to pan · scroll to zoom · click a step to inspect it'),buildLegend(),fab);
    layout.append(wrap,detail);main.append(layout);
    let pan=null;canvas.addEventListener('pointerdown',e=>{if(e.target.closest('[data-graph-node],.proof-edge'))return;pan={x:e.clientX,y:e.clientY,left:canvas.scrollLeft,top:canvas.scrollTop};canvas.setPointerCapture(e.pointerId);});canvas.addEventListener('pointermove',e=>{if(pan){canvas.scrollLeft=pan.left+pan.x-e.clientX;canvas.scrollTop=pan.top+pan.y-e.clientY;}});canvas.addEventListener('pointerup',()=>pan=null);canvas.addEventListener('pointercancel',()=>pan=null);
    const complete=el('details','graph-complete-list');complete.append(el('summary',null,'Complete eligible node list and graph data'));const list=el('div');list.id='graph-node-list';const full=el('a',null,'Download complete proof and reference index (.gz)');full.href='proof-data.json.gz';full.download='communication-complexity-proof-index.json.gz';complete.append(el('p',null,'The display cap affects only the drawing. This list includes every eligible declaration in the selected traversal; the full download also contains declarations outside that traversal.'),full,list);main.append(complete);
    /* The pill names the VIEW, not one of its two relations: it stays pressed
     * while the view is open, and the arrows group next to it says which
     * relation is drawn. Labelling it "Proof map" contradicted its own pressed
     * state as soon as the Lean source graph was selected. */
    $('workspace').before(main);const nav=btn('Graph',()=>open('overview'));nav.id='open-proof-map';nav.title='The dependency explorer: the curated mathematical proof map, and the Lean source-reference graph';$('open-paper-trace').after(nav);
    buildHeader();buildShortcuts();buildFooter();decorateNavigation();
    document.addEventListener('v4-view-changed',e=>{const on=e.detail.mode==='graph';main.hidden=!on;nav.setAttribute('aria-pressed',String(on));if(!on)markShortcut(null);});
    document.addEventListener('v4-declaration-selected',e=>{
      const d=g.cards.get(e.detail.id);if(!d)return;const origin=originOf(d),host=$('selected-badges');
      const badge=el('span','badge o-'+origin,ORIGINS[origin].mark);badge.title=originSentence(origin,d.module);host.prepend(badge);
    });
    /* "/" belongs to whichever view is open: the paper index (claimed by
     * trace.js), the Lean navigation (claimed by the offline template) or,
     * on the map, this command bar. Stopping propagation in the capture phase
     * keeps the template's own document-level handler from also firing. */
    document.addEventListener('keydown',e=>{
      const typing=e.target instanceof Element&&e.target.matches('input,textarea,select,[contenteditable=true]');
      if(e.key!=='/'||typing)return;
      if(!$('workspace').hidden)return;
      e.preventDefault();e.stopPropagation();$('top-search').focus();$('top-search').select();
    },true);
    window.addEventListener('hashchange',()=>{const p=new URLSearchParams(location.hash.slice(1));if(p.get('view')==='graph')open(p.get('graph')==='source'?'source':'overview',p.get('focus'));});
    window.V4Graph={open,graph:g,getView:()=>view,origin:originOf};
    window.V4Trace.refresh();
    const p=new URLSearchParams(initialHash.slice(1));
    if(p.get('view')==='graph')open(p.get('graph')==='source'?'source':'overview',p.get('focus'));
    else if(!p.has('anchor')&&!p.has('decl')&&!p.has('paper'))open('overview');
  }
  document.addEventListener('v4-inspector-ready',start,{once:true});
})();
