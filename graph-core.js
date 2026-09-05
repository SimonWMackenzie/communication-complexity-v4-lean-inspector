/* Pure graph operations. Source references may contain cycles. */
(function(root,factory){const api=factory();if(typeof module==='object'&&module.exports)module.exports=api;else root.ProofGraphCore=api;})(typeof globalThis!=='undefined'?globalThis:this,()=>{
  'use strict';
  const uniq=xs=>[...new Set(xs)];
  function index(data){
    const cards=new Map(data.declarations.map(d=>[d.id,d])),out=new Map(),incoming=new Map();
    for(const id of cards.keys())incoming.set(id,[]);
    for(const [id,d] of cards){const deps=uniq((d.dependencies||[]).map(x=>typeof x==='string'?x:x.target||x.id));for(const target of deps){if(!cards.has(target))throw new Error('Unresolved graph target: '+target);incoming.get(target).push(id);}out.set(id,deps);}
    return {cards,out,incoming,root:data.root};
  }
  function walk(g,start,{direction='out',depth=Infinity}={}){
    if(!g.cards.has(start))throw new Error('Unknown graph start');
    const distance=new Map([[start,0]]),queue=[start];
    for(let i=0;i<queue.length;i++){const id=queue[i],level=distance.get(id);if(level>=depth)continue;
      const next=direction==='out'?g.out.get(id):direction==='in'?g.incoming.get(id):uniq([...g.out.get(id),...g.incoming.get(id)]);
      for(const n of next)if(!distance.has(n)){distance.set(n,level+1);queue.push(n);}
    }return distance;
  }
  function path(g,start,target){
    if(!g.cards.has(start)||!g.cards.has(target))return null;
    const previous=new Map([[start,null]]),queue=[start];
    for(let i=0;i<queue.length;i++){const id=queue[i];if(id===target){const result=[];for(let n=target;n!==null;n=previous.get(n))result.push(n);return result.reverse();}for(const n of g.out.get(id))if(!previous.has(n)){previous.set(n,id);queue.push(n);}}
    return null;
  }
  function isTerminal(d){return d.status==='library-reference'||d.status==='reference-only'||d.kind==='library-reference'||d.kind==='generated-reference'||!d.source;}
  function view(g,start,{direction='out',depth=2,limit=80,libraries=false,grouped=false,pathIds=null}={}){
    const distance=pathIds?new Map(pathIds.map((id,i)=>[id,i])):walk(g,start,{direction,depth});
    const eligible=[...distance.keys()].filter(id=>id===start||libraries||!isTerminal(g.cards.get(id)));
    const allowed=new Set(eligible),edgePairs=[];
    for(const id of eligible)for(const target of g.out.get(id))if(allowed.has(target)&&(!pathIds||pathIds.indexOf(target)===pathIds.indexOf(id)+1))edgePairs.push([id,target]);
    const groups=new Map(),groupOf=new Map();
    for(const id of eligible){const d=g.cards.get(id),key=grouped?(d.module||'[library references]'):id;groupOf.set(id,key);if(!groups.has(key))groups.set(key,{id:key,label:grouped?key:id,members:[],distance:distance.get(id),selected:false});const node=groups.get(key);node.members.push(id);node.distance=Math.min(node.distance,distance.get(id));if(id===start)node.selected=true;}
    const sorted=[...groups.values()].sort((a,b)=>Number(b.selected)-Number(a.selected)||a.distance-b.distance||a.id.localeCompare(b.id));
    const nodes=sorted.slice(0,limit),visible=new Set(nodes.map(n=>n.id)),allEdges=new Map();
    for(const [source,target]of edgePairs){const s=groupOf.get(source),t=groupOf.get(target);if(s===t&&grouped)continue;const key=JSON.stringify([s,t]);if(!allEdges.has(key))allEdges.set(key,{source:s,target:t,pairs:[]});allEdges.get(key).pairs.push([source,target]);}
    const edges=[...allEdges.values()].filter(e=>visible.has(e.source)&&visible.has(e.target));
    return {nodes,edges,allEdges:[...allEdges.values()],eligible,edgePairs,reached:distance.size,eligibleCount:eligible.length,groupCount:groups.size,hiddenGroups:groups.size-nodes.length,hiddenEdges:allEdges.size-edges.length,filteredCards:distance.size-eligible.length,grouped};
  }
  function layout(nodes,{width=290,height=86,gapX=90,gapY=26}={}){
    const layers=new Map();for(const n of nodes){if(!layers.has(n.distance))layers.set(n.distance,[]);layers.get(n.distance).push(n);}
    const keys=[...layers.keys()].sort((a,b)=>a-b),maxRows=Math.max(1,...[...layers.values()].map(x=>x.length)),positions=new Map();
    keys.forEach((key,col)=>{const layer=layers.get(key);layer.forEach((n,row)=>positions.set(n.id,{x:36+col*(width+gapX),y:52+row*(height+gapY),width,height}));});
    return {positions,width:72+keys.length*(width+gapX)-gapX,height:100+maxRows*(height+gapY)-gapY};
  }
  return {index,walk,path,view,layout,isTerminal};
});
