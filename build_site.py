"""Build the retained static inspector; no network or proof-repository write."""
import gzip
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parent

def transform(template):
    template = template.replace('</head>', '<link rel="stylesheet" href="trace.css">\n<link rel="stylesheet" href="design.css">\n</head>')
    template = template.replace('saved<=180', 'saved<=200').replace('scale>=180', 'scale>=200').replace('Math.min(180,scale+10)', 'Math.min(200,scale+10)')
    template = template.replace('function applyScale(){', 'function applyScale(){document.documentElement.classList.toggle("large-text",scale>=150);')
    template = template.replace('Communication complexity / V4', 'Communication complexity')
    template = template.replace('Finite gap and size · Lean inspector</h1>', 'A communication gap, formally proved</h1>')
    template = template.replace('<script id="inspector-data" type="application/json">__INSPECTOR_DATA__</script>', '<script src="trace.js"></script>\n<script src="graph-core.js"></script>\n<script src="graph.js"></script>')
    template = template.replace('(() => {', '(async () => {', 1)
    old = 'try { DATA = JSON.parse($("inspector-data").textContent);'
    new = '''try {
    const response = await fetch("proof-data.json.gz");
    if (!response.ok) throw new Error("Could not load the proof index (HTTP " + response.status + ").");
    if (typeof DecompressionStream === "undefined") throw new Error("Please use a current browser with gzip decompression support.");
    const stream = response.body.pipeThrough(new DecompressionStream("gzip"));
    DATA = JSON.parse(await new Response(stream).text());
    document.getElementById("load-proof").hidden = true;'''
    if old not in template:
        raise ValueError('Original inspector bootstrap changed')
    template = template.replace(old, new, 1)
    template = template.replace('<div id="fatal"', '<div id="load-proof" class="trace-loading" role="status">Loading the paper and compiled proof index...</div>\n<div id="fatal"')
    template = template.replace('catch (error) { $("workspace").hidden', 'catch (error) { $("load-proof").hidden = true; $("workspace").hidden', 1)
    template = template.replace("This inspector has not been built, or its embedded data is invalid. Rebuild it with the repository's inspector builder. Details:", 'The proof index could not be opened. Reload the page or try a current browser. Details:')
    old_end = 'applyScale();fillFilters();renderIntro();renderNavigation();selectDeclaration((declarationFromLocation()||root).id,"statement",false);'
    new_end = old_end + '\n  window.V4Inspector = {DATA, byId, selectDeclaration, openDeclarationCard, renderCode, renderValue};\n  document.dispatchEvent(new CustomEvent("v4-inspector-ready", {detail: window.V4Inspector}));'
    if old_end not in template:
        raise ValueError('Original inspector integration point changed')
    template = template.replace(old_end, new_end, 1)
    for fn in ('renderStatement', 'renderSource'):
        template = template.replace('function ' + fn + '(d,host) {', 'function ' + fn + '(d,host) {\n    if(window.V4Trace)window.V4Trace.addLinks(d,host);', 1)
    template = template.replace('function renderProvenance(d,host) {', 'function renderProvenance(d,host) {\n    if(meta.paperRevision){const revision=section(host,"Revised paper edition");revision.append(el("p","notice",meta.paperRevision.notice));const a=el("a",null,"Download the separate paper source/PDF receipt");a.href="paper-revision.json";revision.append(a);renderValue({edition:meta.paperRevision.receipt.edition,receiptSha256:meta.paperRevision.receiptSha256,scope:meta.paperRevision.receipt.scope,papers:meta.paperRevision.receipt.papers},revision);}', 1)
    template = template.replace('Recorded manuscript correspondence for this declaration', 'Original proof-snapshot manuscript annotations (historical)')
    template = template.replace('function renderDependencies(d,host) {', 'function renderDependencies(d,host) {\n    if(window.V4Graph)host.append(button("Open dependency explorer",()=>window.V4Graph.open("source",d.id)));', 1)
    template = template.replace('    setTab(currentTab);', '    setTab(currentTab);\n    document.dispatchEvent(new CustomEvent("v4-declaration-selected", {detail: {id:d.id}}));', 1)
    template = template.replace('This is a self-contained, offline reading aid.', 'This is a public reading aid for a pinned proof-and-paper snapshot.')
    template = template.replace('No network request is needed to use the inspector.', 'The papers and compressed proof index are served with this site.')
    template = template.replace('<title>V4 finite gap and size · Lean inspector</title>', '<title>Paper and Lean | Communication complexity</title>\n<meta name="description" content="Read both finite communication gap-and-size papers and follow highlighted statements into their Lean formalization, with explicit external assumptions.">')
    if '__INSPECTOR_DATA__' in template:
        raise ValueError('Unresolved payload placeholder')
    return template

def build():
    dist = ROOT / 'dist'
    dist.mkdir(exist_ok=True)
    data = json.loads(gzip.decompress((ROOT / 'inputs/proof-data.json.gz').read_bytes()))
    snapshot = json.loads((ROOT / 'inputs/snapshot.json').read_text())
    actual = hashlib.sha256((ROOT / 'inputs/proof-data.json.gz').read_bytes()).hexdigest()
    assert actual == snapshot['proofPayloadSha256'], 'Snapshot payload changed'
    html = transform((ROOT / 'template.html').read_text(encoding='utf-8'))
    (dist / 'index.html').write_text(html, encoding='utf-8', newline='\n')
    for name in ('trace.js', 'trace.css', 'design.css', 'graph-core.js', 'graph.js'):
        shutil.copyfile(ROOT / name, dist / name)
    overview=json.loads((ROOT/'proof-map.json').read_text(encoding='utf-8'))
    anchors={a['id']:a for a in data['trace']['anchors']}
    names={d['id'] for d in data['declarations']}
    ids={n['id'] for n in overview['nodes']}
    assert len(ids)==len(overview['nodes']), 'Duplicate mathematical map node'
    for node in overview['nodes']:
        assert all(a in anchors for a in node['paperAnchors']), node['id']
        node['lean']=list(dict.fromkeys(name for a in node['paperAnchors'] for name in anchors[a]['lean']))
        assert all(name in names for name in node['lean']), node['id']
    assert all(e['source'] in ids and e['target'] in ids for e in overview['edges'])
    (dist/'proof-map.json').write_text(json.dumps(overview,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    shutil.copyfile(ROOT / 'inputs/proof-data.json.gz', dist / 'proof-data.json.gz')
    shutil.copyfile(ROOT / 'inputs/snapshot.json', dist / 'snapshot.json')
    if 'paperRevision' in snapshot:
        shutil.copyfile(ROOT / 'inputs/paper-revision.json', dist / 'paper-revision.json')
    for paper in data['trace']['papers']:
        target = dist / 'papers' / paper['id']
        target.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / 'inputs' / paper['pdf'], target / 'paper.pdf')
        for page in paper['pages']:
            shutil.copyfile(ROOT / 'inputs' / page['file'], dist / page['file'])
    files = list(dist.rglob('*'))
    assert all(p.stat().st_size < 25*1024*1024 for p in files if p.is_file()), 'Static asset exceeds Cloudflare size limit'
    print('Built public inspector:', len(data['trace']['anchors']), 'paper locations,', snapshot['mappedAnchorCount'], 'curated mappings,', snapshot['renderedPages'], 'pages.')

if __name__ == '__main__':
    build()
