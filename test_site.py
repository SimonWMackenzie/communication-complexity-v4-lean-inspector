"""Static and data-contract regressions; does not launch or inspect a browser."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import unittest

from build_site import transform

ROOT = Path(__file__).resolve().parent

class SiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(gzip.decompress((ROOT / 'inputs/proof-data.json.gz').read_bytes()))
        cls.trace = cls.data['trace']
        cls.by_name = {d['id']: d for d in cls.data['declarations']}
        cls.by_anchor = {a['id']: a for a in cls.trace['anchors']}
        cls.papers = {p['id']: p for p in cls.trace['papers']}
        cls.html = (ROOT / 'dist/index.html').read_text(encoding='utf-8')

    def test_proof_snapshot_unchanged(self):
        self.assertEqual(self.data['meta']['git'], '4644d0a32945c2214592c497edc5872961dc8bda')
        self.assertEqual(len(self.data['modules']), 441)
        self.assertEqual(len(self.data['declarations']), 12815)

    def test_two_papers_all_pages(self):
        self.assertEqual({k:len(v['pages']) for k,v in self.papers.items()}, {'reader':24,'formal':53})

    def test_every_mapping_resolves(self):
        mapped = [a for a in self.trace['anchors'] if a['lean']]
        self.assertEqual(len(mapped), 98)
        self.assertEqual(len(json.loads((ROOT/'trace-mappings.json').read_text(encoding='utf-8'))),99)
        self.assertEqual(len(self.trace['anchors']), len(self.by_anchor))
        for a in mapped:
            self.assertTrue(a['note'])
            for name in a['lean']:
                self.assertIn(name, self.by_name)
                self.assertIn(a['id'], self.by_name[name]['traceAnchors'])

    def test_all_reverse_links_resolve(self):
        for name,d in self.by_name.items():
            for anchor in d.get('traceAnchors', []):
                self.assertIn(name, self.by_anchor[anchor]['lean'])

    def test_rectangles_inside_correct_page(self):
        for a in self.trace['anchors']:
            self.assertGreaterEqual(a['page'],1)
            self.assertLessEqual(a['page'],len(self.papers[a['paperId']]['pages']))
            self.assertTrue(a['destination'])
            self.assertTrue(a['source']['sourceSha256'])
            for r in a['rectangles']:
                self.assertEqual(r['page'],a['page'])
                self.assertTrue(0<=r['x0']<r['x1']<=1)
                self.assertTrue(0<=r['y0']<r['y1']<=1)

    def test_unmapped_is_explicit(self):
        for a in self.trace['anchors']:
            if a['classification']=='unmapped':
                self.assertEqual(a['lean'],[])
                self.assertIn('no curated Lean correspondence',a['note'])

    def test_numbered_statement_headers_are_verified(self):
        for a in self.trace['anchors']:
            if a['kind'] not in {'equation','unnumbered-equation','section','subsection','appendix'}:
                self.assertEqual(a['locationVerification'],'printed numbered header')
                self.assertIn(a['number'],a['excerpt'])
        main=self.by_anchor['reader:thm:reader-main']
        self.assertEqual(main['compiledDestinationPage'],2)
        self.assertEqual(main['page'],2)
        self.assertIn('Theorem 1.1',main['excerpt'])
        branch=self.by_anchor['formal:eq:one-total-branch']
        self.assertEqual(branch['kind'],'unnumbered-equation')
        self.assertIn('genuineObject',branch['excerpt'])
        cutoff=self.by_anchor['formal:lem:finite-cutoff']
        self.assertEqual((cutoff['compiledDestinationPage'],cutoff['page']),(21,21))
        cost=self.by_anchor['formal:eq:communication-cost']
        self.assertEqual(cost['kind'],'unnumbered-equation')
        self.assertIn('min{cost(P)',cost['excerpt'])

    def test_polynomial_existence_remains_external(self):
        a=self.by_anchor['formal:thm:balanced-family-realization']
        self.assertEqual(a['classification'],'external')
        self.assertNotEqual(self.by_name[a['lean'][0]]['status'],'root-audited')

    def test_public_roots_link_real_log_wrapper(self):
        for key in ['reader:thm:reader-main','formal:thm:finite-main']:
            self.assertIn(self.data['root'],self.by_anchor[key]['lean'])

    def test_operational_logs_not_published(self):
        v=self.data['meta']['verification']
        self.assertEqual(len(v['report']['steps']),15)
        self.assertEqual({x['id'] for x in v['logs']},{'root-axioms','source-log-axioms','statement-axioms'})
        self.assertIn('public extract',self.data['meta']['publicEdition']['evidenceNotice'])

    def test_pdfs_and_pages_match_hashes(self):
        for paper in self.papers.values():
            pdf=ROOT/'dist'/paper['pdf']
            self.assertEqual(hashlib.sha256(pdf.read_bytes()).hexdigest(),paper['pdfSha256'])
            for page in paper['pages']:
                self.assertEqual(hashlib.sha256((ROOT/'dist'/page['file']).read_bytes()).hexdigest(),page['sha256'])

    def test_new_papers_have_separate_receipt(self):
        revision=self.data['meta']['paperRevision']
        receipt=(ROOT/'inputs/paper-revision.json').read_bytes()
        self.assertEqual(hashlib.sha256(receipt).hexdigest(),revision['receiptSha256'])
        self.assertEqual(json.loads(receipt),revision['receipt'])
        self.assertIn('older proof verification report',revision['notice'])
        for p in revision['receipt']['papers']:
            self.assertEqual(self.papers[p['id']]['pdfSha256'],p['pdfSha256'])
        self.assertIn('Download the separate paper source/PDF receipt',self.html)

    def test_all_lean_content_matches_previous_published_edition(self):
        original=json.loads(gzip.decompress(subprocess.check_output(
            ['git','show','fa9f8a438cad83d0289637f405577ef63f9eff2a:inputs/proof-data.json.gz'],cwd=ROOT)))
        without_trace=lambda ds:[{k:v for k,v in d.items() if k!='traceAnchors'} for d in ds]
        self.assertEqual(without_trace(self.data['declarations']),without_trace(original['declarations']))
        self.assertEqual(self.data['modules'],original['modules'])
        self.assertEqual(self.data['meta']['verification'],original['meta']['verification'])

    def test_hosting_and_static_asset_limit(self):
        hosting=json.loads((ROOT/'.openai/hosting.json').read_text())
        self.assertEqual(hosting['static']['directory'],'dist')
        for file in (ROOT/'dist').rglob('*'):
            if file.is_file():self.assertLess(file.stat().st_size,25*1024*1024)

    def test_loader_and_trace_integration(self):
        self.assertNotIn('__INSPECTOR_DATA__',self.html)
        self.assertIn('new DecompressionStream("gzip")',self.html)
        self.assertIn('new CustomEvent("v4-inspector-ready"',self.html)
        self.assertIn('<script src="trace.js"></script>',self.html)
        self.assertIn('window.V4Trace.addLinks(d,host)',self.html)
        self.assertIn('new CustomEvent("v4-declaration-selected"',self.html)

    def test_no_remote_runtime_dependency(self):
        for src in re.findall(r'<script[^>]+src="([^"]+)"',self.html):
            self.assertFalse(src.startswith(('http:','https:','//')))
            self.assertTrue((ROOT/'dist'/src).is_file())

    def test_template_change_fails_closed(self):
        with self.assertRaisesRegex(ValueError,'bootstrap changed'):
            transform('<html></html>')

if __name__=='__main__':unittest.main()
