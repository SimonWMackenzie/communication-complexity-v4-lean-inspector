# V4 paper and Lean inspector

Published through **GitHub Pages**. The public source repository is
[SimonWMackenzie/communication-complexity-v4-lean-inspector](https://github.com/SimonWMackenzie/communication-complexity-v4-lean-inspector).
The Pages address is shown in this repository's About section and deployment.

The GitHub Actions workflow builds the retained snapshot, runs the source/data
and graph checks, and publishes only the generated website. No ChatGPT login,
Sites runtime, external API, or secret is needed to use or rebuild it.
The historical .openai/hosting.json is retained for the earlier publication's
provenance and regression checks; it is not the GitHub deployment configuration.
Future publication changes belong in .github/workflows/pages.yml.

This is the dedicated static Site source, separate from the mathematical
proof worktree. It publishes a hash-checked snapshot of that worktree and
adds curated, bidirectional paper correspondence. No proof or manuscript is
changed by preparing or building this Site.

## Rebuild

`python -B build_site.py` uses the retained `inputs/` snapshot and writes
`dist/`. It needs only Python's standard library. Then run
`python -B test_site.py` and `node check_scripts.cjs`.
`npm run dev` serves the built files on loopback port 8764.

The original preparation script additionally requires pypdf, pdfplumber,
Pillow and Poppler. `prepare_snapshot.py --help` documents its inputs. It
checks the original offline inspector hash and every source/PDF receipt
against the proof repository before rendering pages. The input artifact
hash is deliberately pinned; a new proof snapshot requires an explicit
reviewed update, not silently reading a different proof.

## Scope and evidence

- All 77 pages of the two current papers are rendered from their exact PDFs.
- 98 curated anchors link to existing compiled Lean declaration identifiers;
  one further curated entry identifies contextual evidence rather than a theorem.
- The complete compiled PDF anchor index also exposes locations without
  curated counterparts, clearly labelled as such rather than hidden.
- Highlights mark the location/beginning of a labelled statement or equation,
  not the boundary of a complete proof. Physical pages and coordinates come
  from PDF named destinations corresponding to compiled AUX labels. Numbered
  statement headers are verified in the PDF text, correcting destinations
  that LaTeX placed before a page break; the original destination page is retained.
- Every mapping is mathematical interpretation, not a Lean certificate.
  Definitions, statement correspondences, assembled proofs, external inputs,
  and unmapped context are separately labelled.
- Multiple Lean declarations may prove one paper result. Their local
  hypotheses remain visible. The source and balanced-family existence
  results remain external to Lean.
- Runtime, materialization and ETH are outside this finite proof's scope.
- All exact Lean source and compiler reference data remain available. The
  graph is a source-reference graph, not kernel proof-term dependencies.
- The original verification-report hash is retained. Public report metadata
  omits machine-local commands and non-axiom operational log bodies.
- Public Site deployment is not a clean reproducible proof release.

`inputs/snapshot.json` identifies the proof snapshot and trace counts;
`trace-mappings.json` is the auditable curated map. `qa/` contains local PDF
region review images and is excluded from both Git and the published site.

The design reference was the NP-hardness inspector's v2-final: prerendered
paper pages, normalized highlight rectangles, source/definition cards and
reverse navigation. That repository was read without modification.

## Conference edition and dependency explorer

The revised reader has 24 pages; the matching formal paper has 53.
The original Lean snapshot is unchanged. The separate paper revision receipt
records the newer paper bytes, preserving the historical proof audit as-is.
To refresh papers, pass the verified receipt with
prepare_snapshot.py --paper-receipt; this never permits changes outside the
two manuscript directories or waives the old Lean hash checks.

Dependency graph opens a 14-step mathematical map with explicit outside inputs.
Its arrows are curated mathematical explanations. The separate Lean source
view traverses the complete compiler-recorded name-reference index. It supports
incoming/outgoing traversal, arbitrary reachable depth, module grouping,
search, shortest recorded paths from the root, source occurrence evidence,
zoom/pan, and JSON downloads. Display caps and terminal filters are explicit;
group counts distinguish module arrows from declaration-reference pairs.

## Design revision, 6 September 2026

The interface was unified into one token-driven design system
(`design.css`: one type scale, one radius scale, one control height, one
focus ring, one list-row and one badge component shared by the paper, graph
and Lean views; `trace.css` now carries layout only). Overlapping paper
highlights are resolved for display in `trace.js`: where two recorded
location boxes intersect, the upper box is trimmed at the next box's top edge
with `clip-path`, so the visible boxes and their click targets are disjoint.
The recorded coordinates, the proof snapshot, the papers and every mapping are
unchanged; the trimming is presentation only and is stated in the detail
panel. Measured on all 372 recorded locations: 56 overlapping pairs on 27
pages before, 0 visible overlaps after, with every box keeping at least 39%
of its recorded height. Metadata text now meets WCAG AA contrast.

## Provenance revision

The design system was then reworked to match the published NP-hardness
"Formal Proof Explorer" (dark console, mono eyebrows, glass panels, pill
groups, SVG statement cards), and provenance was made visible at every level.

Colour carries origin and nothing else; kind is a mono badge. There are five
origins, read off each declaration's Lean module:

| Origin | Modules | In the root closure |
| --- | --- | --- |
| Proved in Lean, this paper | `EthInapproximability.V4.*` | 3,753 |
| Reused, companion paper's Lean | `NPCC.*`, `Workspace.*`, `EthBridge.*`, `LegacyNPCC.*` | 390 |
| Reused, earlier route here | `EthInapproximability.ParameterizedNP.*` | 1,408 |
| Library | Mathlib, Lean core, Batteries | 1,175 |
| External input | none — not proved in Lean | 2 |

The companion paper is Gaspers, He and Mackenzie, *NP-Completeness of
Deterministic Communication Complexity via Relaxed Interlacing* (companion
manuscript, 2026); its Lean formalization is vendored here and compiles as
part of this build.

The two external inputs are named wherever they appear: the **composed source
theorem** (formal Assumption 4.1 / reader §2.2), whose intended source is the
companion construction, and the **balanced-family theorem** (formal Theorem
4.4 and Appendix D / reader §2, Equation 14 on p. 5), proved on paper in this
paper and deliberately kept outside Lean. Both citations name a location the
compiled anchor index actually carries, so the provenance card's prose and the
link beside it agree. Both enter the root theorem as explicit
hypotheses. The root's audited axiom footprint, quoted from the published
verification log, is `propext · Classical.choice · Quot.sound`; the companion
layer's own balanced-family citation axiom is not in it.

Each map step also reports how many companion-paper declarations its Lean
components reach through recorded source references, and lists them by name
and module. The Lean source view colours every card and module group by
origin and can filter by it; the Lean inspector shows an origin badge and a
coloured tick per navigation row; the paper tracer's highlight colours follow
the correspondence classification and are explained by a key above the pages.

The landing view is the mathematical proof map.

## Comparative QA revision

A second pass compared the site against the published NP-hardness explorer and
closed the gaps it found.

The dependency explorer is now a **fixed one-screen shell**, as the reference
is: `html`/`body` own the viewport, and the canvas and the aside scroll inside
themselves, so the legend, the floating buttons and the axiom footer are always
on screen instead of below the fold. The clamp is scoped to that view — the
paper tracer and the Lean inspector are documents and keep the page's own
scrolling — and it is released below 760px and at text scales of 150% and
above, where the columns have already stacked and one screen cannot hold canvas,
aside and footer at a usable size; the whole page scrolls there instead.

The header went from four rows and 273px to two rows and 165px at 1440px:
identity and the provenance counts on the first row, every control on the
second. Selects are drawn by the design system rather than the browser (an
inline data-URI chevron, no icon font and no network request); the text-size
stepper, the pill groups and the search box share one radius family; and the
proof-index download is offered as the reference's two-line `.dlbtn`, whose
size is read from the transfer the page itself made.

Provenance display was tightened rather than changed: the shortcut numbers now
take their step's origin colour instead of falling through to the interface
accent, the counts say what they are counts of (the root's source-reference
closure) and separate the two that count something else, the legend is a key
with its sentences on tooltips instead of a paragraph over the drawing, and the
graph pill is named for the view it opens rather than for one of that view's
two relations. `--faint` was raised to `#7c8c9e`, which clears 4.5:1 on every
surface it is used on (`--panel2` is the worst case, at 4.54:1), and the
tracer's "no correspondence" and "context" greys, previously a shade apart, are
now a grey and a violet.

In the Lean source graph, declaration names break where the name itself breaks
— after a `.` or `_`, or at a camelCase boundary — and a segment that still
does not fit is middle-ellipsized rather than cut mid-token; the complete name
stays in the node's tooltip and in the aside.

One pre-existing nit is recorded but not fixed, because it is in the read-only
template: its document-level `keydown` handler calls `e.target.matches(...)`
without checking that the target is an `Element`, so a keyboard event
dispatched directly on `document` or `window` throws. Real keystrokes always
target an element, so this never fires in use. The handlers this repository
owns (`trace.js`, `graph.js`) guard it.

The user approved browser testing. test_browser.cjs runs an isolated headless
browser against the local preview and covers paper tracing, definition cards,
graph search/paths/arrows, mobile layout, 200-percent text and page errors.
Pass the installed Playwright module path as its first argument when needed.
Run node test_graph.cjs for the pure graph-data tests as well.
