"""Capture an unchanged proof snapshot and derive paper navigation from its PDFs.

This reads the proof repository, never writes it, and does not formalize or
modify mathematics. Run once for a new publication snapshot, then version inputs/.
"""
import argparse
import base64
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

import pdfplumber
from pypdf import PdfReader
from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parent
PROOF_SHA = "407ea7f19b300704132d20db8d1fdb41212678da5787733e4e59b249dccec913"

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def groups(text):
    result, depth, start = [], 0, None
    for i, char in enumerate(text):
        if char == "{" and (i == 0 or text[i-1] != "\\"):
            if depth == 0:
                start = i + 1
            depth += 1
        elif char == "}" and (i == 0 or text[i-1] != "\\"):
            depth -= 1
            if depth == 0:
                result.append(text[start:i])
    require(depth == 0, "Unbalanced AUX fields")
    return result

def labels(aux):
    result = []
    for line in aux.splitlines():
        if not line.startswith("\\newlabel{"):
            continue
        outer = groups(line[len("\\newlabel"):])
        if len(outer) != 2 or outer[0].endswith("@cref"):
            continue
        parts = groups(outer[1])
        if len(parts) >= 4:
            result.append({"label": outer[0], "number": parts[0], "printedPage": parts[1],
                           "titleTex": parts[2], "destination": parts[3]})
    return result

def plain_tex(text):
    text = re.sub(r"\\(?:IeC|protect)\s*", "", text)
    text = re.sub(r"\\[a-zA-Z]+\*?", "", text)
    return re.sub(r"\s+", " ", text.replace("{", "").replace("}", "").replace("~", " ").replace("$", "")).strip()

def locate_label_sources(directory):
    result = {}
    for file in sorted(directory.rglob("*.tex")):
        if "build" in file.relative_to(directory).parts:
            continue
        text = file.read_text(encoding="utf-8-sig")
        for match in re.finditer(r"\\label\{([^}]+)\}", text):
            name = match.group(1)
            require(name not in result, "Duplicate source label: " + name)
            result[name] = {"file": file.relative_to(directory).as_posix(),
                            "line": text[:match.start()].count("\n") + 1,
                            "sourceSha256": digest(file)}
    return result

def anchor_rectangle(page, top, kind):
    """Highlight the compiled anchor's immediate text region, not an inferred proof.

    The rectangle is deliberately a location marker, not a claim about where
    a formal proof starts or ends. This avoids single-page/italic-font heuristics.
    """
    words = page.extract_words(x_tolerance=2, y_tolerance=3)
    body = [w for w in words if 35 < w["top"] < page.height - 38]
    candidates = [w for w in body if top - 3 <= w["top"] <= top + 35]
    if not candidates:
        candidates = sorted(body, key=lambda w: abs(w["top"] - top))[:6]
    require(candidates, "No PDF text near named destination")
    first_y = min(w["top"] for w in candidates)
    # Two text lines make equation/heading targets usable without swallowing a proof.
    local = [w for w in body if first_y - 1 <= w["top"] <= first_y + 19]
    require(local, "Empty PDF anchor region")
    x0 = min(w["x0"] for w in local) - 3
    x1 = max(w["x1"] for w in local) + 3
    y0 = min(w["top"] for w in local) - 3
    y1 = max(w["bottom"] for w in local) + 3
    return {"x0": max(0, x0 / page.width), "y0": max(0, y0 / page.height),
            "x1": min(1, x1 / page.width), "y1": min(1, y1 / page.height)}, " ".join(w["text"] for w in local)

def verified_statement_location(pdf, record, page_number, top):
    """Verify numbered statement headers, including anchors before a page break.

    LaTeX may place a PDF destination on the preceding page. The printed
    header is authoritative for the clickable location; retain the destination
    page separately as provenance. Fail closed if no unique header is found.
    """
    kind = record["destination"].split(".")[0]
    if record["label"].startswith("eq:") and kind != "equation":
        reviewed_text = {"eq:one-total-branch": "genuineObject(", "eq:communication-cost": "min{cost(P)"}
        require(record["label"] in reviewed_text, "Unreviewed inherited equation anchor")
        matches = [w for w in pdf.pages[page_number - 1].extract_words(x_tolerance=2, y_tolerance=3)
                   if w["text"].startswith(reviewed_text[record["label"]])]
        require(len(matches) == 1, "Could not uniquely locate the unnumbered branch equation")
        return page_number, matches[0]["top"], "Unnumbered equation"
    if kind in {"equation", "section", "subsection", "appendix"}:
        return page_number, top, None
    prefix = record["label"].split(":")[0]
    header = {"cor": "Corollary", "lem": "Lemma"}.get(prefix, kind.capitalize())
    matches = []
    for candidate_page in range(max(1, page_number - 1), min(len(pdf.pages), page_number + 1) + 1):
        words = pdf.pages[candidate_page - 1].extract_words(
            x_tolerance=2, y_tolerance=3, extra_attrs=["fontname"])
        for word, number in zip(words, words[1:]):
            if (word["text"] == header and number["text"].rstrip(".") == record["number"]
                    and abs(word["top"] - number["top"]) < 2
                    and (("bold" in word["fontname"].lower() and "bold" in number["fontname"].lower())
                         or (kind in {"assumption", "invariant"} and "italic" in word["fontname"].lower()
                             and 60 < word["x0"] < 80))):
                matches.append((candidate_page, word["top"]))
    require(len(matches) == 1, f"Expected one printed header for {record['label']}: {matches}")
    return *matches[0], header

def prepare(repo, snapshot, mapping_files, paper_receipt=None):
    require(digest(snapshot) == PROOF_SHA, "Unexpected original inspector snapshot")
    html = snapshot.read_text(encoding="utf-8")
    match = re.search(r'<script id="inspector-data" type="application/json">(.*?)</script>', html, re.S)
    require(match is not None, "Missing original proof payload")
    data = json.loads(match.group(1))
    report = data["meta"]["verification"]["report"]
    require(report["success"] and len(report["steps"]) == 15, "Incomplete proof verification")
    revision = json.loads(paper_receipt.read_text(encoding="utf-8")) if paper_receipt else None
    if revision:
        require(revision["success"] and revision["proofCommit"] == data["meta"]["git"], "Invalid paper revision receipt")
        require({p["id"] for p in revision["papers"]} == {"reader", "formal"}, "Both paper receipts required")
        for rel, expected in {**revision["source_hashes"], **revision["manuscript_hashes"]}.items():
            require(rel.startswith(("routes/parameterized-np/reader-facing/", "routes/parameterized-np/autoformalization/")), "Revision changes something outside the papers")
            require(digest(repo / rel) == expected.lower(), "Revised paper receipt mismatch: " + rel)
    for rel, expected in report["source_hashes"].items():
        if revision and rel in revision["source_hashes"]:
            continue
        require(digest(repo / rel) == expected.lower(), "Proof/paper source changed: " + rel)
    for rel, expected in report["manuscript_hashes"].items():
        revised_hash = revision["manuscript_hashes"].get(rel) if revision else None
        require(digest(repo / rel) == (revised_hash or expected).lower(), "Paper changed without receipt: " + rel)
    mappings = []
    for path in mapping_files:
        mappings.extend(json.loads(path.read_text(encoding="utf-8-sig")))
    by_name = {d["id"]: d for d in data["declarations"]}
    by_anchor = {}
    for item in mappings:
        key = (item["paperId"], item["label"])
        require(key not in by_anchor, "Duplicate trace mapping: " + str(key))
        require(item["classification"] in {"definition", "statement", "assembled", "external", "context"}, "Unknown mapping class")
        require(all(name in by_name for name in item["lean"]), "Unknown Lean mapping: " + str(key))
        by_anchor[key] = item
    inputs = ROOT / "inputs"
    inputs.mkdir(exist_ok=True)
    trace = {"schemaVersion": 1, "papers": [], "anchors": [], "geometryMeaning":
             "Highlights locate compiled paper anchors; they do not delimit or certify an entire proof. Correspondence to Lean is curated, not compiler-derived."}
    diagnostics = []
    for paper in data["papers"]:
        paper_id = paper["id"]
        pdf_path = repo / paper["path"]
        directory = pdf_path.parent.parent
        aux_path = directory / "build/main.aux"
        aux_text = aux_path.read_text(encoding="utf-8-sig")
        if revision:
            revised_paper = next(p for p in revision["papers"] if p["id"] == paper_id)
            require(digest(aux_path) == revised_paper["auxSha256"], "AUX differs from reviewed build")
        src_labels = locate_label_sources(directory)
        paper_dir = inputs / "papers" / paper_id
        paper_dir.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(pdf_path, paper_dir / "paper.pdf")
        shutil.copyfile(aux_path, paper_dir / "labels.aux")
        reader = PdfReader(pdf_path)
        if revision:
            require(len(reader.pages) == revised_paper["pages"], "Paper revision page count differs")
        destinations = reader.named_destinations
        page_records = []
        with tempfile.TemporaryDirectory(prefix="v4-paper-pages-") as temporary:
            prefix = str(Path(temporary) / "page")
            subprocess.run(["pdftoppm", "-r", "125", "-png", str(pdf_path), prefix], check=True, capture_output=True)
            rendered = sorted(Path(temporary).glob("page-*.png"), key=lambda p: int(p.stem.split("-")[-1]))
            require(len(rendered) == len(reader.pages), "Rendered PDF page count differs")
            for i, path in enumerate(rendered, 1):
                with Image.open(path) as image:
                    dest = paper_dir / f"page-{i:03d}.webp"
                    image.convert("RGB").save(dest, "WEBP", quality=84, method=4)
                    page_records.append({"page": i, "width": image.width, "height": image.height,
                                         "file": f"papers/{paper_id}/{dest.name}", "sha256": digest(dest)})
            with pdfplumber.open(pdf_path) as pdf:
                for record in labels(aux_text):
                    label = record["label"]
                    if label not in src_labels or record["destination"] not in destinations:
                        continue
                    destination = destinations[record["destination"]]
                    page_number = reader.get_destination_page_number(destination) + 1
                    destination_page = page_number
                    top = pdf.pages[page_number - 1].height - float(destination.top)
                    page_number, top, header = verified_statement_location(pdf, record, page_number, top)
                    page = pdf.pages[page_number - 1]
                    kind = record["destination"].split(".")[0]
                    if header == "Unnumbered equation":
                        kind = "unnumbered-equation"
                    rect, excerpt = anchor_rectangle(page, top, kind)
                    mapping = by_anchor.get((paper_id, label))
                    title = plain_tex(record["titleTex"])
                    display_kind = header or {"equation": "Equation", "section": "Section", "subsection": "Section"}.get(kind, kind.capitalize())
                    record.update({"id": paper_id + ":" + label, "paperId": paper_id, "page": page_number,
                                   "compiledDestinationPage": destination_page,
                                   "locationVerification": "reviewed equation text; inherited destination corrected" if kind == "unnumbered-equation" else "printed numbered header" if header else "compiled PDF destination",
                                   "kind": kind, "title": display_kind + ("" if kind == "unnumbered-equation" else " " + record["number"]) + (" — " + title if kind != "equation" else ""),
                                   "rectangles": [{"page": page_number, **rect}], "excerpt": excerpt,
                                   "source": src_labels[label], "lean": mapping["lean"] if mapping else [],
                                   "classification": mapping["classification"] if mapping else "unmapped",
                                   "note": mapping["note"] if mapping else "This paper location has no curated Lean correspondence in this edition. Use nearby mapped statements; do not infer formal coverage from its presence."})
                    trace["anchors"].append(record)
                    if kind == "unnumbered-equation":
                        record["note"] += " The display is unnumbered in the PDF; its AUX label inherits the preceding location and number. This highlight was corrected using the equation text, without changing the paper."
                    if mapping:
                        with Image.open(rendered[page_number - 1]) as image:
                            y0 = max(0, int(rect["y0"] * image.height) - 16)
                            y1 = min(image.height, int(rect["y1"] * image.height) + 16)
                            crop = image.convert("RGB").crop((0, y0, image.width, y1))
                            crop.thumbnail((900, 160))
                            diagnostics.append((record["id"], crop.copy()))
        trace["papers"].append({"id": paper_id, "title": paper["title"], "pdf": f"papers/{paper_id}/paper.pdf",
                                "pdfSha256": digest(pdf_path), "auxSha256": digest(aux_path), "pages": page_records})
        # Hosted files replace the data URLs and machine-local paths.
        paper.pop("dataUrl", None)
        paper["href"] = f"papers/{paper_id}/paper.pdf"
        paper["downloadName"] = paper_id + "-paper.pdf"
        if revision:
            paper["sha256"] = digest(pdf_path)
            paper["bytes"] = pdf_path.stat().st_size
            paper["paperRevision"] = revision["edition"]
    found = {(a["paperId"], a["label"]) for a in trace["anchors"]}
    require(set(by_anchor) <= found, "Mapped labels have no compiled PDF destinations: " + repr(set(by_anchor) - found))
    trace["anchors"].sort(key=lambda a: (a["paperId"], a["page"], a["rectangles"][0]["y0"], a["label"]))
    for item in trace["anchors"]:
        for name in item["lean"]:
            by_name[name].setdefault("traceAnchors", []).append(item["id"])
    # Public evidence preserves exact mathematical source and audit text, but
    # excludes operational logs enumerating unrelated untracked experiments.
    verification = data["meta"]["verification"]
    verification["logs"] = [log for log in verification["logs"] if log["id"] in {"root-axioms", "source-log-axioms", "statement-axioms"}]
    original_report = verification["report"]
    verification["report"] = {key: value for key, value in original_report.items() if key not in {"repository", "git_status", "git_state", "output_directory"}}
    for step in verification["report"]["steps"]:
        step.pop("command", None)
    data["meta"]["publicEdition"] = {"originalOfflineArtifactSha256": PROOF_SHA,
        "evidenceNotice": "The original full report hash is retained. The displayed report is a public extract; machine-local command lines and non-axiom operational log bodies are omitted. No Lean source or mathematical statement was changed.",
        "paperTrace": "Compiled PDF destinations locate labels; printed numbered statement headers verify and correct page-break locations. Human-reviewed label/declaration mappings determine mathematical correspondence, which is not itself kernel-checked."}
    if revision:
        data["meta"]["paperRevision"] = {"receiptSha256": digest(paper_receipt), "receipt": revision,
            "notice": "The papers were editorially revised after the unchanged Lean proof snapshot. This separate source/PDF receipt covers the revised papers; the older proof verification report covers the earlier paper bytes, not these PDFs."}
        data["meta"]["publicEdition"]["evidenceNotice"] += " A separate paper-revision receipt identifies the new manuscript bytes; the original proof report is historical evidence for the unchanged Lean snapshot."
    data["trace"] = trace
    compressed = gzip.compress(json.dumps(data, ensure_ascii=False, separators=(",", ":")).encode("utf-8"), mtime=0)
    (inputs / "proof-data.json.gz").write_bytes(compressed)
    (inputs / "trace-index.json").write_text(json.dumps(trace, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    (ROOT / "trace-mappings.json").write_text(json.dumps(mappings, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    manifest = {"schemaVersion": 1, "proofCommit": data["meta"]["git"], "sourceSnapshotSha256": PROOF_SHA,
                "proofPayloadSha256": digest(inputs / "proof-data.json.gz"), "proofPayloadBytes": len(compressed),
                "anchorCount": len(trace["anchors"]), "mappedAnchorCount": len(by_anchor),
                "leanLinkedAnchorCount": sum(bool(a["lean"]) for a in trace["anchors"]),
                "renderedPages": sum(len(p["pages"]) for p in trace["papers"]),
                "originalProofVerificationReportSha256": verification["reportSha256"],
                "scope": "Finite gap and same-matrix size only; external source/family existence remains external."}
    if revision:
        manifest["paperRevision"] = {"edition": revision["edition"], "receiptSha256": digest(paper_receipt),
                                     "pages": {p["id"]: p["pages"] for p in revision["papers"]}}
        shutil.copyfile(paper_receipt, inputs / "paper-revision.json")
    (inputs / "snapshot.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    # PDF-region review sheets are local QA, never public website assets.
    qa = ROOT / "qa"
    qa.mkdir(exist_ok=True)
    for batch in range(0, len(diagnostics), 12):
        selected = diagnostics[batch:batch+12]
        sheet = Image.new("RGB", (960, sum(img.height + 32 for _, img in selected)), "#edf0f5")
        draw, y = ImageDraw.Draw(sheet), 0
        for title, img in selected:
            draw.text((10, y+5), title, fill="#111111")
            sheet.paste(img, (30, y + 26))
            y += img.height + 32
        sheet.save(qa / f"pdf-anchor-regions-{batch//12+1:02d}.png")
        sheet.save(qa / f"pdf-anchor-regions-{batch//12+1:02d}.jpg", quality=88)
    print(json.dumps(manifest, indent=2))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--snapshot", required=True, type=Path)
    parser.add_argument("--mappings", nargs="+", required=True, type=Path)
    parser.add_argument("--paper-receipt", type=Path)
    args = parser.parse_args()
    prepare(args.repo.resolve(), args.snapshot.resolve(), args.mappings, args.paper_receipt)
