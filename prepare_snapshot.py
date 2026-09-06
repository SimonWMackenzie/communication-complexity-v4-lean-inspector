"""Capture an unchanged proof snapshot and derive paper navigation from its PDFs.

This reads the proof repository, never writes it, and does not formalize or
modify mathematics. Run once for a new publication snapshot, then version inputs/.
"""
import argparse
import base64
import collections
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import string
import subprocess
import tempfile
import unicodedata

import pdfplumber
from pypdf import PdfReader
from PIL import Image, ImageDraw, ImageFont

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
    """Map each \\label to its manuscript file, plus the manuscript text itself.

    The text is read only to learn where a statement environment ends; nothing
    in the proof repository is written or reformatted.
    """
    result, texts, offsets = {}, {}, {}
    for file in sorted(directory.rglob("*.tex")):
        if "build" in file.relative_to(directory).parts:
            continue
        text = file.read_text(encoding="utf-8-sig")
        relative = file.relative_to(directory).as_posix()
        texts[relative] = text
        for match in re.finditer(r"\\label\{([^}]+)\}", text):
            name = match.group(1)
            require(name not in result, "Duplicate source label: " + name)
            result[name] = {"file": relative, "line": text[:match.start()].count("\n") + 1,
                            "sourceSha256": digest(file)}
            offsets[name] = match.start()
    return result, texts, offsets

### Printed extent ############################################################
# A highlight boxes what a labelled statement or display actually occupies on
# its page. A statement is grown from its printed header line to its last
# printed line, and where the environment ends in prose the manuscript source
# supplies its closing words, so the box ends where the author ended the
# statement rather than where a font changes. A display is not counted in
# lines at all: it is taken as the connected block of rendered ink its printed
# number claims, because a row containing a fraction, a large operator with
# limits or a case brace is taller than one line of text and no line height
# measures it. None of this infers, delimits or certifies a proof.

INK_DPI = 300                # resolution the printed ink is measured at
INK_LEVEL = 200              # a pixel at least this dark is ink
SLIVER = 2.0                 # thinner than any printed row: a dot, accent or rule
FLUSH = 4.0                  # how near the margin a row starts to be running text
INDENT = 36.0                # the deepest indent running text is set at here
FOLIO = (35.0, 722.0)        # the printed body, excluding running head and folio

TEXT_FONT = re.compile(r"LM(?:Roman|Sans|Mono|TypeWriter)", re.I)
SLANTED = re.compile(r"Italic|Slanted|Oblique", re.I)
BOLD = re.compile(r"Bold", re.I)
ENVIRONMENT_WORDS = {"Theorem", "Lemma", "Corollary", "Proposition", "Definition", "Assumption",
                     "Invariant", "Convention", "Claim", "Remark", "Example", "Notation", "Fact",
                     "Observation", "Conjecture", "Question"}
STATEMENT_ENVIRONMENTS = {word.lower() for word in ENVIRONMENT_WORDS}
NUMBERED = re.compile(r"[A-Z]?\d+(?:\.\d+)*\.?")
EQUATION_TAG = re.compile(r"\(\d+\)")
PROOF_WORDS = {"Proof", "Proof.", "Proof:"}
DISPLAY_KINDS = {"equation", "unnumbered-equation"}
HEADING_KINDS = {"section", "subsection", "appendix"}
ALPHANUMERIC = set(string.ascii_lowercase + string.digits)
# The plain closing words of a statement: a run of at least three ordinary
# words ending the environment, so inline mathematics never enters the target.
# A parenthesised item tag such as (S4) counts as one of those words.
PLAIN_WORD = r"\(?[A-Za-z][A-Za-z0-9'\u2019-]*\)?[.,;:!?]?"
CLOSING_RUN = re.compile(r"(?:%s\s+){2,}%s\s*$" % (PLAIN_WORD, PLAIN_WORD))
ENVIRONMENT_START = re.compile(r"\\begin\{([a-zA-Z]+\*?)\}")

def visual_lines(page):
    """The page's printed lines, with stacked-math fragments folded back in.

    Sub- and superscripts, fraction bars and case blocks print as their own
    word rows a few points from the row they belong to. Folding each fragment
    into the row it overlaps makes one entry per printed line, so a box can be
    grown a line at a time.
    """
    typed = page.extract_words(x_tolerance=2, y_tolerance=3, extra_attrs=["fontname", "size"])
    inside = lambda word: FOLIO[0] < word["top"] < FOLIO[1]  # excludes only head and folio
    rows = []
    for word in sorted((w for w in typed if inside(w)), key=lambda w: (round(w["top"], 1), w["x0"])):
        if rows and abs(rows[-1]["top"] - word["top"]) <= 3:
            rows[-1]["words"].append(word)
            rows[-1]["bottom"] = max(rows[-1]["bottom"], word["bottom"])
        else:
            rows.append({"top": word["top"], "bottom": word["bottom"], "words": [word]})
    def shared(row, other):
        return 0 if other is None else min(row["bottom"], other["bottom"]) - max(row["top"], other["top"])
    def absorb(host, row):
        host["top"] = min(host["top"], row["top"])
        host["bottom"] = max(host["bottom"], row["bottom"])
        host["words"] += row["words"]
    # A row stands on its own when it carries a display's number or enough
    # full-size words to be a printed line; anything less - a script, a
    # fraction bar, a case brace - belongs to the row it overlaps. Two numbered
    # rows of one aligned display are two labels and must stay two lines.
    for row in rows:
        body = [w for w in row["words"] if w["size"] >= 9.5 and "Extension" not in w["fontname"]]
        numbered = any(EQUATION_TAG.fullmatch(w["text"]) and w["x1"] > page.width - 90 for w in row["words"])
        row["whole"] = len(body) >= 4 or (numbered and len(body) >= 3)
    lines = []
    for index, row in enumerate(rows):
        previous = lines[-1] if lines else None
        following = rows[index + 1] if index + 1 < len(rows) else None
        before, after = shared(row, previous), shared(row, following)
        if row["whole"] or max(before, after) <= 0:
            lines.append(row)
        elif after > before:
            absorb(following, row)         # a fragment of the line below
        else:
            absorb(previous, row)          # a fragment of the line above
    for line in lines:
        line["x0"] = min(word["x0"] for word in line["words"])
        line["x1"] = max(word["x1"] for word in line["words"])
        line["plain"] = []
        # The line's own baseline row: the sub-row carrying its full-size
        # words. A compiled destination is measured against this, not against
        # the top of a script that happens to reach higher.
        body = [w for w in line["words"] if w["size"] >= 9.5 and "Extension" not in w["fontname"]]
        crowd = collections.Counter(round(word["top"], 1) for word in (body or line["words"]))
        line["base"] = min(top for top, count in crowd.items() if count == max(crowd.values()))
    # extract_words splits a word at every font change, so the readable text of
    # a line comes from the untyped extraction, assigned to the line it sits in.
    if lines:
        for word in page.extract_words(x_tolerance=2, y_tolerance=3):
            if not inside(word):
                continue
            distance = lambda line: (max(0, line["top"] - word["top"]) + max(0, word["top"] - line["bottom"]),
                                     abs(line["top"] - word["top"]))
            min(lines, key=distance)["plain"].append(word)
    reading = lambda word: (round(word["top"] / 3), word["x0"])
    for line in lines:
        line["words"].sort(key=reading)
        line["plain"].sort(key=reading)
        line["text"] = " ".join(word["text"] for word in line["plain"])
    return lines

def lettered(line):
    return [word for word in line["words"]
            if word["size"] >= 9 and TEXT_FONT.search(word["fontname"]) and any(c.isalpha() for c in word["text"])]

def printed_rows(page):
    """The page's printed word rows, one per printed baseline and unfolded.

    Unlike visual_lines these are not merged into reading lines: a display's
    numerator prints as its own row and must stay separate from the sentence
    beside it, whose last word may sit at the same height.
    """
    rows = []
    typed = page.extract_words(x_tolerance=2, y_tolerance=3, extra_attrs=["fontname", "size"])
    for word in sorted((w for w in typed if FOLIO[0] < w["top"] < FOLIO[1]),
                       key=lambda w: (round(w["top"], 1), w["x0"])):
        if rows and abs(rows[-1]["top"] - word["top"]) <= 3:
            rows[-1]["words"].append(word)
            rows[-1]["bottom"] = max(rows[-1]["bottom"], word["bottom"])
        else:
            rows.append({"top": word["top"], "bottom": word["bottom"], "words": [word]})
    for row in rows:
        row["x0"] = min(word["x0"] for word in row["words"])
        row["x1"] = max(word["x1"] for word in row["words"])
    return rows

def running_text(row, margin, width):
    """Whether a printed row is running text rather than a row of a display.

    Text is set flush to the margin, or one indent in from it and opening with
    a word; a display row is set in from the margin and opens with
    mathematics. A row ending in a number at the right margin is usually a
    numbered display, but a justified sentence whose last word is a reference
    to one ends the same way, so such a row counts as text only when it also
    starts flush at the margin and opens with a word.
    """
    opening = min(row["words"], key=lambda word: word["x0"])
    worded = bool(opening["size"] >= 9 and TEXT_FONT.search(opening["fontname"])
                  and any(character.isalpha() for character in opening["text"]))
    if any(EQUATION_TAG.fullmatch(word["text"]) and word["x1"] > width - 90 for word in row["words"]):
        return bool(worded and row["x0"] <= margin + FLUSH)
    return bool(row["x0"] <= margin + FLUSH or (worded and row["x0"] <= margin + INDENT))

def ink_runs(mask):
    """Every maximal run of inked pixel rows in a rendered page or column strip."""
    profile = mask.convert("F").resize((1, mask.height), Image.BOX)
    inked = list(getattr(profile, "get_flattened_data", profile.getdata)())
    runs, start = [], None
    for y in range(mask.height + 1):
        on = y < mask.height and inked[y] > 0.0
        if on and start is None:
            start = y
        elif not on and start is not None:
            runs.append((start, y))
            start = None
    return runs

def fold_slivers(bands):
    """A stray dot, accent or rule is not a printed row of its own.

    An i-dot separated from its word by one blank pixel row, or a fraction
    rule clear of both numerator and denominator, rejoins the row it touches;
    a sliver touching nothing is not a row at all and is dropped.
    """
    while True:
        thin = next((i for i, band in enumerate(bands)
                     if band["bottom"] - band["top"] < SLIVER), None)
        if thin is None:
            return bands
        band = bands.pop(thin)
        gaps = [(band["top"] - bands[thin - 1]["bottom"], thin - 1)] if thin else []
        if thin < len(bands):
            gaps.append((bands[thin]["top"] - band["bottom"], thin))
        touching = [gap for gap in gaps if gap[0] < SLIVER]
        if touching:
            host = bands[min(touching)[1]]
            host["top"] = min(host["top"], band["top"])
            host["bottom"] = max(host["bottom"], band["bottom"])
            host["x0"] = min(host["x0"], band["x0"])
            host["x1"] = max(host["x1"], band["x1"])

def page_ink(page, rendered, margin):
    """The page's display ink in bands, and the running text taken out of it.

    Running text is masked first, over its own columns only, so the last line
    of an introducing sentence never joins the display it precedes even where
    the two print less than a point apart. What remains is banded: one band
    per connected block of display ink, whatever its height.
    """
    with Image.open(rendered) as image:
        mask = image.convert("L").point(lambda level: 255 if level < INK_LEVEL else 0)
        scale = page.height / mask.height
        at = lambda point, limit: max(0, min(limit, int(round(point / scale))))
        blocks = []
        for row in printed_rows(page):
            if not running_text(row, margin, page.width):
                continue
            left, right = at(row["x0"] - 1, mask.width), at(row["x1"] + 1, mask.width)
            if left >= right:
                continue
            strip = mask.crop((left, 0, right, mask.height))
            covered = [(a, b) for a, b in ink_runs(strip)
                       if a * scale < row["bottom"] and row["top"] < b * scale]
            if not covered:
                continue
            top, bottom = covered[0][0], covered[-1][1]
            blocks.append((top * scale, bottom * scale))
            mask.paste(0, (left, top, right, bottom))
        bands = []
        for a, b in ink_runs(mask):
            if not FOLIO[0] < a * scale < FOLIO[1]:
                continue
            box = mask.crop((0, a, mask.width, b)).getbbox()
            bands.append({"top": a * scale, "bottom": b * scale,
                          "x0": box[0] * scale, "x1": box[2] * scale, "tag": None})
    fold_slivers(bands)
    for word in page.extract_words(x_tolerance=2, y_tolerance=3):
        if not (EQUATION_TAG.fullmatch(word["text"]) and word["x1"] > page.width - 90):
            continue
        middle = (word["top"] + word["bottom"]) / 2
        for band in bands:
            if band["top"] - 1 <= middle <= band["bottom"] + 1:
                band["tag"] = word["text"]
                break
    return bands, sorted(blocks)

def page_measures(lines):
    """This page's left text margin and its printed body-line pitch.

    The pitch is measured between consecutive full prose lines: list items and
    display rows are set further apart and would inflate a plain median.
    """
    columns = collections.Counter(round(line["x0"]) for line in lines if len(lettered(line)) >= 5)
    frequent = [x for x, count in columns.items() if count >= 3]
    spans = [(a, b) for a, b in zip(lines, lines[1:]) if 10 < b["top"] - a["top"] < 32]
    steps = sorted(b["top"] - a["top"] for a, b in spans if len(lettered(a)) >= 5 and len(lettered(b)) >= 5)
    steps = steps or sorted(b["top"] - a["top"] for a, b in spans)
    # Body pitch is the tightest spacing the page repeats: list items and
    # displays are set further apart and would inflate a median.
    repeated = [step for step, count in collections.Counter(round(s * 2) / 2 for s in steps).items() if count >= 3]
    pitch = min(repeated) if repeated else (steps[len(steps) // 2] if steps else 14.0)
    return min(frequent) if frequent else 72.0, pitch

def line_facts(line, margin, width):
    """How a printed line reads: display or text, heading, header, proof."""
    words, letters = line["words"], lettered(line)
    tagged = any(EQUATION_TAG.fullmatch(word["text"]) and word["x1"] > width - 90 for word in words)
    return {
        # Prose runs from the margin; a display is centred, or tagged, or has
        # too few ordinary words to be a printed line of text.
        "prose": line["x0"] <= margin + 20 and len(letters) >= 3 and not tagged,
        # A short margin line with no mathematics at all - "Thus", "satisfies" -
        # is running text too, and ends a display even though it is not prose.
        "aside": (line["x0"] <= margin + 20 and len(letters) >= 1 and not tagged
                  and all(word["size"] < 9 or TEXT_FONT.search(word["fontname"]) for word in words)),
        "words": len(letters),
        "tagged": bool(tagged),
        "heading": line["x0"] <= margin + 6 and any(
            word["size"] >= 11.5 and BOLD.search(word["fontname"]) for word in words),
        "header": bool(len(words) >= 2 and words[0]["text"] in ENVIRONMENT_WORDS
                       and NUMBERED.fullmatch(words[1]["text"]) and line["x0"] <= margin + 6
                       and abs(words[1]["top"] - words[0]["top"]) < 2
                       and ((BOLD.search(words[0]["fontname"]) and BOLD.search(words[1]["fontname"]))
                            or (SLANTED.search(words[0]["fontname"]) and SLANTED.search(words[1]["fontname"])))),
        "proof": bool(words) and words[0]["text"] in PROOF_WORDS and line["x0"] <= margin + 6,
        "italic": (sum(1 for word in letters if SLANTED.search(word["fontname"])) / len(letters)) if letters else 0.0,
    }

def closing_words(text, offset):
    """The statement environment's own closing words, from the manuscript.

    Only a trailing run of ordinary words counts, so a statement ending in a
    display simply has none and the printed layout decides instead.
    """
    starts = [m for m in ENVIRONMENT_START.finditer(text) if m.start() < offset]
    for match in reversed(starts):
        name = match.group(1)
        if name.rstrip("*").lower() not in STATEMENT_ENVIRONMENTS:
            continue
        depth, close = 0, None
        for step in re.finditer(r"\\(begin|end)\{" + re.escape(name) + r"\}", text[match.start():]):
            depth += 1 if step.group(1) == "begin" else -1
            if depth == 0:
                close = match.start() + step.start()
                break
        if close is None or close < offset:
            continue
        body = re.sub(r"(?<!\\)%.*", "", text[match.end():close]).rstrip()
        run = CLOSING_RUN.search(body)
        return run.group(0).split()[-8:] if run else []
    return []

def normalized(text):
    return "".join(c for c in unicodedata.normalize("NFKD", text).lower() if c in ALPHANUMERIC)

def locate_closing(lines, first, stop, words):
    """Every line on which the statement's closing words finish.

    Letters are compared without spacing or punctuation, so a word broken by
    an end-of-line hyphen still matches. The longest tail that occurs at all
    wins; a statement whose closing words carry a subscript matches on fewer.
    """
    letters, owner = [], []
    for index in range(first, stop):
        for word in sorted(lines[index]["plain"], key=lambda w: w["x0"]):
            for character in normalized(word["text"]):
                letters.append(character)
                owner.append(index)
    printed = "".join(letters)
    for length in range(len(words), 2, -1):
        target = normalized(" ".join(words[-length:]))
        hits, at = [], 0
        while target:
            at = printed.find(target, at)
            if at < 0:
                break
            hits.append(owner[at + len(target) - 1])
            at += 1
        if hits:
            return hits
    return []

def paragraph_start(lines, facts, index, indent, pitch):
    """A printed line that starts a new indented paragraph."""
    return (abs(lines[index]["x0"] - indent) <= 3 and facts[index]["words"] >= 2
            and lines[index]["top"] - lines[index - 1]["top"] > 1.2 * pitch)

def statement_extent(lines, facts, index, margin, pitch, blockers, closing):
    """Grow a statement box from its header to its last line on this page."""
    stop, terminator = len(lines), "page-end"
    for following in range(index + 1, len(lines)):
        if following in blockers or facts[following]["header"]:
            stop, terminator = following, "next-statement"
            break
        if facts[following]["proof"]:
            stop, terminator = following, "proof"
            break
        if facts[following]["heading"]:
            stop, terminator = following, "section-heading"
            break
    # amsthm sets plain statements in italic and definition-like ones upright,
    # so the body's own style says which printed line can end it.
    body = next((facts[i] for i in range(index + 1, stop) if facts[i]["prose"]), None)
    slanted = (body or facts[index])["italic"] >= 0.6
    styled, reason, indent = None, None, margin + 17
    for following in range(index + 1, stop):
        fact = facts[following]
        fresh = paragraph_start(lines, facts, following, indent, pitch)
        if not (fact["prose"] or fresh):
            continue                          # a display never ends a statement
        ended = fact["italic"] < 0.4 if slanted else fresh
        if ended:
            styled, reason = following - 1, "upright-paragraph" if slanted else "new-paragraph"
            break
    hits = locate_closing(lines, index, stop, closing) if closing else []
    if hits:
        aim = styled if styled is not None else stop - 1
        return min(hits, key=lambda hit: (abs(hit - aim), hit)), "source-end", True
    if styled is not None:
        return styled, reason, False
    return stop - 1, terminator, False

def display_seat(model, number, index, inherited):
    """The ink band carrying this display's printed number.

    The printed number is the display's own identifier, so it locates the
    display directly; where a page prints the same number twice, the one
    nearest the compiled location is this display's. A display printed
    without a number - the two unnumbered anchors whose AUX entry inherits a
    neighbour's number - is seated on the band holding the row its verified
    location points at instead.
    """
    base = model["lines"][index]["base"]
    tag = None if inherited else "(%s)" % number
    seats = [i for i, band in enumerate(model["bands"]) if tag and band["tag"] == tag]
    if seats:
        return min(seats, key=lambda i: abs(model["bands"][i]["top"] - base)), "ink-cluster"
    holding = [i for i, band in enumerate(model["bands"])
               if band["top"] - 1 <= base <= band["bottom"] + 1]
    require(holding, "No printed ink at a display's verified location")
    return holding[0], "ink-cluster-located"

def display_cluster(model, seat):
    """The block of display ink one printed number claims.

    Running text closes a block of display ink. Inside a block every printed
    number owns its own row, and a row printed without one - a row of an
    aligned display set \\nonumber, a large operator's limit line, a case
    brace - belongs to the number nearest to it.
    """
    bands, blocks = model["bands"], model["blocks"]
    parted = lambda i, j: any(bands[i]["bottom"] - 1 < close and open_ < bands[j]["top"] + 1
                              for open_, close in blocks)
    first, last = seat, seat
    while first and not parted(first - 1, first):
        first -= 1
    while last + 1 < len(bands) and not parted(last, last + 1):
        last += 1
    owners = sorted({i for i in range(first, last + 1) if bands[i]["tag"]} | {seat})
    reach = lambda i: bands[seat]["top"] - bands[i]["bottom"] if i < seat else \
        bands[i]["top"] - bands[seat]["bottom"]
    start, end = seat, seat
    for index in range(seat - 1, first - 1, -1):
        rival = max((o for o in owners if o < index), default=None)
        if index in owners or (rival is not None
                               and bands[index]["top"] - bands[rival]["bottom"] < reach(index)):
            break
        start = index
    for index in range(seat + 1, last + 1):
        rival = min((o for o in owners if o > index), default=None)
        if index in owners or (rival is not None
                               and bands[rival]["top"] - bands[index]["bottom"] < reach(index)):
            break
        end = index
    # Running text is masked out of the ink, so a block that is the last one
    # on its page has still ended in text if any is printed below it.
    ended = ("next-number" if end + 1 < len(bands) and not parted(end, end + 1)
             else "running-text" if any(open_ > bands[end]["bottom"] for open_, _ in blocks)
             else "page-end")
    return start, end, ended

def continues_overleaf(following, kind, indent):
    """Whether the page after a box that reached the page end carries more of it.

    A statement continues unless the next page opens something else: a proof,
    a heading, another statement, or a fresh indented paragraph. A display
    continues only if the next page opens with display ink; a line of running
    text printed above that ink - the sentence introducing the next display -
    means this one ended at the foot of its own page.
    """
    if not following or not following["lines"]:
        return False
    if kind in DISPLAY_KINDS:
        if not following["bands"]:
            return False
        opens = following["bands"][0]["top"]
        return not any(start < opens for start, _ in following["blocks"])
    opening, line = following["facts"][0], following["lines"][0]
    if opening["heading"] or opening["header"] or opening["proof"]:
        return False
    return not (abs(line["x0"] - indent) <= 3 and opening["words"] >= 2)

def page_model(page, rendered):
    """One page's printed lines and printed ink, with the measures box rules read."""
    lines = visual_lines(page)
    margin, pitch = page_measures(lines)
    bands, blocks = page_ink(page, rendered, margin)
    return {"lines": lines, "margin": margin, "pitch": pitch,
            "bands": bands, "blocks": blocks,
            "plain": [word for word in page.extract_words(x_tolerance=2, y_tolerance=3)
                      if FOLIO[0] < word["top"] < FOLIO[1]],
            "width": page.width, "height": page.height,
            "facts": [line_facts(line, margin, page.width) for line in lines]}

def band_text(model, band):
    """The readable text of one printed ink band."""
    inside = [word for word in model["plain"]
              if band["top"] - 1 <= (word["top"] + word["bottom"]) / 2 <= band["bottom"] + 1]
    inside.sort(key=lambda word: (round(word["top"] / 3), word["x0"]))
    return " ".join(word["text"] for word in inside)

def display_box(model, start, end):
    """The rectangle around a run of display ink, kept clear of its neighbours.

    Three points of breathing room, but never past the halfway point to the
    printed row on either side, so a highlight never reaches into a
    neighbouring display or into the sentence that introduces this one.
    """
    bands, blocks = model["bands"], model["blocks"]
    covered = bands[start:end + 1]
    top = min(band["top"] for band in covered)
    bottom = max(band["bottom"] for band in covered)
    above = max([bands[start - 1]["bottom"] if start else 0.0]
                + [close for _, close in blocks if close <= top])
    below = min([bands[end + 1]["top"] if end + 1 < len(bands) else model["height"]]
                + [open_ for open_, _ in blocks if open_ >= bottom])
    x0 = min(band["x0"] for band in covered) - 3
    x1 = max(band["x1"] for band in covered) + 3
    y0 = min(top, max(top - 3, (top + above) / 2))
    y1 = max(bottom, min(bottom + 3, (bottom + below) / 2))
    return {"x0": max(0, x0 / model["width"]), "y0": max(0, y0 / model["height"]),
            "x1": min(1, x1 / model["width"]), "y1": min(1, y1 / model["height"])}

def anchor_line(model, kind, top):
    """The printed line a compiled destination points at.

    LaTeX puts a display's destination on the line that introduces it, so a
    display box would otherwise open on a sentence. Step onto the display.
    """
    lines, facts = model["lines"], model["facts"]
    require(lines, "Empty PDF page for a named destination")
    # LaTeX places a destination a little above the line it names, so a line
    # printed above the destination is the weaker reading of the two.
    reach = lambda line: (top - line["base"]) * 1.5 if line["base"] < top else line["base"] - top
    index = min(range(len(lines)), key=lambda i: reach(lines[i]))
    running = facts[index]["prose"] or facts[index]["aside"] or (
        lines[index]["x0"] <= model["margin"] + 3 and not facts[index]["tagged"])
    if (kind in DISPLAY_KINDS and running and index + 1 < len(lines)
            and not (facts[index + 1]["prose"] or facts[index + 1]["aside"])
            and lines[index + 1]["x0"] > model["margin"] + 20
            and lines[index + 1]["top"] - lines[index]["top"] <= 1.9 * model["pitch"]):
        index += 1
    return index

def anchor_extent(model, index, kind, number, blockers, closing, following):
    """The printed rectangle, header text and extent record for one anchor.

    A display is boxed from the ink its printed number claims; a statement or
    heading is boxed from the printed lines it occupies.
    """
    lines, facts = model["lines"], model["facts"]
    margin, pitch = model["margin"], model["pitch"]
    if kind in DISPLAY_KINDS:
        seat, method = display_seat(model, number, index, kind == "unnumbered-equation")
        start, end, terminator = display_cluster(model, seat)
        cut = terminator == "page-end" and continues_overleaf(following, kind, margin + 17)
        extent = {"lines": end - start + 1, "terminator": terminator,
                  "sourceEndMatched": False, "truncatedAtPageEnd": cut, "method": method}
        return display_box(model, start, end), band_text(model, model["bands"][seat]), extent
    if kind in HEADING_KINDS:
        start, end, terminator, matched = index, index, "heading-line", False
    else:
        start = index
        end, terminator, matched = statement_extent(lines, facts, index, margin, pitch, blockers, closing)
    covered = lines[start:end + 1]
    x0 = min(line["x0"] for line in covered) - 3
    x1 = max(line["x1"] for line in covered) + 3
    # Three points of breathing room, but never into a neighbouring line.
    top = lines[start]["top"]
    bottom = max(line["bottom"] for line in covered)
    above = (lines[start - 1]["bottom"] + top) / 2 if start else 0
    below = (bottom + lines[end + 1]["top"]) / 2 if end + 1 < len(lines) else model["height"]
    y0 = min(top, max(top - 3, above))
    y1 = max(bottom, min(bottom + 3, below))
    rectangle = {"x0": max(0, x0 / model["width"]), "y0": max(0, y0 / model["height"]),
                 "x1": min(1, x1 / model["width"]), "y1": min(1, y1 / model["height"])}
    cut = (terminator == "page-end" and end == len(lines) - 1
           and continues_overleaf(following, kind, margin + 17))
    extent = {"lines": len(covered), "terminator": terminator, "sourceEndMatched": matched,
              "truncatedAtPageEnd": cut, "method": "printed-lines"}
    return rectangle, lines[index]["text"], extent

### Geometry gates ############################################################
# Two closed checks on the boxes the rules produced, measured against the
# printed ink itself rather than against the rules that drew them. Both fail
# the run: a wrong highlight is a wrong claim about the paper.
STRADDLE = 0.15  # of a printed row's height, the most an edge may cut off

def check_geometry(geometries, anchors):
    """No two display boxes may overlap, and no box edge may cut a printed row.

    Statement boxes legitimately contain display boxes, so only displays are
    checked against each other; every box, statement or display, is checked
    against the printed rows, because an edge through the middle of a row
    shows half a line of mathematics.
    """
    overlapping, straddling = [], []
    displays = collections.defaultdict(list)
    for anchor in anchors:
        if anchor["kind"] in DISPLAY_KINDS:
            displays[(anchor["paperId"], anchor["page"])].append(anchor)
    for boxes in displays.values():
        boxes.sort(key=lambda anchor: anchor["rectangles"][0]["y0"])
        for first, second in zip(boxes, boxes[1:]):
            a, b = first["rectangles"][0], second["rectangles"][0]
            if b["y0"] < a["y1"] and b["x0"] < a["x1"] and a["x0"] < b["x1"]:
                overlapping.append(first["id"] + " / " + second["id"])
    for anchor in anchors:
        model = geometries[anchor["paperId"]][anchor["page"]]
        rectangle = anchor["rectangles"][0]
        edges = (rectangle["y0"] * model["height"], rectangle["y1"] * model["height"])
        printed = [(band["top"], band["bottom"]) for band in model["bands"]] + model["blocks"]
        for top, bottom in printed:
            inset = STRADDLE * (bottom - top)
            if any(top + inset < edge < bottom - inset for edge in edges):
                straddling.append(f"{anchor['id']} at {top:.1f}-{bottom:.1f}")
    require(not overlapping, "Display highlights overlap: " + "; ".join(overlapping))
    require(not straddling, "Highlight edges cut printed rows: " + "; ".join(straddling))
    print(f"geometry gates: {len(displays)} pages of displays, 0 overlaps, 0 straddled rows")

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
             "Highlights box the printed extent of a labelled statement or display. A statement is boxed from its printed header line to its last line on that page (one continuing onto the next page is cut at the page end). A display is boxed from the connected block of printed ink its own number claims, so a fraction, a large operator's limit line, a case brace or a row set \\nonumber is inside the box whatever its height; rows sharing one block are divided between the numbers printed beside them. They do not delimit or certify proofs. Correspondence to Lean is curated, not compiler-derived."}
    diagnostics, geometries = [], {}
    for paper in data["papers"]:
        paper_id = paper["id"]
        pdf_path = repo / paper["path"]
        directory = pdf_path.parent.parent
        aux_path = directory / "build/main.aux"
        aux_text = aux_path.read_text(encoding="utf-8-sig")
        if revision:
            revised_paper = next(p for p in revision["papers"] if p["id"] == paper_id)
            require(digest(aux_path) == revised_paper["auxSha256"], "AUX differs from reviewed build")
        src_labels, src_texts, src_offsets = locate_label_sources(directory)
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
            # A second, finer greyscale rendering is the ink a display box is
            # measured from. It is local evidence only: the published page
            # images stay the 125 dpi colour ones written just below.
            subprocess.run(["pdftoppm", "-r", str(INK_DPI), "-gray", "-png", str(pdf_path),
                            str(Path(temporary) / "ink")], check=True, capture_output=True)
            inked = sorted(Path(temporary).glob("ink-*.png"), key=lambda p: int(p.stem.split("-")[-1]))
            require(len(inked) == len(reader.pages), "Ink rendering page count differs")
            for i, path in enumerate(rendered, 1):
                with Image.open(path) as image:
                    dest = paper_dir / f"page-{i:03d}.webp"
                    image.convert("RGB").save(dest, "WEBP", quality=84, method=4)
                    page_records.append({"page": i, "width": image.width, "height": image.height,
                                         "file": f"papers/{paper_id}/{dest.name}", "sha256": digest(dest)})
            with pdfplumber.open(pdf_path) as pdf:
                # Locate every anchor first: a statement box stops at the next
                # statement's printed header, so each page's other anchors are
                # part of the geometry and must be known before any box is grown.
                located, geometry = [], {}
                measure = lambda number: page_model(pdf.pages[number - 1], inked[number - 1])
                for record in labels(aux_text):
                    label = record["label"]
                    if label not in src_labels or record["destination"] not in destinations:
                        continue
                    destination = destinations[record["destination"]]
                    page_number = reader.get_destination_page_number(destination) + 1
                    destination_page = page_number
                    top = pdf.pages[page_number - 1].height - float(destination.top)
                    page_number, top, header = verified_statement_location(pdf, record, page_number, top)
                    kind = record["destination"].split(".")[0]
                    if header == "Unnumbered equation":
                        kind = "unnumbered-equation"
                    if page_number not in geometry:
                        geometry[page_number] = measure(page_number)
                    index = anchor_line(geometry[page_number], kind, top)
                    located.append((record, destination_page, page_number, top, header, kind, index))
                starts = collections.defaultdict(set)
                for _, _, page_number, _, _, kind, index in located:
                    starts[(page_number, kind in DISPLAY_KINDS)].add(index)
                for record, destination_page, page_number, top, header, kind, index in located:
                    label = record["label"]
                    blockers = starts[(page_number, False)] - {index}
                    closing = closing_words(src_texts[src_labels[label]["file"]], src_offsets[label]) \
                        if kind not in DISPLAY_KINDS | HEADING_KINDS else []
                    if page_number < len(pdf.pages) and page_number + 1 not in geometry:
                        geometry[page_number + 1] = measure(page_number + 1)
                    rect, excerpt, extent = anchor_extent(geometry[page_number], index, kind,
                                                          record["number"], blockers, closing,
                                                          geometry.get(page_number + 1))
                    mapping = by_anchor.get((paper_id, label))
                    title = plain_tex(record["titleTex"])
                    display_kind = header or {"equation": "Equation", "section": "Section", "subsection": "Section"}.get(kind, kind.capitalize())
                    record.update({"id": paper_id + ":" + label, "paperId": paper_id, "page": page_number,
                                   "compiledDestinationPage": destination_page,
                                   "locationVerification": "reviewed equation text; inherited destination corrected" if kind == "unnumbered-equation" else "printed numbered header" if header else "compiled PDF destination",
                                   "kind": kind, "title": display_kind + ("" if kind == "unnumbered-equation" else " " + record["number"]) + (" — " + title if kind != "equation" else ""),
                                   "rectangles": [{"page": page_number, **rect}], "excerpt": excerpt,
                                   "extent": extent,
                                   "source": src_labels[label], "lean": mapping["lean"] if mapping else [],
                                   "classification": mapping["classification"] if mapping else "unmapped",
                                   "note": mapping["note"] if mapping else "This paper location has no curated Lean correspondence in this edition. Use nearby mapped statements; do not infer formal coverage from its presence."})
                    trace["anchors"].append(record)
                    if kind == "unnumbered-equation":
                        record["note"] += " The display is unnumbered in the PDF; its AUX label inherits the preceding location and number. This highlight was corrected using the equation text, without changing the paper."
                    diagnostics.append({"id": record["id"], "kind": kind, "page": page_number,
                                        "file": f"papers/{paper_id}/page-{page_number:03d}.webp",
                                        "rect": rect, "extent": extent, "mapped": bool(mapping)})
                geometries[paper_id] = geometry
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
    check_geometry(geometries, trace["anchors"])
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
        "paperTrace": "Compiled PDF destinations locate labels; printed numbered statement headers verify and correct page-break locations. Each highlight then boxes the printed extent of that statement or display. A statement is measured in printed lines, from its header to its last line on that page, against the PDF's own text geometry and the manuscript's closing words, and is cut at the page end if it continues overleaf. A display is measured as printed ink: the connected block of ink its own printed number claims, so a fraction, a limit line under a large operator, a case brace or an aligned row set \\nonumber lies inside the box regardless of height, and rows sharing a block are divided between the numbers printed beside them. Two checks fail the build: display highlights may not overlap, and no highlight edge may cut through a printed row. Highlights do not delimit or certify proofs. Human-reviewed label/declaration mappings determine mathematical correspondence, which is not itself kernel-checked."}
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
        if paper_receipt.resolve() != (inputs / "paper-revision.json").resolve():
            shutil.copyfile(paper_receipt, inputs / "paper-revision.json")
    (inputs / "snapshot.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    review_sheets(inputs, diagnostics)
    print(json.dumps(manifest, indent=2))

# QA review sheets are local evidence for the extent heuristics, never public
# website assets: every anchor's page region is drawn with the box it produced,
# so each one can be checked by eye against the printed statement.
CELL, ROWS, COLUMNS, LABEL, PAD, CONTEXT = (748, 430), 4, 2, 22, 8, 24

def review_sheets(inputs, diagnostics):
    qa = ROOT / "qa"
    qa.mkdir(exist_ok=True)
    for stale in qa.glob("extent-*"):
        stale.unlink()
    try:
        font = ImageFont.truetype("arial.ttf", 15)
    except OSError:
        font = ImageFont.load_default()
    rank = lambda item: (0 if item["kind"] not in DISPLAY_KINDS | HEADING_KINDS else 1 if item["mapped"] else 2,
                         item["id"])
    ordered = sorted(diagnostics, key=rank)
    per_sheet = ROWS * COLUMNS
    width = COLUMNS * CELL[0] + (COLUMNS + 1) * PAD
    height = ROWS * (CELL[1] + LABEL) + (ROWS + 1) * PAD
    index = []
    pages = {}
    for batch in range(0, len(ordered), per_sheet):
        selected = ordered[batch:batch + per_sheet]
        name = f"extent-{batch // per_sheet + 1:02d}"
        sheet = Image.new("RGB", (width, height), "#e7ebf1")
        draw = ImageDraw.Draw(sheet)
        for slot, item in enumerate(selected):
            if item["file"] not in pages:
                pages[item["file"]] = Image.open(inputs / item["file"]).convert("RGB")
            page = pages[item["file"]]
            box = [item["rect"]["x0"] * page.width, item["rect"]["y0"] * page.height,
                   item["rect"]["x1"] * page.width, item["rect"]["y1"] * page.height]
            top = max(0, int(box[1]) - CONTEXT)
            bottom = min(page.height, int(box[3]) + CONTEXT)
            region = page.crop((0, top, page.width, bottom))
            marks = ImageDraw.Draw(region)
            marks.rectangle([box[0], box[1] - top, box[2], box[3] - top], outline="#d81b60", width=3)
            region.thumbnail(CELL)
            x = PAD + (slot % COLUMNS) * (CELL[0] + PAD)
            y = PAD + (slot // COLUMNS) * (CELL[1] + LABEL + PAD)
            rows = "row(s)" if item["extent"]["method"].startswith("ink") else "line(s)"
            caption = "{id} · {kind} · {method} · {terminator}{source} · {lines} {rows}{cut}{map}".format(
                id=item["id"], kind=item["kind"], method=item["extent"]["method"],
                terminator=item["extent"]["terminator"],
                source="+src" if item["extent"]["sourceEndMatched"] else "",
                lines=item["extent"]["lines"], rows=rows,
                cut=" · CUT AT PAGE END" if item["extent"]["truncatedAtPageEnd"] else "",
                map=" · MAPPED" if item["mapped"] else "")
            draw.text((x, y + 3), caption, fill="#101418", font=font)
            sheet.paste(region, (x, y + LABEL))
            index.append(f"{name} slot {slot + 1}: {caption}")
        sheet.save(qa / (name + ".png"))
    for page in pages.values():
        page.close()
    (qa / "extent-index.txt").write_text("\n".join(index) + "\n", encoding="utf-8")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--snapshot", required=True, type=Path)
    parser.add_argument("--mappings", nargs="+", required=True, type=Path)
    parser.add_argument("--paper-receipt", type=Path)
    args = parser.parse_args()
    prepare(args.repo.resolve(), args.snapshot.resolve(), args.mappings, args.paper_receipt)
