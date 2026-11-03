#!/usr/bin/env python3
"""Check Alpha Cycle HTML structure and, optionally, real offline browser rendering.

Run from any directory:
  python3 Papers/test_html_rendering.py
  python3 Papers/test_html_rendering.py --browser --screenshots-dir /tmp/alpha-shots

The browser check requires Playwright and its Chromium browser on the checking
machine. It never changes the paper or Lean sources and never uses the network.
"""

import argparse
import hashlib
import json
import re
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit


class PageInventory(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.prose = []
        self.scripts = []
        self.style_starts = 0
        self.style_ends = 0
        self.lean_boxes = 0
        self.source_links = []
        self.assets = []
        self.current_script = None

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag not in {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}:
            self.stack.append(tag)
        if tag == "style":
            self.style_starts += 1
        if tag == "script":
            self.current_script = []
        if tag == "details" and "lean-box" in attrs.get("class", "").split():
            self.lean_boxes += 1
        if tag == "a" and attrs.get("href", "").startswith("../Formalization/") and "#L" in attrs["href"]:
            self.source_links.append(attrs["href"])
        if tag in {"script", "img", "link", "iframe"}:
            url = attrs.get("src", attrs.get("href", ""))
            if url.startswith(("https://", "http://", "//")):
                self.assets.append(url)

    def handle_endtag(self, tag):
        if tag == "style":
            self.style_ends += 1
        if tag == "script" and self.current_script is not None:
            self.scripts.append("".join(self.current_script))
            self.current_script = None
        if tag in self.stack:
            index = len(self.stack) - 1 - self.stack[::-1].index(tag)
            del self.stack[index:]

    def handle_data(self, data):
        if self.current_script is not None:
            self.current_script.append(data)
        if "body" in self.stack and not any(tag in self.stack for tag in {"pre", "code", "script", "style"}):
            self.prose.append(data)


def static_checks(path):
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    inventory = PageInventory()
    inventory.feed(text)
    assert inventory.style_starts == inventory.style_ends, "Unbalanced style tags"
    assert text.count("@font-face") == 20, "KaTeX font-face rules were collapsed or lost"
    assert len(inventory.scripts) >= 3, "Missing inline KaTeX or math initializer script"
    assert any("renderMathInElement(document.body" in script for script in inventory.scripts), "Equation-rendering initializer is missing"
    assert not inventory.assets, "Page depends on external assets"
    assert inventory.lean_boxes == 19, "Lean boxes were lost or duplicated"
    assert len(inventory.source_links) == 47, "Source buttons were lost or duplicated"
    for url in inventory.source_links:
        parsed = urlsplit(url)
        source = (path.parent / unquote(parsed.path)).resolve()
        assert source.is_file(), "Source button target is missing: " + url
        match = re.fullmatch(r"L(\d+)-L(\d+)", parsed.fragment)
        assert match, "Source button line range is invalid: " + url
        lo, hi = map(int, match.groups())
        assert 1 <= lo <= hi <= len(source.read_text().splitlines()), "Source button line range is out of bounds: " + url
    prose = "".join(inventory.prose)
    expressions = re.findall(r"\\\((.*?)\\\)|\\\[(.*?)\\\]", prose, re.S)
    assert len(expressions) == 389, "Paper equations were lost or duplicated"
    assert prose.count(r"\(") == prose.count(r"\)"), "Unbalanced inline math delimiters"
    assert prose.count(r"\[") == prose.count(r"\]"), "Unbalanced display math delimiters"
    for phrase in ("Coverage ID", "Paper locator", "Status: KERNEL_CHECKED", "source unpublished", "Lean declaration"):
        assert phrase not in text, "An unwanted audit line returned: " + phrase
    return {
        "sha256": hashlib.sha256(raw).hexdigest(),
        "bytes": len(raw),
        "scripts": len(inventory.scripts),
        "style_tags": inventory.style_starts,
        "equations": len(expressions),
        "lean_boxes": inventory.lean_boxes,
        "source_links": len(inventory.source_links),
        "external_assets": inventory.assets,
    }


def browser_checks(path, expected, screenshots_dir):
    try:
        from playwright.sync_api import sync_playwright
    except ImportError as exc:
        raise SystemExit("Browser check requires Playwright and Chromium; no browser check was performed") from exc
    evidence = []
    if screenshots_dir:
        screenshots_dir.mkdir(parents=True, exist_ok=True)
    with sync_playwright() as runtime:
        browser = runtime.chromium.launch(headless=True, chromium_sandbox=True)
        context = browser.new_context(offline=True, viewport={"width": 1280, "height": 900}, device_scale_factor=1)
        page = context.new_page()
        errors = []
        page.on("pageerror", lambda error: errors.append(str(error)))
        page.goto(path.as_uri(), wait_until="load")
        page.wait_for_function("typeof katex !== 'undefined' && document.querySelectorAll('.katex').length > 0")
        page.evaluate("async () => { await document.fonts.ready; await Promise.all(Array.from(document.fonts, font => font.load())); }")
        for width in [1280, 390]:
            page.set_viewport_size({"width": width, "height": 900})
            metrics = page.evaluate(r"""() => {
                const clone = document.querySelector('main').cloneNode(true);
                clone.querySelectorAll('pre, code, script, style, .katex').forEach(element => element.remove());
                const text = clone.textContent;
                return {
                    width: innerWidth,
                    document_width: document.documentElement.scrollWidth,
                    rendered: document.querySelectorAll('.katex').length,
                    math_errors: Array.from(document.querySelectorAll('.katex-error')).map(element => ({text: element.textContent, error: element.title})),
                    unrendered_math_spans: Array.from(document.querySelectorAll('span.math')).filter(element => !element.querySelector('.katex')).map(element => element.textContent),
                    raw_delimiters: /\\[()[\]]/.test(text),
                    lean_boxes: document.querySelectorAll('details.lean-box').length,
                    source_buttons: Array.from(document.querySelectorAll('.srcline a')).filter(element => element.textContent === 'source').length,
                    styles_outside_tags: text.includes('.prov{') || document.body.textContent.includes('.prov{position:relative'),
                    main_contains_greek_alpha: Array.from(document.querySelectorAll('.katex-html')).some(element => element.textContent.includes('α')),
                    font_faces: Array.from(document.fonts).length,
                    font_failures: Array.from(document.fonts).filter(font => font.status !== 'loaded').map(font => font.family),
                    math_font: getComputedStyle(document.querySelector('.katex')).fontFamily,
                    visible_text_width: (() => { const canvas = document.createElement('canvas'); const ctx = canvas.getContext('2d'); ctx.font = '16px serif'; return ctx.measureText('Alpha Cycle').width; })()
                };
            }""")
            metrics["page_errors"] = list(errors)
            assert metrics["rendered"] == expected["equations"], metrics
            assert not metrics["math_errors"], metrics
            assert not metrics["unrendered_math_spans"], metrics
            assert not metrics["raw_delimiters"], metrics
            assert not metrics["page_errors"], metrics
            assert not metrics["styles_outside_tags"], metrics
            assert metrics["main_contains_greek_alpha"], metrics
            assert metrics["font_faces"] == 20 and not metrics["font_failures"], metrics
            assert "KaTeX_Main" in metrics["math_font"], metrics
            assert metrics["visible_text_width"] > 10, "Browser has no usable system text fonts"
            assert metrics["lean_boxes"] == expected["lean_boxes"], metrics
            assert metrics["source_buttons"] == expected["source_links"], metrics
            assert metrics["document_width"] <= width, metrics
            if screenshots_dir:
                page.screenshot(path=str(screenshots_dir / ("alpha-cycle-%d.png" % width)))
            evidence.append(metrics)
        page.set_viewport_size({"width": 1280, "height": 900})
        first = page.locator("details.lean-box").first
        assert not first.evaluate("element => element.open")
        first.locator(":scope > summary").click()
        assert first.evaluate("element => element.open"), "Lean box does not open"
        technical = first.locator("details.tech-detail")
        assert not technical.evaluate("element => element.open")
        if screenshots_dir:
            first.screenshot(path=str(screenshots_dir / "alpha-cycle-lean-box.png"))
        page.locator('nav a[href="#positive"]').click()
        assert page.evaluate("location.hash") == "#positive", "Navigation does not work"
        browser.close()
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--browser", action="store_true", help="Require an actual offline Chromium check")
    parser.add_argument("--html", type=Path, default=Path(__file__).with_name("alpha_cycle_interactive.html"))
    parser.add_argument("--screenshots-dir", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    path = args.html.resolve()
    result = {"static": static_checks(path)}
    if args.browser:
        result["browser"] = browser_checks(path, result["static"], args.screenshots_dir)
    else:
        result["browser"] = "Not run (use --browser to require real browser rendering)"
    rendered = json.dumps(result, indent=2)
    if args.report:
        args.report.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
