# Code Tutor V2 — Architecture & Design Specification

> **Purpose of this document:** Provide a complete, self-contained technical overview of `201_code_tutor_v2` so another developer or AI agent can immediately understand the codebase, design constraints, internal data structures, APIs, and roadmap without re-reading the entire 9,969-line single-file source (`code_tutor.py`).

---

## 1. Project Overview & Core Design Constraints

**Code Tutor V2** (`code_tutor.py`) is a **single-file, offline-capable static code analyzer + interactive 1:1 AI code tutor** tailored for studying complex engineering codebases (primarily **MATLAB `.m`**, **Python `.py`**, **C/C++**, **JS/TS/TSX**) alongside domain research papers (`.pdf`, `.pd`, `.md`, `.txt`).

### Non-Negotiable Design Constraints
1. **Single-File Portability:** Users deploy updates to air-gapped (closed-network) Windows PCs by copying **only `code_tutor.py`**. No Node/React build step, no external CSS/JS files, and no external asset files (even the ADD logo is embedded as Base64 PNG inside `code_tutor.py`).
2. **Stdlib-First with Graceful Degradation:** Must run on Python 3.10–3.14 standard library alone. Optional packages (`tree-sitter*`, `pymupdf`, `pymupdf4llm`, `pypdf`) enhance AST precision and PDF parsing when present, but never block startup if missing.
3. **Read-Only Target Projects:** Never writes cache or HTML files into the analyzed target repository; all generated HTML, caches, and study state are stored under `WORKSPACES_ROOT` (`<app_dir>/workspaces/<project_hash>/`).
4. **No Heavy Vector DB / Embedding Runtime:** Closed-network target PCs may have no embedding server or GPU Python stack; paper retrieval uses an in-process BM25-like TF-IDF index + optional OpenAI-compatible LLM query expansion and reranking.
5. **Windows & Korean Path Safety:** File/folder pickers use PowerShell/Tkinter subprocesses communicating via Base64/ASCII JSON (`ensure_ascii=True`). Server restart (`--serve`) checks `code_hash` via `/api/status` and cleanly shuts down stale `pythonw.exe` instances via `POST /api/shutdown`.

---

## 2. High-Level Architecture

```text
+-------------------------------------------------------------------+
| CLI / GUI Entry (main, launch_gui, run_pipeline)                  |
+-------------------------------------------------------------------+
        |                                         |
        v                                         v
+-------------------------------+       +---------------------------+
| Static Analyzer               |       | PaperWikiManager          |
| - Project (Python AST)        |       | - _extract_pdf_pages      |
| - ForeignMixin (TS / MATLAB)  |       | - _chunk_sections (v5)    |
| - ResolverMixin (Call/Var/Dep)|       | - BM25 TF-IDF + ProseWt   |
+-------------------------------+       +---------------------------+
        |                                         |
        v                                         |
+-------------------------------+                 |
| AIEnricher + Validator        |                 |
| - Batch static/LLM enrichment |                 |
| - Grounding check (anti-hall.)|                 |
+-------------------------------+                 |
        |                                         |
        v                                         v
+-------------------------------------------------------------------+
| build_html() -> Single Self-Contained HTML (3-Pane Workbench UI)  |
+-------------------------------------------------------------------+
        ^                                         ^
        | HTTP JSON API (localhost:8765)          |
+-------------------------------------------------------------------+
| create_tutor_server + TutorEngine (--serve)                       |
| - brief(), answer_question(), _wiki_refs() (Expand + Rerank)      |
| - translate_wiki_snippet(), open_wiki_doc(), LLMCache             |
+-------------------------------------------------------------------+
```

---

## 3. Backend Components (`code_tutor.py`, 9,969 lines)

### 3.1 Static Code Analysis (`L511–L3691`)
- **`FileRec` (`L511–L580`) & `Unit` (`L583–L632`)**: Core models representing source files and code units (`m`: module/script, `c`: class, `f`: function/method), metrics (LOC, cyclomatic complexity, nesting depth, difficulty), variable defs/uses, call edges, side effects, and step chunks.
- **`ResolverMixin` (`L770–L1025`)**: Resolves cross-file imports, module maps, class/attribute types, and call targets.
- **`ForeignMixin` (`L1042–L1948`)**:
  - Uses `tree-sitter` for C, C++, JS, TS, TSX when installed (with brace fallback `_build_brace_fallback_units`).
  - Dedicated MATLAB parser (`_build_matlab_units`, `_walk_matlab_scope`) handling scripts, functions, `global` variables, matrix/vector calls, and multi-return signatures (`[a, b] = func(...)`).
- **`Project` (`L1952–L3691`)**: Orchestrates file loading, unit construction, dependency graph, cycle marking (`mark_cycles`), static summaries, logical step segmentation (`compute_steps`), and bottom-up/top-down learning order (`learning_order`).

### 3.2 LLM Client, Grounding & Batch Enrichment (`L3706–L4331`)
- **`LLMClient` (`L3712–L3798`)**: OpenAI-compatible HTTP client (`urllib.request`, `/models`, `/chat/completions`).
  - `_ssl_ctx()` clears `ssl.VERIFY_X509_STRICT` (enabled by default in Python 3.14) while preserving standard TLS certificate/hostname verification, preventing `Missing Authority Key Identifier` errors behind corporate proxies or Google APIs.
- **Text & TeX Sanitizer (`_TEX_MAP`, `sanitize_tex`, `clean_llm_text`, `L3799–L3901`)**: Strips `<think>...</think>` reasoning tags, converts LaTeX/pipe-escaped math tokens (`\epsilon`, `|epsilon`, `\Delta`, `\frac{a}{b}`, `\sqrt{x}`, arrows, Greek letters) to Unicode/plain text, and unwraps `$...$` expressions (preserving currency like `$100`).
- **`Validator` (`L3967–L4054`)**: Verifies LLM-generated overview/function summaries against statically known identifiers (`ground()`) to reject hallucinated symbol names.
- **`LLMCache` (`L4121–L4146`)**: Thread-safe JSON key-value cache on disk.
- **`AIEnricher` (`L4177–L4331`)**: Parallel worker pool for generating project overview and per-unit batch explanations.

### 3.3 Paper / Wiki Extraction, Chunking & Retrieval (`L7424–L8258`)
- **Supported Extensions:** `.pdf`, `.pd` (security-renamed PDFs), `.md`, `.markdown`, `.txt`.
- **PDF Extraction Fallback Chain (`_extract_pdf_pages`, `L7689–L7790`):**
  1. `pymupdf4llm.to_markdown(..., page_chunks=True)` (2-column reading order, headings, tables)
  2. `pymupdf` (`fitz`) `pg.get_text("blocks")` with `_is_noise_pdf_block()`
  3. `pypdf` / `PyPDF2`
  4. `pdfplumber`
  5. `pdftotext` CLI
  6. Pure-stdlib PDF stream/ToUnicode CMap extractor (`_extract_pdf_stdlib`)
- **Noise & Artifact Filtering:**
  - `_is_noise_pdf_block()` (`L7654–L7672`): Filters header/footer margins (top/bottom 5.5%), TOC dot leaders (`..... 12`), short diagram/axis label blocks, and numeric-only blocks.
  - `_clean_paper_text()` (`L7448–L7464`): Strips `<!-- Start of picture text --> ... <!-- End of picture text -->`, `<br>`, soft hyphens (`\xad`), line-wrap hyphens, and legacy Symbol/MT Extra math font artifacts (`ð`→`(`, `Þ`→`)`, `¼`→`=`, PUA `\uf0xx`).
- **Sentence-Bounded Chunking (`_split_sentences_clean`, `_chunk_sections`, `L7824–L7862`, `chunk_ver = 5`):**
  - Joins visual PDF line wraps inside paragraphs and splits strictly on sentence boundaries (`max_chars=760`) so excerpts never cut mid-sentence.
- **`PaperWikiManager` (`L7865–L8258`):**
  - Persists index in `paper_wiki.json`. Supports `custom_sources` and `ignore_auto_dirs` (allowing users to exclude `proj_root/papers/`).
  - `build_llm_wiki()`: Generates one structured Korean Wiki summary card per paper (`핵심 주제/알고리즘`, `주요 수식·기호·변수 매핑`, `좌표계·가정·제약`).
  - `search()`: BM25-weighted TF-IDF over chunks + `_prose_quality_factor()` (boosts multi-sentence prose, penalizes `[1]` citation lists and fragments) + Wiki summary bonus, enforcing `per_doc_limit` diversity and attaching `wiki_summary` + `wiki_is_llm` to each hit.

### 3.4 1:1 Tutor Engine & LLM-Enhanced Retrieval (`L8261–L9327`)
- **`TutorEngine._wiki_refs()` (`L8313–L8336`):**
  - **Without LLM:** Runs BM25 `self.wiki.search(..., top_k=6, per_doc_limit=2)`.
  - **With LLM (`_active_llm_client`):**
    1. `_llm_expand_wiki_query()` (`L8339–L8373`): Extracts 6–10 English academic keywords/algorithm names from the code slice (or returns `__NONE__` for trivial utility/logging code). Cached in `wiki_q_cache.json`.
    2. Runs wide BM25 search (`top_k=12, per_doc_limit=3`).
    3. `_llm_rerank_wiki_refs()` (`L8375–L8428`): Selects up to 4 directly relevant excerpts AND generates a concise 1–2 sentence Korean **`code_link`** explanation describing how the code connects to that specific paper excerpt. Cached in `wiki_q_cache.json`.
- **`_format_wiki_prompt()` (`L8430–L8442`):** Injects up to 4 matched snippets (capped at 1,700 chars) into `brief()` and `answer_question()` prompts.
- **`brief()` (`L8870–L8970`):** Produces structured 1:1 tutor cards (`🎯 핵심 의도`, `🔢 논리 흐름`, `🔄 데이터 연결`, `⚠ 포인트`, `suggestions`, `refs`). Even on LLM cache hits, `refs` are refreshed from the current `PaperWikiManager` index.
- **`answer_question()` (`L9220–L9305`):** Multi-turn Q&A (`max_tokens=2400`, appends truncation notice if `finish_reason == "length"`).
- **`translate_wiki_snippet()` & `open_wiki_doc()`:** On-demand Korean translation of original paper snippets (cached in `wiki_tr_cache.json`) and OS-native file launch (`os.startfile` on Windows).

---

## 4. Frontend UI & Rendering Pipeline (`L4401–L7198`)

Embedded HTML/CSS/JS inside `code_tutor.py` (`load_template` / `build_html`):
- **3-Pane Workbench:**
  - **Left:** Project switcher, Paper/Wiki modal trigger, file/learning-order/caution/history tabs, unit tree.
  - **Center:** `① 개요` (KPIs, bulleted summary + divider, file dependency SVG + pop-out), `② 그래프` (interactive call graph + bidirectional pop-out window), `③ 코드보기` (`content-visibility: auto` virtualized lines, step selector).
  - **Right:** `🎓 1:1 튜터`, `🔎 변수 추적`, `🗺 흐름·구조`.
- **Markdown & Formula Renderer (`L4883–L5055`):**
  - `sanitizeTex()`: Strips `<!-- Start/End of picture text -->`, `<br>`, converts Greek/math commands, unwraps `$...$`.
  - `md()`: Handles `□` cleanup, `<sup>`/`<sub>`, `**bold**`, `_italic_` (preserving `snake_case`), `` `code` ``.
  - `mdBlock()`: Renders GFM tables (`.md-tbl-wrap`), `#{1,6}` section headers, `<ul>`, `<ol>`, `>`, and sentence-broken `<p>` via `_splitSentencesSafe()` + `_normInlineBullets()`.
  - `fmtSummary()` & `fmtFlowStep()`: Renders `🎯 핵심 의도`, `🔢 논리 흐름` (single outer bullet + indented sub-bullets, no double bullets), `🔄 데이터 연결`, `⚠ 포인트`.
- **Reference Card (`renderWikiRefs`, `L5925–L5965`):**
  - Default view: **`code_link`** (Korean code-to-paper connection explanation) when available, else **`orig`** (original paper excerpt).
  - Per-item controls: `[원문 발췌 / 연결 해설]`, `[Wiki 요약 / Wiki 닫기]`, `[한글 / 원문]` (enabled only in `orig` view), `[접기 / 펼치기]`, and clickable `📄 doc_name` to open the source file.

---

## 5. HTTP Server API (`create_tutor_server`, `L9330–L9532`)

| Method | Endpoint | Purpose |
| :--- | :--- | :--- |
| `GET` | `/api/status` | Server `code_hash`, LLM config, study state, prewarm, wiki status |
| `GET` | `/api/projects` | List known workspaces under `workspaces/` |
| `GET` | `/api/wiki/status` | Indexed docs, chunk counts, `auto_dirs`, `custom_sources` |
| `GET` | `/api/wiki/doc?id=...` | Document summary + first 25 extracted chunks |
| `POST` | `/api/config` | Save & preflight-test LLM settings (`.code_tutor_config.json`) |
| `POST` | `/api/brief` | Get/generate 1:1 tutor brief for `(unit_id, l1, l2, level)` |
| `POST` | `/api/chat` | Ask follow-up question in thread |
| `POST` | `/api/delete_msg` | Delete a specific Q&A pair from `tutor_threads.json` |
| `POST` | `/api/clear_thread` | Clear entire Q&A thread for a unit |
| `POST` | `/api/pin` | Pin/unpin note to top of tutor pane |
| `POST` | `/api/prewarm` | Start/stop background brief pre-generation |
| `POST` | `/api/study_state` | Persist `done` / `bookmarks` / `last` |
| `POST` | `/api/project_switch` / `_browse` / `_remove` | Switch, pick, or delete workspace |
| `POST` | `/api/wiki/index` | `scan`, `add_path`, `browse_dir`, `browse_files`, `remove_source`, `build_llm` |
| `POST` | `/api/wiki/translate` | Translate paper excerpt to Korean (`wiki_tr_cache.json`) |
| `POST` | `/api/wiki/open` | Open original paper file in OS default viewer |
| `POST` | `/api/shutdown` | Gracefully shut down server for version upgrade |

---

## 6. Workspace & Persistence Layout

- **Global config:** `<script_dir>/.code_tutor_config.json` (LLM `base_url`, `model`, `api_key`, `extra_body`, `last_dir`, etc. — **exclude from Git**)
- **Per-project workspace:** `<script_dir>/workspaces/<name>_<sha1_6>/` (**exclude from Git**)
  - `<name>_code_tutor.html`: Generated standalone HTML
  - `project_info.json`: Project root path & timestamp
  - `paper_wiki.json`: Extracted chunks, Wiki summaries, `custom_sources`, `ignore_auto_dirs`
  - `llm_tutor_cache.json`: Cached `brief()` responses
  - `wiki_q_cache.json`: Cached LLM query expansions & rerank/`code_link` results
  - `wiki_tr_cache.json`: Cached Korean translations of paper snippets
  - `tutor_threads.json`: Per-unit Q&A history, pins, bookmarks, done flags

---

## 7. Known Limitations & Planned V3 (`202_code_tutor_v3`) Direction

1. **PDF Equation & Figure Fidelity:** `pymupdf` / `pymupdf4llm` still breaks complex 2D matrix/integral layouts (`□`, `ð`, `Z` for `∫`) in raw text excerpts.
2. **Next-Gen Integration (`USDL`):** Pair `code_tutor` with `D:\Project\USDL` (Docling layout parser + GPU `CodeFormulaV2` + extracted figure/formula image assets + `content.md` / `metadata.yaml`) so code-to-paper excerpts can display clean Markdown alongside cropped formula/figure images.
