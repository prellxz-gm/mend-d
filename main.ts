// mend — one patch tool for every AI edit format.
// Implements SPEC.md v1: unified diffs, SEARCH/REPLACE blocks, V4A patches
// and JSON editor calls, with three-tier fuzzy matching and all-or-nothing
// writes. Node standard library only; erasable TypeScript only.

import { mkdirSync, readFileSync, rmSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

class ParseErr extends Error {
  n: number;
  constructor(n: number) {
    super(`parse ${n}`);
    this.n = n;
  }
}

interface Hunk {
  a: number;
  o: string[];
  n: string[];
  nMap: number[];
  plus: string[];
  noNL: boolean;
  plusNoNL: boolean;
}

interface USection {
  old: string | null | undefined;
  nw: string | null | undefined;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

interface VChunk {
  anchor: string | null;
  o: string[];
  n: string[];
  nMap: number[];
  eof: boolean;
}

interface VSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  lines: string[];
  chunks: VChunk[];
}

type JOp =
  | { command: 'create'; path: string; fileText: string }
  | { command: 'str_replace'; path: string; oldStr: string; newStr: string }
  | { command: 'insert'; path: string; insertLine: number; newStr: string };

type Edit =
  | { kind: 'u'; sec: USection }
  | { kind: 's'; path: string; oldLines: string[]; newLines: string[] }
  | { kind: 'v'; sec: VSection }
  | { kind: 'j'; op: JOp };

type Fail = { ok: false; code: string; path: string };
type Ok = { ok: true };
type ApplyResult = Ok | Fail;

function fail(code: string, path: string): Fail {
  return { ok: false, code, path };
}

interface FileParts {
  lines: string[];
  eol: string;
  ends: boolean;
}

interface Tree {
  disk: Map<string, string | null>;
  cur: Map<string, string | null>;
}

interface Ctx {
  strict: boolean;
  moves: { old: string; nw: string }[];
}

// ---------------------------------------------------------------------------
// Small helpers

function isSafe(p: string): boolean {
  if (p === '') return false;
  if (p.startsWith('/')) return false;
  if (p.includes('\\')) return false;
  for (const s of p.split('/')) {
    if (s === '' || s === '.' || s === '..') return false;
  }
  return true;
}

/** Patch lines: split at \n, one trailing \r removed per line, no empty piece after a final \n. */
function splitPatch(text: string): string[] {
  const parts = text.split('\n');
  if (parts.length > 0 && parts[parts.length - 1] === '') parts.pop();
  for (let i = 0; i < parts.length; i++) {
    if (parts[i].endsWith('\r')) parts[i] = parts[i].slice(0, -1);
  }
  return parts;
}

function parseFile(text: string): FileParts {
  const idx = text.indexOf('\n');
  const eol = idx > 0 && text[idx - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { lines: [], eol, ends: false };
  const parts = text.split(eol);
  let ends = false;
  if (parts[parts.length - 1] === '') {
    parts.pop();
    ends = true;
  }
  return { lines: parts, eol, ends };
}

function serFile(f: FileParts): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.eol) + (f.ends ? f.eol : '');
}

function byteCmp(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

function diskRead(t: Tree, p: string): string | null {
  if (!t.disk.has(p)) {
    try {
      t.disk.set(p, readFileSync(p, 'utf8'));
    } catch {
      t.disk.set(p, null);
    }
  }
  return t.disk.get(p) as string | null;
}

function curGet(t: Tree, p: string): string | null {
  if (t.cur.has(p)) return t.cur.get(p) as string | null;
  return diskRead(t, p);
}

function curSet(t: Tree, p: string, v: string | null): void {
  t.cur.set(p, v);
}

// ---------------------------------------------------------------------------
// Matching (SPEC section 5)

function normLine(l: string, tier: number): string {
  if (tier === 0) return l;
  if (tier === 1) return l.replace(/[ \t]+$/, '');
  return l.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

function occs(file: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  const no = o.map((l) => normLine(l, tier));
  for (let i = 0; i + o.length <= file.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (normLine(file[i + j], tier) !== no[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

function findTier(file: string[], o: string[], strict: boolean): { tier: number; occ: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const occ = occs(file, o, t);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

function leadingWs(l: string): string {
  const m = /^[ \t]*/.exec(l);
  return m ? m[0] : '';
}

/**
 * Build the replacement lines for a matched O at position pos.
 * Context lines (nMap[i] >= 0) are written as the file's own matched line.
 * At tier 2 every other line is re-indented: P (leading whitespace of O's
 * first line) replaced by F (leading whitespace of the file's first matched
 * line) when the line starts with P. At tiers 0/1 lines are written as-is.
 */
function buildNew(n: string[], nMap: number[], o: string[], file: string[], pos: number, tier: number): string[] {
  const out: string[] = [];
  let f = '';
  let p = '';
  if (tier === 2) {
    f = leadingWs(file[pos]);
    p = leadingWs(o[0]);
  }
  for (let i = 0; i < n.length; i++) {
    if (nMap[i] >= 0) {
      out.push(file[pos + nMap[i]]);
      continue;
    }
    const l = n[i];
    if (tier === 2 && l !== '' && !/^[ \t]+$/.test(l) && l.startsWith(p)) out.push(f + l.slice(p.length));
    else out.push(l);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Format detection (SPEC section 4)

function detectFormat(lines: string[]): string | null {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== '') {
      first = i;
      break;
    }
  }
  if (first === -1) return null;
  const fl = lines[first];
  if (fl.trim() === '*** Begin Patch') return 'v4a';
  const fch = fl.trimStart()[0];
  if (fch === '[' || fch === '{') return 'json';
  for (const l of lines) {
    if (l.trimEnd() === '<<<<<<< SEARCH') return 'search-replace';
  }
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('diff --git ')) return 'unified';
    if (lines[i].startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) return 'unified';
  }
  return null;
}

// ---------------------------------------------------------------------------
// Entry point

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  let seenFormat = false;
  let seenCheck = false;
  let seenStrict = false;
  let positional: string[] = [];
  let afterDashDash = false;
  for (const a of args) {
    if (!afterDashDash) {
      if (a === '--') {
        afterDashDash = true;
        continue;
      }
      if (a === '--check') {
        if (seenCheck) return { code: 2, out: ['error: usage'] };
        seenCheck = true;
        check = true;
        continue;
      }
      if (a === '--strict') {
        if (seenStrict) return { code: 2, out: ['error: usage'] };
        seenStrict = true;
        strict = true;
        continue;
      }
      if (a.startsWith('--format=')) {
        if (seenFormat) return { code: 2, out: ['error: usage'] };
        seenFormat = true;
        const v = a.slice('--format='.length);
        if (v !== 'auto' && v !== 'unified' && v !== 'search-replace' && v !== 'v4a' && v !== 'json') {
          return { code: 2, out: ['error: usage'] };
        }
        format = v;
        continue;
      }
      if (a.startsWith('-') && a !== '-') return { code: 2, out: ['error: usage'] };
    }
    positional.push(a);
  }
  if (positional.length > 1) return { code: 2, out: ['error: usage'] };
  const patchArg = positional.length === 0 ? undefined : positional[0];

  let patchText: string;
  if (patchArg === undefined || patchArg === '-') {
    patchText = readFileSync(0, 'utf8');
  } else {
    try {
      patchText = readFileSync(patchArg, 'utf8');
    } catch {
      return { code: 2, out: ['error: no-patch'] };
    }
  }
  const lines = splitPatch(patchText);

  let fmt = format;
  if (fmt === null || fmt === 'auto') {
    const d = detectFormat(lines);
    if (d === null) return { code: 2, out: ['error: format'] };
    fmt = d;
  }

  let edits: Edit[];
  try {
    if (fmt === 'unified') edits = parseUnified(lines);
    else if (fmt === 'search-replace') edits = parseSR(lines);
    else if (fmt === 'v4a') edits = parseV4A(lines);
    else edits = parseJSON(lines, patchText);
  } catch (e) {
    if (e instanceof ParseErr) return { code: 2, out: [`error: parse ${e.n}`] };
    throw e;
  }
  if (edits.length === 0) return { code: 2, out: ['error: parse 1'] };

  const tree: Tree = { disk: new Map(), cur: new Map() };
  const ctx: Ctx = { strict, moves: [] };
  const failures: { code: string; path: string }[] = [];
  for (const e of edits) {
    const r = applyEdit(e, tree, ctx);
    if (!r.ok) failures.push({ code: r.code, path: r.path });
  }
  if (failures.length > 0) {
    const out = failures.map((f) => `error: ${f.code} ${f.path}`);
    out.push(`failed: ${failures.length} of ${edits.length} edits`);
    return { code: 1, out };
  }

  const entries: { key: string; line: string }[] = [];
  const dSet = new Set<string>();
  const aSet = new Set<string>();
  for (const p of tree.cur.keys()) {
    const before = diskRead(tree, p);
    const after = tree.cur.get(p) as string | null;
    if (before === after) continue;
    if (before === null && after !== null) {
      entries.push({ key: p, line: `A ${p}` });
      aSet.add(p);
    } else if (before !== null && after === null) {
      entries.push({ key: p, line: `D ${p}` });
      dSet.add(p);
    } else {
      entries.push({ key: p, line: `M ${p}` });
    }
  }
  for (const m of ctx.moves) {
    if (dSet.has(m.old) && aSet.has(m.nw)) {
      for (let i = entries.length - 1; i >= 0; i--) {
        if (entries[i].line === `D ${m.old}` || entries[i].line === `A ${m.nw}`) entries.splice(i, 1);
      }
      dSet.delete(m.old);
      aSet.delete(m.nw);
      entries.push({ key: m.nw, line: `R ${m.old} -> ${m.nw}` });
    }
  }
  entries.sort((a, b) => byteCmp(a.key, b.key));
  const out = entries.map((e) => e.line);
  out.push(entries.length === 1 ? 'ok: 1 file' : `ok: ${entries.length} files`);

  if (!check) {
    for (const p of tree.cur.keys()) {
      const before = diskRead(tree, p);
      const after = tree.cur.get(p) as string | null;
      if (before === after) continue;
      if (after === null) {
        try {
          rmSync(p);
        } catch {
          // already gone
        }
      } else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, after);
      }
    }
  }
  return { code: 0, out };
}

// ---------------------------------------------------------------------------
// Unified diffs (SPEC section 6)

function parseHeaderPath(s: string): string | null {
  const t = s.split('\t')[0].trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/')) return t.slice(2);
  if (t.startsWith('b/')) return t.slice(2);
  return t;
}

function buildHunk(body: string[], a: number): Hunk {
  const o: string[] = [];
  const n: string[] = [];
  const nMap: number[] = [];
  const plus: string[] = [];
  for (const bl of body) {
    if (bl.startsWith('\\')) continue;
    if (bl === '') {
      o.push('');
      n.push('');
      nMap.push(o.length - 1);
      continue;
    }
    const c = bl[0];
    if (c === ' ') {
      const t = bl.slice(1);
      o.push(t);
      n.push(t);
      nMap.push(o.length - 1);
    } else if (c === '-') {
      o.push(bl.slice(1));
    } else if (c === '+') {
      n.push(bl.slice(1));
      nMap.push(-1);
      plus.push(bl.slice(1));
    }
  }
  let noNL = false;
  let lastCtxPlus = -1;
  for (let i = 0; i < body.length; i++) {
    if (body[i].startsWith(' ') || body[i].startsWith('+')) lastCtxPlus = i;
  }
  if (lastCtxPlus >= 0 && lastCtxPlus + 1 < body.length && body[lastCtxPlus + 1].startsWith('\\')) noNL = true;
  let plusNoNL = false;
  let lastPlus = -1;
  for (let i = 0; i < body.length; i++) {
    if (body[i].startsWith('+')) lastPlus = i;
  }
  if (lastPlus >= 0 && lastPlus + 1 < body.length && body[lastPlus + 1].startsWith('\\')) plusNoNL = true;
  return { a, o, n, nMap, plus, noNL, plusNoNL };
}

function parseUnified(lines: string[]): Edit[] {
  const secs: USection[] = [];
  let cur: USection | null = null;
  let inHeader = false;
  let headerHasPair = false;
  const n = lines.length;
  let i = 0;
  while (i < n) {
    const line = lines[i];
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)[ \t]*$/.exec(line);
      if (!m) throw new ParseErr(i + 1);
      cur = { old: m[1], nw: m[2], newFile: false, deletedFile: false, hunks: [] };
      secs.push(cur);
      inHeader = true;
      headerHasPair = false;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) {
      if (cur !== null && inHeader && !headerHasPair) {
        cur.old = parseHeaderPath(line.slice(4));
        cur.nw = parseHeaderPath(lines[i + 1].slice(4));
        headerHasPair = true;
        i += 2;
        continue;
      }
      cur = {
        old: parseHeaderPath(line.slice(4)),
        nw: parseHeaderPath(lines[i + 1].slice(4)),
        newFile: false,
        deletedFile: false,
        hunks: [],
      };
      secs.push(cur);
      inHeader = true;
      headerHasPair = true;
      i += 2;
      continue;
    }
    if (line.startsWith('--- ')) {
      if (cur !== null && inHeader) throw new ParseErr(i + 2);
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new ParseErr(i + 1);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
      if (!m) throw new ParseErr(i + 1);
      const hunkA = parseInt(m[1], 10);
      inHeader = false;
      i++;
      const body: string[] = [];
      while (i < n) {
        const bl = lines[i];
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          body.push(bl);
          i++;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      cur.hunks.push(buildHunk(body, hunkA));
      continue;
    }
    if (cur !== null && inHeader) {
      if (!headerHasPair) {
        if (line.startsWith('rename from ')) cur.old = line.slice('rename from '.length).trim();
        else if (line.startsWith('rename to ')) cur.nw = line.slice('rename to '.length).trim();
      }
      if (line.startsWith('new file mode')) cur.newFile = true;
      else if (line.startsWith('deleted file mode')) cur.deletedFile = true;
      i++;
      continue;
    }
    i++;
  }
  return secs.map((sec) => ({ kind: 'u', sec }) as Edit);
}

function applyHunks(fp: FileParts, hunks: Hunk[], strict: boolean, failPath: string): { ok: true; fp: FileParts } | Fail {
  let lines = fp.lines.slice();
  const eol = fp.eol;
  let ends = fp.ends;
  let d = 0;
  for (const h of hunks) {
    if (h.o.length === 0) {
      const ins = Math.min(h.a + d, lines.length);
      const atEnd = ins === lines.length;
      const nl = buildNew(h.n, h.nMap, h.o, lines, ins, 0);
      lines.splice(ins, 0, ...nl);
      if (atEnd) ends = !h.noNL;
      d += h.n.length;
      continue;
    }
    const found = findTier(lines, h.o, strict);
    if (!found) return fail('no-match', failPath);
    const target = h.a - 1 + d;
    let best = found.occ[0];
    let bestDist = Math.abs(best - target);
    for (const p of found.occ) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const nl = buildNew(h.n, h.nMap, h.o, lines, best, found.tier);
    const toEnd = best + h.o.length === lines.length;
    lines.splice(best, h.o.length, ...nl);
    if (toEnd) ends = !h.noNL;
    d += h.n.length - h.o.length;
  }
  return { ok: true, fp: { lines, eol, ends } };
}

function applyUnified(sec: USection, tree: Tree, ctx: Ctx): ApplyResult {
  const oldP = sec.old;
  const newP = sec.nw;
  if (oldP !== null && oldP !== undefined && !isSafe(oldP)) return fail('unsafe', oldP);
  if (newP !== null && newP !== undefined && !isSafe(newP)) return fail('unsafe', newP);
  const isCreate = oldP === null || sec.newFile;
  const isDelete = !isCreate && (newP === null || sec.deletedFile);
  if (isCreate) {
    const p = newP as string;
    if (p === null || p === undefined) return fail('unsafe', '');
    if (curGet(tree, p) !== null) return fail('exists', p);
    const plus: string[] = [];
    let ends = false;
    for (const h of sec.hunks) {
      if (h.plus.length > 0) ends = !h.plusNoNL;
      plus.push(...h.plus);
    }
    const content = plus.length === 0 ? '' : plus.join('\n') + (ends ? '\n' : '');
    curSet(tree, p, content);
    return { ok: true };
  }
  if (isDelete) {
    const p = oldP as string;
    if (p === null || p === undefined) return fail('unsafe', '');
    if (curGet(tree, p) === null) return fail('missing', p);
    curSet(tree, p, null);
    return { ok: true };
  }
  const oldPath = oldP as string;
  const newPath = newP as string;
  if (oldPath === newPath) {
    const cur = curGet(tree, oldPath);
    if (cur === null) return fail('missing', oldPath);
    const r = applyHunks(parseFile(cur), sec.hunks, ctx.strict, oldPath);
    if (!r.ok) return r;
    curSet(tree, oldPath, serFile(r.fp));
    return { ok: true };
  }
  const cur = curGet(tree, oldPath);
  if (cur === null) return fail('missing', oldPath);
  if (curGet(tree, newPath) !== null) return fail('exists', newPath);
  const r = applyHunks(parseFile(cur), sec.hunks, ctx.strict, oldPath);
  if (!r.ok) return r;
  curSet(tree, newPath, serFile(r.fp));
  curSet(tree, oldPath, null);
  ctx.moves.push({ old: oldPath, nw: newPath });
  return { ok: true };
}

// ---------------------------------------------------------------------------
// SEARCH/REPLACE blocks (SPEC section 7)

function parseSR(lines: string[]): Edit[] {
  const edits: Edit[] = [];
  let prevReplace = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i].trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let j = i - 1; j > prevReplace; j--) {
      const l = lines[j];
      if (l.trim() === '') continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new ParseErr(searchLine + 1);
      path = prevPath;
    }
    let j = i + 1;
    let eq = -1;
    while (j < lines.length) {
      if (lines[j].trimEnd() === '=======') {
        eq = j;
        break;
      }
      if (lines[j].trimEnd() === '>>>>>>> REPLACE') break;
      j++;
    }
    if (eq === -1) throw new ParseErr(searchLine + 1);
    let k = eq + 1;
    let rep = -1;
    while (k < lines.length) {
      if (lines[k].trimEnd() === '>>>>>>> REPLACE') {
        rep = k;
        break;
      }
      k++;
    }
    if (rep === -1) throw new ParseErr(searchLine + 1);
    const oldLines = lines.slice(i + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push({ kind: 's', path, oldLines, newLines });
    prevPath = path;
    prevReplace = rep;
    i = rep + 1;
  }
  return edits;
}

function applySR(e: Extract<Edit, { kind: 's' }>, tree: Tree, ctx: Ctx): ApplyResult {
  const p = e.path;
  if (!isSafe(p)) return fail('unsafe', p);
  if (e.oldLines.length === 0) {
    if (curGet(tree, p) !== null) return fail('exists', p);
    const content = e.newLines.length === 0 ? '' : e.newLines.join('\n') + '\n';
    curSet(tree, p, content);
    return { ok: true };
  }
  const cur = curGet(tree, p);
  if (cur === null) return fail('missing', p);
  const fp = parseFile(cur);
  const found = findTier(fp.lines, e.oldLines, ctx.strict);
  if (!found) return fail('no-match', p);
  if (found.occ.length > 1) return fail('ambiguous', p);
  const pos = found.occ[0];
  const nl = buildNew(e.newLines, e.newLines.map(() => -1), e.oldLines, fp.lines, pos, found.tier);
  fp.lines.splice(pos, e.oldLines.length, ...nl);
  curSet(tree, p, serFile(fp));
  return { ok: true };
}

// ---------------------------------------------------------------------------
// V4A patches (SPEC section 8)

function isV4ASectionStart(line: string): boolean {
  return (
    line.startsWith('*** Add File: ') ||
    line.startsWith('*** Delete File: ') ||
    line.startsWith('*** Update File: ')
  );
}

function parseV4A(lines: string[]): Edit[] {
  let first = -1;
  let last = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== '') {
      first = i;
      break;
    }
  }
  for (let i = lines.length - 1; i >= 0; i--) {
    if (lines[i].trim() !== '') {
      last = i;
      break;
    }
  }
  if (first === -1) throw new ParseErr(1);
  if (lines[first].trim() !== '*** Begin Patch') throw new ParseErr(first + 1);
  if (lines[last].trim() !== '*** End Patch') throw new ParseErr(lines.length + 1);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i];
    if (line.trim() === '') {
      i++;
      continue;
    }
    if (!isV4ASectionStart(line)) throw new ParseErr(i + 1);
    const kind = line.startsWith('*** Add File: ')
      ? 'add'
      : line.startsWith('*** Delete File: ')
        ? 'delete'
        : 'update';
    const prefixLen = kind === 'add' ? '*** Add File: '.length : '*** Delete File: '.length;
    const path = line.slice(prefixLen).trim();
    let end = i + 1;
    while (end < last && !isV4ASectionStart(lines[end])) end++;
    let bodyEnd = end;
    while (bodyEnd > i + 1 && lines[bodyEnd - 1].trim() === '') bodyEnd--;
    if (kind === 'add') {
      const fileLines: string[] = [];
      for (let k = i + 1; k < bodyEnd; k++) {
        const l = lines[k];
        if (l === '') fileLines.push('');
        else if (l.startsWith('+')) fileLines.push(l.slice(1));
        else throw new ParseErr(k + 1);
      }
      edits.push({ kind: 'v', sec: { kind: 'add', path, moveTo: null, lines: fileLines, chunks: [] } });
    } else if (kind === 'delete') {
      for (let k = i + 1; k < bodyEnd; k++) {
        if (lines[k].trim() !== '') throw new ParseErr(k + 1);
      }
      edits.push({ kind: 'v', sec: { kind: 'delete', path, moveTo: null, lines: [], chunks: [] } });
    } else {
      let moveTo: string | null = null;
      let idx = i + 1;
      if (idx < bodyEnd && lines[idx].startsWith('*** Move to: ')) {
        moveTo = lines[idx].slice('*** Move to: '.length).trim();
        idx++;
      }
      const chunks: VChunk[] = [];
      let curChunk: VChunk | null = null;
      let startedChunk = false;
      for (; idx < bodyEnd; idx++) {
        const l = lines[idx];
        if (l.startsWith('@@')) {
          const anchorText = l.slice(2).trim();
          curChunk = { anchor: anchorText === '' ? null : anchorText, o: [], n: [], nMap: [], eof: false };
          chunks.push(curChunk);
          startedChunk = true;
          continue;
        }
        if (l === '*** End of File') {
          if (curChunk === null) throw new ParseErr(idx + 1);
          curChunk.eof = true;
          curChunk = null;
          continue;
        }
        if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
          if (curChunk === null) {
            if (startedChunk) throw new ParseErr(idx + 1);
            curChunk = { anchor: null, o: [], n: [], nMap: [], eof: false };
            chunks.push(curChunk);
            startedChunk = true;
          }
          if (l === '') {
            curChunk.o.push('');
            curChunk.n.push('');
            curChunk.nMap.push(curChunk.o.length - 1);
          } else if (l[0] === ' ') {
            const t = l.slice(1);
            curChunk.o.push(t);
            curChunk.n.push(t);
            curChunk.nMap.push(curChunk.o.length - 1);
          } else if (l[0] === '-') {
            curChunk.o.push(l.slice(1));
          } else {
            curChunk.n.push(l.slice(1));
            curChunk.nMap.push(-1);
          }
          continue;
        }
        throw new ParseErr(idx + 1);
      }
      if (chunks.length === 0 && moveTo === null) throw new ParseErr(i + 1);
      edits.push({ kind: 'v', sec: { kind: 'update', path, moveTo, lines: [], chunks } });
    }
    i = end;
  }
  return edits;
}

function findAnchor(lines: string[], anchor: string, cursor: number, strict: boolean): number {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    for (let i = cursor; i < lines.length; i++) {
      if (normLine(lines[i], t) === normLine(anchor, t)) return i;
    }
  }
  return -1;
}

function findTierFrom(
  lines: string[],
  o: string[],
  cursor: number,
  strict: boolean,
  eof: boolean,
): { tier: number; pos: number } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const occ = occs(lines, o, t).filter((p) => p >= cursor && (!eof || p + o.length === lines.length));
    if (occ.length > 0) return { tier: t, pos: occ[0] };
  }
  return null;
}

function applyV4A(sec: VSection, tree: Tree, ctx: Ctx): ApplyResult {
  const p = sec.path;
  if (!isSafe(p)) return fail('unsafe', p);
  if (sec.moveTo !== null && !isSafe(sec.moveTo)) return fail('unsafe', sec.moveTo);
  if (sec.kind === 'add') {
    if (curGet(tree, p) !== null) return fail('exists', p);
    const content = sec.lines.length === 0 ? '' : sec.lines.join('\n') + '\n';
    curSet(tree, p, content);
    return { ok: true };
  }
  if (sec.kind === 'delete') {
    if (curGet(tree, p) === null) return fail('missing', p);
    curSet(tree, p, null);
    return { ok: true };
  }
  const cur = curGet(tree, p);
  if (cur === null) return fail('missing', p);
  if (sec.moveTo !== null && curGet(tree, sec.moveTo) !== null) return fail('exists', sec.moveTo);
  const fp = parseFile(cur);
  const lines = fp.lines.slice();
  let cursor = 0;
  for (const ch of sec.chunks) {
    if (ch.anchor !== null) {
      const idx = findAnchor(lines, ch.anchor, cursor, ctx.strict);
      if (idx === -1) return fail('no-match', p);
      cursor = idx + 1;
    }
    if (ch.o.length === 0) {
      const ins = ch.eof ? lines.length : cursor;
      const nl = buildNew(ch.n, ch.nMap, ch.o, lines, ins, 0);
      lines.splice(ins, 0, ...nl);
      cursor = ins + nl.length;
      continue;
    }
    const found = findTierFrom(lines, ch.o, cursor, ctx.strict, ch.eof);
    if (!found) return fail('no-match', p);
    const nl = buildNew(ch.n, ch.nMap, ch.o, lines, found.pos, found.tier);
    lines.splice(found.pos, ch.o.length, ...nl);
    cursor = found.pos + nl.length;
  }
  const result = serFile({ lines, eol: fp.eol, ends: fp.ends });
  if (sec.moveTo !== null) {
    curSet(tree, sec.moveTo, result);
    curSet(tree, p, null);
    ctx.moves.push({ old: p, nw: sec.moveTo });
  } else {
    curSet(tree, p, result);
  }
  return { ok: true };
}

// ---------------------------------------------------------------------------
// JSON edits (SPEC section 9)

function validateEditObject(obj: unknown, errLine: number): Edit {
  if (typeof obj !== 'object' || obj === null || Array.isArray(obj)) throw new ParseErr(errLine);
  const o = obj as Record<string, unknown>;
  if (typeof o.path !== 'string') throw new ParseErr(errLine);
  if (typeof o.command !== 'string') throw new ParseErr(errLine);
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') throw new ParseErr(errLine);
    return { kind: 'j', op: { command: 'create', path: o.path, fileText: o.file_text } };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') throw new ParseErr(errLine);
    if (o.new_str !== undefined && typeof o.new_str !== 'string') throw new ParseErr(errLine);
    return {
      kind: 'j',
      op: {
        command: 'str_replace',
        path: o.path,
        oldStr: o.old_str,
        newStr: typeof o.new_str === 'string' ? o.new_str : '',
      },
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) throw new ParseErr(errLine);
    if (typeof o.new_str !== 'string') throw new ParseErr(errLine);
    return { kind: 'j', op: { command: 'insert', path: o.path, insertLine: o.insert_line, newStr: o.new_str } };
  }
  throw new ParseErr(errLine);
}

function parseJSON(lines: string[], rawText: string): Edit[] {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== '') {
      first = i;
      break;
    }
  }
  if (first === -1) return [];
  if (lines[first].trimStart().startsWith('[')) {
    let arr: unknown;
    try {
      arr = JSON.parse(rawText);
    } catch {
      throw new ParseErr(first + 1);
    }
    if (!Array.isArray(arr)) throw new ParseErr(first + 1);
    const edits: Edit[] = [];
    for (const el of arr) edits.push(validateEditObject(el, first + 1));
    return edits;
  }
  const edits: Edit[] = [];
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    if (l.trim() === '') continue;
    let obj: unknown;
    try {
      obj = JSON.parse(l);
    } catch {
      throw new ParseErr(i + 1);
    }
    edits.push(validateEditObject(obj, i + 1));
  }
  return edits;
}

function countOccurrences(text: string, sub: string): { count: number; first: number } {
  let count = 0;
  let first = -1;
  let from = 0;
  while (true) {
    const at = text.indexOf(sub, from);
    if (at === -1) break;
    count++;
    if (first === -1) first = at;
    from = at + 1;
  }
  return { count, first };
}

function applyJSON(op: JOp, tree: Tree): ApplyResult {
  const p = op.path;
  if (!isSafe(p)) return fail('unsafe', p);
  if (op.command === 'create') {
    if (curGet(tree, p) !== null) return fail('exists', p);
    curSet(tree, p, op.fileText);
    return { ok: true };
  }
  if (op.command === 'str_replace') {
    const cur = curGet(tree, p);
    if (cur === null) return fail('missing', p);
    const fp = parseFile(cur);
    const isCRLF = fp.eol === '\r\n';
    let text = cur;
    let oldS = op.oldStr;
    let newS = op.newStr;
    if (isCRLF) {
      text = cur.replace(/\r\n/g, '\n');
      oldS = op.oldStr.replace(/\r\n/g, '\n');
      newS = op.newStr.replace(/\r\n/g, '\n');
    }
    const { count, first } = countOccurrences(text, oldS);
    if (count === 0) return fail('no-match', p);
    if (count > 1) return fail('ambiguous', p);
    let result = text.slice(0, first) + newS + text.slice(first + oldS.length);
    if (isCRLF) result = result.replace(/\n/g, '\r\n');
    curSet(tree, p, result);
    return { ok: true };
  }
  const cur = curGet(tree, p);
  if (cur === null) return fail('missing', p);
  const fp = parseFile(cur);
  if (op.insertLine < 0 || op.insertLine > fp.lines.length) return fail('no-match', p);
  const nl = splitPatch(op.newStr);
  fp.lines.splice(op.insertLine, 0, ...nl);
  curSet(tree, p, serFile(fp));
  return { ok: true };
}

// ---------------------------------------------------------------------------
// Dispatch

function applyEdit(e: Edit, tree: Tree, ctx: Ctx): ApplyResult {
  if (e.kind === 'u') return applyUnified(e.sec, tree, ctx);
  if (e.kind === 's') return applySR(e, tree, ctx);
  if (e.kind === 'v') return applyV4A(e.sec, tree, ctx);
  return applyJSON(e.op, tree);
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
