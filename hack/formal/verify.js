'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const crypto = require('node:crypto');
const { spawnSync } = require('node:child_process');
const { extractModel } = require('../load-model');
const mutations = require('./mutations');

const root = path.resolve(__dirname, '../..');
const formal = path.join(root, 'formal');
const filename = path.join(formal, 'sync-manifest.json');
const sha = data => crypto.createHash('sha256').update(data).digest('hex');
const read = file => fs.readFileSync(file, 'utf8');
function sourceFiles() {
  return ['Authz.lean', 'Main.lean', ...fs.readdirSync(path.join(formal, 'Authz'))
  .filter(name => name.endsWith('.lean')).sort().map(name => 'Authz/' + name)];
}
function sourceText() { return sourceFiles().map(name => [name, read(path.join(formal, name))]); }
const manifest = JSON.parse(read(filename));

function hashes(html) {
  const header = html.match(/<span><strong>Status:<\/strong> Canonical Technical Reference \((v[\d.]+)\)<\/span>/g);
  assert.equal(header?.length, 1, 'canonical version header');
  assert.ok(header[0].includes('(' + manifest.version + ')'), 'manifest version disagrees with HTML');
  return {
    documentSha256: sha(html), modelSha256: sha(extractModel(html)), versionHeaderSha256: sha(header[0]),
    leanSourcesSha256: sha(JSON.stringify(sourceText())),
    toolchainSha256: sha(read(path.join(formal, 'lean-toolchain')) + read(path.join(formal, 'lakefile.toml')))
  };
}
function fresh(expected, actual) {
  const changed = Object.keys(actual).filter(k => expected[k] !== actual[k]);
  if (changed.length) throw new Error(`STALE FORMAL MANIFEST: ${changed.join(', ')}. Review the spec and proofs, then run gmake record-formal.`);
}
function command(binary, args, opts = {}) {
  const result = spawnSync(binary, args, { cwd: root, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
    stdio: opts.input == null ? 'inherit' : 'pipe', ...opts });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, (result.stdout || '') + (result.stderr || '') + '\n' + binary + ' ' + args.join(' '));
  return result.stdout;
}

// Skip nested comments, strings and complete character literals. Apostrophes also occur in identifiers.
function codeOnly(text) {
  const character = /'(?:\\(?:u\{[0-9a-fA-F]+\}|u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|[^\r\n])|[^'\\\r\n])'/uy;
  let result = '', depth = 0, string = false, line = false;
  for (let i = 0; i < text.length; i++) {
    const c = text[i], pair = text.slice(i, i + 2);
    if (line) { if (c === '\n') { line = false; result += '\n'; } continue; }
    if (string) { if (c === '\\') i++; else if (c === '"') string = false; continue; }
    if (pair === '/-') { depth++; i++; result += ' '; continue; }
    if (depth) { if (pair === '-/') { depth--; i++; } else if (c === '\n') result += '\n'; continue; }
    if (pair === '--') { line = true; i++; continue; }
    if (c === '"') { string = true; result += ' '; continue; }
    if (c === "'") {
      character.lastIndex = i;
      if (character.test(text)) { i = character.lastIndex - 1; result += ' '; continue; }
    }
    result += c;
  }
  return result;
}
function audit(html) {
  assert.match(codeOnly(`def quote := '"'\nprivate theorem check' : True := by sorry`), /\bsorry\b/);
  assert.doesNotMatch(codeOnly(`/- outer /- sorry -/ inner -/ def word := "admit" -- axiom\n`), /\b(sorry|admit|axiom)\b/);
  const interpretation = html.split('id="p4-interpretation"')[1].split('id="p4-methods"')[0];
  assert.match(interpretation, /<tr>[^\n]*companies\/\{company\}\/settings[^\n]*companies\/\{parent\}\/settings\/\{setting\}[^\n]*<\/tr>/,
    'the singleton and collection collision belongs in the §4.2 rejection table');
  const rejections = interpretation.split('<caption>What the build rejects</caption>')[1].split('</table>')[0];
  assert.ok(rejections.split('</tr>').some(row => ['BatchUpdate', 'update_mask', 'allow_missing', 'child'].every(word => row.includes(word))),
    'the core build-rejection table must cover BatchUpdate fields missing from the child request');
  const ids = [...html.matchAll(/<h3 id="(p\d+-[^"]+)">/g)].map(m => m[1]).sort();
  assert.deepEqual([...Object.keys(manifest.sections), ...Object.keys(manifest.outsideSemanticCore)].sort(), ids);
  assert.deepEqual(Object.keys(manifest.theorems), ['T1','T2','T3','T4','T5','T6']);
  const proofs = new Set(Object.values(manifest.theorems).flat());
  for (const [name, source] of sourceText()) {
    const code = codeOnly(source);
    assert.doesNotMatch(code, /\b(sorry|admit|axiom|native_decide|unsafe|partial|implemented_by|extern|csimp|opaque)\b/, name);
  }
  const declarations = new Set([...Object.values(manifest.sections).flat(), ...proofs]);
  const modules = sourceFiles().map(name => name.slice(0, -'.lean'.length).replaceAll('/', '.'));
  for (const mod of modules) assert.match(mod, /^(?:Main|Authz(?:\.[A-Za-z_]\w*)*)$/);
  const commands = ['import Lean', ...modules.map(mod => 'import ' + mod), 'set_option format.width 10000'];
  for (const decl of declarations) {
    assert.match(decl, /^Authz(?:\.[a-zA-Z_]\w*)+$/);
    commands.push('#check ' + decl);
  }
  // Read the compiled environment. This includes private declarations and generated theorems.
  commands.push(
    'open Lean Elab Command in',
    'run_cmd do',
    '  let env ← getEnv',
    '  let mut names := #[]',
    '  for (name, info) in env.constants.toList do',
    '    let some idx := env.getModuleIdxFor? name | continue',
    '    let mod := env.header.moduleNames[idx.toNat]!',
    '    if ((`Authz).isPrefixOf mod || mod == `Main) && (info matches .thmInfo _) then',
    '      names := names.push name',
    '  logInfo m!"Kernel theorem count {names.size}"',
    '  for name in names do elabCommand (← `(#print axioms $(mkCIdent name)))'
  );
  const result = command('lake', ['env', 'lean', '--stdin'], { cwd: formal, input: commands.join('\n') });
  const standard = new Set(['propext','Classical.choice','Quot.sound']);
  const seen = new Set(), used = new Set();
  for (const match of result.matchAll(/^'(.+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])/gm)) {
    seen.add(match[1]);
    for (const axiom of (match[2] || '').split(',').map(x => x.trim()).filter(Boolean)) {
      assert.ok(standard.has(axiom), `${match[1]} depends on ${axiom}`);
      used.add(axiom);
    }
  }
  const count = result.match(/^Kernel theorem count (\d+)$/m);
  assert.ok(count && seen.size === Number(count[1]), 'missing kernel audit results');
  for (const name of proofs) assert.ok(seen.has(name), 'missing manifest theorem ' + name);
  console.log(`Audited ${seen.size} compiled Lean theorems, including private and generated declarations. Axioms: ${[...used].sort().join(', ')}.`);
}
function main() {
  const args = process.argv.slice(2);
  const record = args[0] === '--record';
  const probe = args[0] === '--check-source';
  if (args.length && !(record && args.length === 1) && !(probe && args.length === 2)) throw new Error('Unexpected verification arguments');
  const html = read(probe ? args[1] : path.join(root, 'index.html'));
  const current = hashes(html);
  if (!record) fresh(manifest.hashes, current);
  if (probe) return;
  command('lake', ['--wfail', 'build'], { cwd: formal });
  audit(html);
  command(process.execPath, ['hack/run-checks.js']);
  command(process.execPath, ['hack/formal/verify-cases.js']);
  mutations.run();
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'authz-drift-'));
  try {
    const drift = path.join(temp, 'index.html');
    const injected = html.replace('window.AuthzModel = api', '/* deliberate model drift */ window.AuthzModel = api');
    assert.notEqual(injected, html);
    assert.notEqual(hashes(injected).modelSha256, current.modelSha256);
    fs.writeFileSync(drift, injected);
    // Exercise the same preflight used by the verification command before any model execution.
    const r = spawnSync(process.execPath, [__filename, '--check-source', drift], { encoding: 'utf8' });
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /STALE FORMAL MANIFEST: [^\n]*modelSha256/);
    console.log('Rejected deliberate drift in the embedded reference model.');
  } finally {
    fs.rmSync(temp, { recursive: true, force: true });
  }
  const end = hashes(read(path.join(root, 'index.html')));
  assert.deepEqual(end, current, 'Specification changed during verification');
  if (record) {
    const tmp = filename + '.' + process.pid + '.tmp';
    try {
      fs.writeFileSync(tmp, JSON.stringify({ ...manifest, hashes: current }, null, 2) + '\n', { flag: 'wx' });
      fs.renameSync(tmp, filename);
    } finally { fs.rmSync(tmp, { force: true }); }
  }
}
if (require.main === module) main();
