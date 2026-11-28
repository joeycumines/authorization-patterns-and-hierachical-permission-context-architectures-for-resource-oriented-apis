// Run against the repository's HTML, or pass a local path or URL to another copy.
const assert = require('node:assert/strict');
const path = require('node:path');
const { execFileSync } = require('node:child_process');
const { readFile } = require('node:fs/promises');
const { pathToFileURL } = require('node:url');
const { chromium } = require(process.env.PW || 'playwright');

function specURL(input) {
  if (/^(?:https?|file):/i.test(input)) return new URL(input);
  return pathToFileURL(path.resolve(input));
}

const documents = [
  ['overview', '01-overview-and-model.md'],
  ['architecture', '02-architecture-and-semantics.md'],
  ['contracts', '03-contracts-and-enforcement.md'],
  ['algorithms', '04-algorithms-and-checks.md'],
  ['history', '05-version-history.md'],
  ['all', 'authorization-architecture-reference.md']
];

const sections = {
  overview: ['exec-summary', 'part-1', 'part-2', 'part-5'],
  architecture: ['part-3'],
  contracts: ['part-4'],
  algorithms: ['part-4'],
  history: ['version-history']
};

const numberedHeadings = {
  overview: ['1.1', '1.2', '1.3', '1.4', '2.1', '2.2', '5.1', '5.2'],
  architecture: ['3.1', '3.2', '3.3', '3.4', '3.5', '3.6', '3.7', '3.8', '3.9'],
  contracts: ['4.1', '4.2', '4.3', '4.5'],
  algorithms: ['4.4', '4.6'],
  history: []
};

function markdownURL(base, id, { hash = false, raw = false } = {}) {
  const url = new URL(base);
  const params = new URLSearchParams({ format: 'md' });
  if (id) params.set('doc', id);
  if (raw) params.set('raw', '1');
  if (hash) url.hash = params.toString();
  else for (const [key, value] of params) url.searchParams.set(key, value);
  return url.href;
}

function currentSelector(page, key) {
  const url = new URL(page.url());
  return url.searchParams.get(key) ?? new URLSearchParams(url.hash.slice(1)).get(key);
}

async function download(page, button, filename) {
  const [file] = await Promise.all([page.waitForEvent('download'), page.locator(button).click()]);
  assert.equal(file.suggestedFilename(), filename);
  assert.equal(await file.failure(), null, 'Download failed for ' + filename);
  return file.path();
}

async function checkBundle(page, button, text) {
  const archive = await download(page, button, 'authorization-reference-markdown.tar');
  const members = execFileSync('tar', ['-tf', archive], { encoding: 'utf8' }).trimEnd().split('\n');
  const normative = documents.slice(0, 4);
  assert.deepEqual([...members].sort(), normative.map(([, name]) => name).sort());
  for (const [id, name] of normative) {
    const expected = await page.evaluate(id => window.AuthzMarkdown.serialize(id), id);
    assert.ok(expected === text[id], 'Article and download page disagree on ' + name);
    const actual = execFileSync('tar', ['-xOf', archive, name], { maxBuffer: 16 * 1024 * 1024 });
    assert.ok(actual.equals(Buffer.from(expected)), 'Archive member differs from serializer output for ' + id);
  }
}

async function checkSingle(page, button, id, text) {
  const name = documents.find(([key]) => key === id)[1];
  const file = await download(page, button, name);
  assert.ok((await readFile(file)).equals(Buffer.from(text[id])), 'Downloaded bytes differ for ' + name);
}

async function checkCopy(page, button, expected) {
  await page.bringToFront();
  await page.locator(button).click();
  await page.waitForFunction(async expected => (await navigator.clipboard.readText()) === expected, expected);
}

async function checkSelectors(page, selector, selected) {
  assert.deepEqual(await page.locator(selector + ' option').evaluateAll(opts => opts.map(o => o.value)),
    documents.map(([id]) => id));
  assert.equal(await page.locator(selector).inputValue(), selected);
}

async function checkView(page, expected, raw = false) {
  await page.waitForFunction(expected => document.getElementById('md-permalink-pre')?.textContent === expected, expected);
  if (raw) {
    assert.equal(await page.locator('body > :not(pre)').count(), 0, 'Raw mode should contain only the Markdown');
  }
}

async function checkDocuments(page, url) {
  const snap = await page.evaluate(() => {
    const article = document.getElementById('article-content');
    const md = window.AuthzMarkdown;
    const tableData = Array.from(article.querySelectorAll('table'), table => {
      const section = table.closest('section');
      const sub = Array.from(section.querySelectorAll('h3[id]'))
        .filter(h => h.compareDocumentPosition(table) & Node.DOCUMENT_POSITION_FOLLOWING).at(-1);
      return {
        section: section.id, number: sub?.textContent.match(/^\d+\.\d+/)?.[0],
        header: Array.from(table.rows[0].cells, c => c.textContent.trim().replace(/\s+/g, ' ')),
        rows: table.rows.length
      };
    });
    return {
      manifest: md.documents.map(({id, filename, normative}) => [id, filename, normative]),
      text: Object.fromEntries(md.documents.map(({id}) => [id, md.serialize(id)])),
      title: article.querySelector('h1').textContent.trim(),
      parts: Array.from(article.querySelectorAll(':scope > section'), section => [section.id,
        section.querySelector('h2').textContent.trim()]),
      subsections: Array.from(article.querySelectorAll(':scope > section > h3[id]'), h => h.textContent.trim()),
      proofs: Array.from(article.querySelectorAll('details.proof'), d => d.querySelector('summary').textContent),
      versionHeadings: Array.from(article.querySelectorAll('#version-history > h3'), h => h.textContent.trim()),
      citations: Array.from(article.querySelectorAll('#bib-list > li'), li => li.querySelector('a[href]')?.href),
      tables: tableData,
      checks: document.getElementById('results').textContent.trim().split('\n')
    };
  });
  assert.deepEqual(snap.manifest, documents.map(([id, name], i) => [id, name, i < 4]));
  assert.deepEqual(snap.proofs, ['Proof of Theorem 1.1', 'Proof of Proposition 3.1']);
  assert.ok(snap.versionHeadings.length > 0 && snap.citations.length > 0);
  const text = snap.text;
  const plain = value => value.replace(/\[([^\]]+)\]\([^)]+\)/g, '$1').replace(/[`*]/g, '');
  const originalHeadings = snap.subsections.map(h => h.match(/^\d+\.\d+/)[0]);
  assert.deepEqual([...originalHeadings].sort(), Object.values(numberedHeadings).flat().sort());

  for (const [id] of documents) {
    const all = id === 'all';
    const lines = text[id].split('\n');
    assert.ok(lines.includes('# ' + snap.title), id + ' lacks the canonical title');
    const parts = snap.parts.filter(([key]) => all || sections[id].includes(key)).map(([, h]) => h);
    assert.deepEqual(lines.filter(l => l.startsWith('## ')).map(l => plain(l.slice(3))), parts, id + ' parts');
    const headings = snap.subsections.filter(h => all || numberedHeadings[id].includes(h.match(/^\d+\.\d+/)[0]));
    assert.deepEqual(lines.filter(l => /^### \d+\.\d+\b/.test(l)).map(l => plain(l.slice(4))), headings, id + ' sections');
    assert.deepEqual(lines.filter(l => /^### v\d/.test(l)).map(l => plain(l.slice(4))),
      all || id === 'history' ? snap.versionHeadings : [], id + ' version history headings');
    if (all || id === 'overview') {
      for (const href of snap.citations) assert.ok(text[id].includes(href), id + ' bibliography entry ' + href);
    }
    const proofText = ['A permit applies at every descendant of its scope', 'A grant whose scope is not an ancestor of'];
    for (const [i, proof] of snap.proofs.entries()) {
      const belongs = all || id === ['overview', 'architecture'][i];
      assert.equal(lines.includes('#### ' + proof), belongs, id + ' ' + proof);
      assert.equal(text[id].includes(proofText[i]), belongs, id + ' text of ' + proof);
    }
    const tables = snap.tables.filter(t => all || (t.section === 'part-4'
      ? numberedHeadings[id].includes(t.number) : sections[id].includes(t.section)));
    const headers = lines.flatMap((line, i) => /^\| (?:--- \| ?)+$/.test(line) ? [i - 1] : []);
    assert.equal(headers.length, tables.length, id + ' table count');
    for (const [i, h] of headers.entries()) {
      const cells = plain(lines[h]).slice(1, -1).split('|').map(s => s.trim());
      assert.deepEqual(cells, tables[i].header, id + ' table headers');
      let end = h + 2;
      while (end < lines.length && lines[end].startsWith('|')) ++end;
      assert.equal(end - h - 1, tables[i].rows, id + ' table row count');
    }
    assert.deepEqual(lines.filter(l => l.startsWith('PASS  ')),
      all || id === 'algorithms' ? snap.checks : [], id + ' regression results');
  }

  const context = page.context();
  const [mdPage] = await Promise.all([context.waitForEvent('page'), page.click('#btn-markdown')]);
  await checkView(mdPage, text.overview);
  await checkSelectors(mdPage, '#md-doc', 'overview');
  for (const [id] of documents) {
    await mdPage.selectOption('#md-doc', id);
    await checkView(mdPage, text[id]);
    assert.equal(currentSelector(mdPage, 'doc'), id);
  }
  await mdPage.goto(markdownURL(url));
  await checkView(mdPage, text.all);
  await checkSelectors(mdPage, '#md-doc', 'all');
  await mdPage.selectOption('#md-doc', 'architecture');
  await mdPage.waitForURL(candidate => candidate.searchParams.get('doc') === 'architecture');
  await checkView(mdPage, text.architecture);
  await mdPage.reload();
  await checkView(mdPage, text.architecture);
  assert.equal(await mdPage.locator('#md-doc').inputValue(), 'architecture');
  await checkCopy(mdPage, '#btn-md-copy', text.architecture);
  await checkSingle(mdPage, '#btn-md-dl', 'architecture', text);
  await checkBundle(mdPage, '#btn-md-bundle', text);
  await mdPage.click('#btn-md-raw');
  await checkView(mdPage, text.architecture, true);
  assert.equal(currentSelector(mdPage, 'raw'), '1');
  assert.equal(currentSelector(mdPage, 'doc'), 'architecture');
  await mdPage.reload();
  await checkView(mdPage, text.architecture, true);
  await mdPage.goBack();
  await checkView(mdPage, text.architecture);
  await mdPage.click('#btn-md-html');
  await mdPage.locator('#article-content').waitFor();
  for (const key of ['doc', 'format', 'raw']) assert.equal(currentSelector(mdPage, key), null);

  for (const hash of [false, true]) {
    for (const [id] of documents) {
      await mdPage.goto(markdownURL(url, id, { hash }));
      await checkView(mdPage, text[id]);
      assert.equal(await mdPage.locator('#md-doc').inputValue(), id);
    }
    await mdPage.goto(markdownURL(url, 'contracts', { hash, raw: true }));
    await checkView(mdPage, text.contracts, true);
  }
  await mdPage.goto(markdownURL(url, 'overview', { hash: true }));
  await mdPage.selectOption('#md-doc', 'algorithms');
  await checkView(mdPage, text.algorithms);
  assert.equal(new URLSearchParams(new URL(mdPage.url()).hash.slice(1)).get('doc'), 'algorithms');
  await mdPage.reload();
  await checkView(mdPage, text.algorithms);
  await mdPage.click('#btn-md-html');
  await mdPage.locator('#article-content').waitFor();
  assert.equal(currentSelector(mdPage, 'format'), null);
  await mdPage.close();

  // Exercise the browser's popup-blocked fallback through the article button.
  await page.evaluate(() => { window.open = () => null; });
  await page.click('#btn-markdown');
  await page.locator('#md-modal').waitFor();
  await checkSelectors(page, '#md-modal-doc', 'overview');
  await page.selectOption('#md-modal-doc', 'history');
  assert.ok((await page.locator('#md-modal-pre').textContent()) === text.history);
  await checkCopy(page, '#md-modal-copy', text.history);
  await checkSingle(page, '#md-modal-download', 'history', text);
  await checkBundle(page, '#md-modal-bundle', text);
  await page.click('#md-modal-close');
  assert.equal(await page.locator('#md-modal').isVisible(), false);
  return { length: text.all.length, passLines: text.all.split('\n').filter(l => l.startsWith('PASS  ')).length, documents: documents.map(([id]) => id),
    tables: snap.tables.length, proofs: snap.proofs.length, bundles: 2 };
}

async function check(browser, url) {
  const page = await browser.newPage({ viewport: { width: 1300, height: 1000 },
    permissions: ['clipboard-read', 'clipboard-write'] });
  const errors = [];
  function collectErrors(p) {
    p.on('pageerror', (err) => errors.push(err.message));
    p.on('console', (msg) => {
      if (msg.type() === 'error' && !/favicon/.test(msg.text())) errors.push(msg.text());
    });
  }
  collectErrors(page);
  page.context().on('page', collectErrors);
  await page.goto(url.href);
  await page.waitForFunction(() => document.getElementById('results')?.textContent.trim());
  const results = await page.locator('#results').evaluate((el) => {
    const lines = el.textContent.trim().split('\n');
    return { total: lines.length, fails: lines.filter((line) => !line.startsWith('PASS  ')) };
  });

  assert.equal(await page.locator('#sim-rpc').inputValue(), 'get_team_b');
  assert.match(await page.locator('#sim-out-client').textContent(), /^Client result: ALLOW$/m);
  assert.match(await page.locator('#sim-out-pep').textContent(), /^Authoritative result: ALLOW$/m);
  const initialTeam = (await page.locator('#sim-out-server').textContent()).split('\n\n')
    .find(ctx => ctx.startsWith('Anchor companies/A/teams/B '));
  assert.match(initialTeam, /ALLOW\s+at companies\/A\/teams\/B\n\s+keys: [^\n]*\bteams\.get\b/);

  const ops = await page.locator('#sim-rpc option').evaluateAll((options) => options.map((o) => o.value));
  assert.ok(ops.length, 'No simulator operations');
  const sim = [];
  for (const op of ops) {
    await page.selectOption('#sim-rpc', op);
    const client = await page.locator('#sim-out-client').textContent();
    const server = await page.locator('#sim-out-pep').textContent();
    const clientResult = client.match(/^Client result: (\w+)/m)?.[1];
    const serverResult = server.match(/^Authoritative result: (\w+)/m)?.[1];
    assert.ok(clientResult && serverResult, 'Missing simulator verdict for ' + op);
    assert.equal(await page.locator('#sim-alert .callout-danger').count(), 0,
      op + ': simulator flagged verdicts ' + clientResult + '/' + serverResult);
    sim.push(op + ' -> ' + client.trim().split('\n').pop() + ' | ' + server.trim().split('\n').pop());
  }

  // Isolate Team D's private rule so an otherwise universal List has exactly one reason to refuse.
  await page.uncheck('#pol-teamc-forbid');
  await page.selectOption('#sim-rpc', 'list_wildcard');
  for (const profile of ['grants', 'claims']) {
    await page.selectOption('#sim-mode', profile);
    for (const enabled of [false, true]) {
      await page.locator('#pol-private-d').setChecked(enabled);
      const client = (await page.locator('#sim-out-client').textContent()).split('\n').pop();
      const server = (await page.locator('#sim-out-pep').textContent()).split('\n').pop();
      const company = (await page.locator('#sim-out-server').textContent()).split('\n\n')
        .find(ctx => ctx.startsWith('Anchor companies/A '));
      assert.equal(client, 'Client result: ' + (enabled ? 'UNLOADED' : 'ALLOW'));
      assert.equal(server, 'Authoritative result: ' + (enabled ? 'DENY' : 'ALLOW'));
      if (enabled) assert.match(company, /no claim for widgets\.list/);
      else assert.match(company, /ALLOW\s+at companies\/A\n\s+keys: [^\n]*\bwidgets\.list\b/);
      sim.push(profile + ' private=' + enabled + ' -> ' + client + ' | ' + server);
    }
  }

  await page.fill('#toc-search', 'requested_anchors');
  const search = await page.locator('.toc-item:not(.toc-hidden)').allTextContents();
  assert.ok(search.some((name) => name.includes('4.1')), 'Search missed the permission context contract');
  await page.fill('#toc-search', '');
  await page.click('.cite');
  const popOpen = await page.locator('#cite-popover').evaluate((el) => el.style.display);
  await page.keyboard.press('Escape');
  const popAfter = await page.evaluate(() => ({
    display: document.getElementById('cite-popover').style.display,
    focusIsCite: document.activeElement.classList.contains('cite')
  }));
  const toggle = page.locator('#btn-toggle-sidebar');
  const ariaBefore = await toggle.getAttribute('aria-expanded');
  await toggle.click();
  const ariaAfter = await toggle.getAttribute('aria-expanded');
  assert.equal(popOpen, 'block');
  assert.deepEqual(popAfter, { display: 'none', focusIsCite: true });
  assert.deepEqual([ariaBefore, ariaAfter], ['true', 'false']);

  const scope = await page.locator('#exec-summary > p').filter({ hasText: 'how the server decides a request' }).textContent();
  const md = await checkDocuments(page, url);
  assert.ok(await page.evaluate(phrase => window.AuthzMarkdown.serialize('all').includes(phrase), scope.trim()),
    'Combined Markdown export is missing executive summary text');
  console.log(JSON.stringify({ errors, results, sim, search, popOpen, popAfter, aria: [ariaBefore, ariaAfter], md }, null, 1));
  assert.deepEqual(errors, [], 'Browser errors');
  assert.deepEqual(results.fails, [], 'Model checks failed in the browser');
  assert.equal(md.passLines, results.total, 'Exported model check count');
  await page.close();
}

async function main() {
  const url = specURL(process.argv[2] || path.join(__dirname, '..', 'index.html'));
  const browser = await chromium.launch({ channel: 'chrome', headless: true });
  try {
    await check(browser, url);
  } finally {
    await browser.close();
  }
}

main().catch((err) => { console.error(err); process.exitCode = 1; });
