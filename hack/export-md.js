'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const { pathToFileURL } = require('node:url');
const { chromium } = require(process.env.PW || 'playwright');

async function exportMarkdown() {
  const root = path.resolve(__dirname, '..');
  const destination = path.join(root, 'build', 'md');
  const browser = await chromium.launch({ channel: 'chrome', headless: true });
  let documents;
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    page.on('console', message => {
      if (message.type() === 'error') errors.push(message.text());
    });
    await page.goto(pathToFileURL(path.join(root, 'index.html')).href);
    documents = await page.evaluate(() => {
      const { documents, serialize } = window.AuthzMarkdown;
      return documents.map(({ id, filename }) => ({ id, filename, markdown: serialize(id) }));
    });
    assert.deepEqual(errors, [], 'Browser errors while exporting the specification');
  } finally {
    await browser.close();
  }

  assert.ok(documents.length, 'No Markdown documents were declared');
  const filenames = new Set();
  for (const { id, filename, markdown } of documents) {
    assert.match(filename, /^[a-z0-9][a-z0-9-]*\.md$/);
    assert.ok(!filenames.has(filename), 'Duplicate Markdown filename ' + filename);
    filenames.add(filename);
    assert.ok(markdown.trim().length, 'Empty Markdown for ' + id);
  }
  await fs.mkdir(destination, { recursive: true });
  const stage = await fs.mkdtemp(path.join(destination, '.export-'));
  try {
    for (const { filename, markdown } of documents) {
      await fs.writeFile(path.join(stage, filename), markdown, 'utf8');
    }
    for (const { filename, markdown } of documents) {
      await fs.rename(path.join(stage, filename), path.join(destination, filename));
      console.log('build/md/' + filename + ' (' + markdown.trim().split(/\s+/u).length + ' words)');
    }
  } finally {
    await fs.rm(stage, { recursive: true, force: true });
  }
}

exportMarkdown().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
