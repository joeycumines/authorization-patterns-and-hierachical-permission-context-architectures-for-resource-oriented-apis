// Execute the same trusted, standalone script that the browser runs in index.html.
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

function extractModel(html) {
  const scripts = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)]
    .map(match => match[1])
    .filter(script => script.includes('window.AuthzModel = api'));
  if (scripts.length !== 1) throw new Error(`Expected one embedded AuthzModel, found ${scripts.length}`);
  return scripts[0];
}

function loadModel(file = path.join(__dirname, '..', 'index.html')) {
  const script = extractModel(fs.readFileSync(file, 'utf8'));
  const context = { module: { exports: {} }, console };
  vm.runInNewContext(script, context, { filename: file });
  return context.module.exports;
}

module.exports = loadModel;
module.exports.extractModel = extractModel;
