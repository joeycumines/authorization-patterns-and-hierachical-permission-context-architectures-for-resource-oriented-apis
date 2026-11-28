// Runs the reference model's regression checks (§4.6) headless, straight from index.html.
// Usage: node hack/run-checks.js [index.html] [--all]
const file = process.argv.slice(2).find((a) => !a.startsWith('--'));
const api = require('./load-model.js')(file);
const lines = api.run();
if (!lines.length) throw new Error('The reference model returned no regression checks');
const fails = lines.filter((line) => !line.startsWith('PASS  '));
for (const line of process.argv.includes('--all') ? lines : fails) console.log(line);
console.log(`TOTAL ${lines.length}  PASS ${lines.length - fails.length}  FAIL ${fails.length}`);
process.exitCode = fails.length ? 1 : 0;
