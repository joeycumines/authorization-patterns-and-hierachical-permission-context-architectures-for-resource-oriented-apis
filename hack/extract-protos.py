"""Extract the published protobuf blocks in sections 4.1 and 4.5."""

import html
from pathlib import Path
import re
import sys

source, output, *expected = sys.argv[1:]
blocks = re.findall(
    r'<span>(authz/v1/[a-z_]+\.proto)[^<]*</span>.*?</div>\s*<pre><code>(.*?)</code></pre>',
    Path(source).read_text(encoding='utf-8'),
    re.DOTALL,
)
names = [name for name, _ in blocks]
if not names or len(names) != len(set(names)) or (expected and set(names) != set(expected)):
    sys.exit(f'Unexpected protobuf blocks in {source}: {names!r} (expected {expected!r})')

for name, markup in blocks:
    body = html.unescape(re.sub(r'<[^>]+>', '', markup))
    path = Path(output) / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body if body.endswith('\n') else body + '\n', encoding='utf-8')
