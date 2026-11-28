import Authz.Oracle

open Lean

/-- Each line is an independent JSON request. Every input receives exactly one
response. A malformed request reports an error without losing later records. -/
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := match (Json.parse line).bind Authz.Oracle.handle with
      | .ok value => Json.mkObj [("ok", value)]
      | .error err => Json.mkObj [("error", toJson err)]
    output.putStrLn result.compress
    output.flush
