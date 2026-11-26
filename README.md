The encoding description is in [encoding.pdf](encoding.pdf) (or it's source in [encoding.md](encoding.md)).

## CLI usage
```
USAGE: NxNQueen [COMMAND]

COMMANDS:
    encode <n> <k>  ... generates a DIMANCS CNF encoding for the specified n,k values, outputs into stdout
    solve  <n>   ... finds the maximal k which is SAT for an nxn board
```
For example `cabal run exes -- solve 7` outputs:
```
trying k=1
trying k=2
trying k=3
trying k=4
trying k=5
trying k=6
trying k=7
trying k=8
The maximal k for n=7 is: 7

Example solution:
.ww....
..ww...
.....bb
w......
ww.....
....bb.
....bbb
```

## Limatation
The encoding isn't very efficient for the UNSAT case so for large n (>9) glucose will get stuck on the first k which is UNSAT
