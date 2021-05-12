# Wumpus World in Jess
Assignment for the Artificial Intelligence Course at FH Hagenberg Summer Term 2021

## Running
1. Extract **Jess71p2.zip**.
2. Add its `bin`-Folder to your path.
3. Now execute the following commands **in the root of this repository**:

```powershell
jess
(batch jess/cave<ID>.clp) # 1. execute this in the JESS REPL
                          # 2. replace ID with the appropriate cave
(exit) # optional: exit the JESS REPL
```

## Questions
- `.jess`-Files do not exist, where are they?
- e.g. `cave0.clp` loads `(batch jess\\ww.clp)` but crashes because of the paths, is this intended?
- [JESS Documentation](https://jess.sandia.gov/jess/docs/71/) is offline :(
  - Alternative exists at the Wayback-Machine [here](https://web.archive.org/web/20200814203325/https://jess.sandia.gov/jess/docs/71/)
