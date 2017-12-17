# Claire

A simple proof assistant based on LK

## Build

- stack
- ghc >= 8

```
$ git clone https://github.com/myuon/claire
$ cd claire
$ stack build
```

## Run proofchecker

```
$ stack exec claire lib/hol.cl
= Constants =
("all",ArrT (ArrT (VarT "'a") (ConT "bool" [])) (ConT "bool" []))
...
= Proved Theorems =
("Curry",(Pred "?P" [] :==>: (Pred "?Q" [] :==>: Pred "?R" [])) :==>: ((Pred "?P" [] :/\: Pred "?Q" []) :==>: Pred "?R" []))
...
```

## Run interactive shell

```
$ stack exec claire
=========================
=== Welcome to Claire ===
=========================
```

### Try proving!

```
=========================
=== Welcome to Claire ===
=========================

decl>theorem id: a ==> a

[] |- [Pred "a" [] :==>: Pred "a" []]
command>apply ImpR

[Pred "a" []] |- [Pred "a" []]
command>apply I

decl>print_proof
= proof of the previous theorem =
proof
  apply ImpR
  apply I
qed
```

See [Parser.y](src/Claire/Parser/Parser.y) for complete syntax.

