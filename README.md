# Processing a `-ddump-splices`

run `./process-file path/to/output/of/ddump-splices/name.Type`
where `name` is whatever you want and `Type` is the name of 
a file containing definitions for creating the repro.
There must be a file named `Type` in the root of the repository.

# Reproducibles in this repository

## Processed/Minimal1

Just like the first one we sent, (doesn't typecheck with 5Gb ram)

## Processed/Minimal2

Added pattern synonyms for indexes into the lists. (takes about 4.5 Gbs)

```haskell
type D0_ = Z
type D1_ = S Z
type D2_ = S (S Z)
...

pattern IdxA = SZ
pattern IdxB = SS SZ
...
```

## Processed/Minimal31

Added `Here / There` pattern synonyms (consumes about 2.5 Gb)

```haskell
pattern PatAA x = Here x
pattern PatAB x = There (Here x)
...
```

## Processed/Minimal32

Just like `Minimal31`, but on a larger datatype. This one
does not compile for unknown reasons.

## Processed/Minimal4

Added type signatures to the `Here / There` patterns.
Typechecks with about 2.5Gb of ram on this example. 
Larger examples explode much faster than without the `Here / There` patterns.
