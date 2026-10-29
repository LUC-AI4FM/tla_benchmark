```tla
ars

SeekCorrect ==
    [][\A p \in Offset : Seek(p) => RAF_Seek(p)]_vars

SeekEstablishesInv2 ==
    [][\A p \in Offset : Seek(p) => Inv2']_vars

Write1Correct ==
    [][\A d \in Symbols : Write1(d) => RAF_Write(<<d>>)]_vars

Read1Correct ==
    [][Read1 => RAF_Read(1)]_vars

WriteAtMostCorrect ==
    [][\A data \in NonEmptyDataArrays :
          WriteAtMost(data) =>
              \E k \in 1..Len(data) : RAF_Write(SubSeq(data, 1, k))]_vars

ReadCorrect ==
    [][\A n \in 1..MaxOffset : Read(n) => RAF_Read(n)]_vars

(***************************************************************************
TLC configuration:

CONSTANTS
    Symbols = {a, b}
    ArbitrarySymbol = ArbitrarySymbol
    MaxOffset = 3
    BuffSz = 2

SPECIFICATION Spec
SYMMETRY Symmetry
ALIAS Alias

INVARIANTS
    TypeOK
    Inv1
    Inv2CanAlwaysBeRestored
    Inv3
    Inv4
    Inv5

PROPERTIES
    Safety
    FlushBufferCorrect
    SeekCorrect
    SeekEstablishesInv2
    Write1Correct
    Read1Correct
    WriteAtMostCorrect
    ReadCorrect
***************************************************************************)

=============================================================================
```