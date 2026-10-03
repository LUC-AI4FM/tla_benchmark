----------------------------- MODULE BufferedRandomAccessFile -----------------------------

EXTENDS Naturals, Sequences

(*
  Constants:
    Symbols          - finite nonempty set of symbol values (e.g., bytes)
    ArbitrarySymbol  - a distinguished value in Symbols used to represent "unknown"
    MaxOffset        - maximum addressable offset; the file address range is 0..MaxOffset-1
    BuffSz           - size (capacity) of the in-memory buffer (in symbols)
*)
CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

ASSUME /\ ArbitrarySymbol \in Symbols
       /\ MaxOffset \in Nat /\ MaxOffset > 0
       /\ BuffSz \in Nat /\ BuffSz > 0 /\ BuffSz <= MaxOffset

(*
  Indices and helper sets.
*)
Offsets == 0 .. (MaxOffset - 1)
BufIdx  == 0 .. (BuffSz - 1)

(*
  State variables.
    disk      : on-disk contents (total map Offsets -> Symbols)
    len       : logical file length (0..MaxOffset)
    pos       : file pointer (0..len)
    bufBase   : base file offset of buffer slot 0
    buf       : in-memory buffer values (total map BufIdx -> Symbols)
    bufValid  : subset of indices in BufIdx that currently hold meaningful bytes
    bufDirty  : subset of bufValid whose values differ from disk and must be flushed
    lastRead  : last value returned by a read operation (in Symbols)
*)
VARIABLES disk, len, pos, bufBase, buf, bufValid, bufDirty, lastRead

vars == << disk, len, pos, bufBase, buf, bufValid, bufDirty, lastRead >>

(*
  Window coverage predicate and overlay function used for refinement relations.
*)
BufCoversPos ==
  \/ pos = MaxOffset
  \/ /\ pos >= bufBase
     /\ pos < bufBase + BuffSz

OverlayDisk(d, bBase, b, dset) ==
  [ x \in Offsets |->
      IF /\ x >= bBase
         /\ x < bBase + BuffSz
         /\ (x - bBase) \in dset
      THEN b[x - bBase] ELSE d[x]
  ]

(*
  Abstract logical view of the file as perceived by reads (disk overlaid with dirty buffer).
*)
AbsFile ==
  [ x \in Offsets |->
      IF /\ x >= bufBase
         /\ x < bufBase + BuffSz
         /\ (x - bufBase) \in bufDirty
         /\ (x - bufBase) \in bufValid
      THEN buf[x - bufBase] ELSE disk[x]
  ]

(*
  Types and basic well-formedness.
*)
TypeOK ==
  /\ disk \in [Offsets -> Symbols]
  /\ len \in 0..MaxOffset
  /\ pos \in 0..len
  /\ bufBase \in 0..MaxOffset
  /\ buf \in [BufIdx -> Symbols]
  /\ bufValid \subseteq { i \in BufIdx : bufBase + i < MaxOffset }
  /\ bufDirty \subseteq bufValid
  /\ lastRead \in Symbols

(*
  Internal invariants about the buffer vs. disk and logical length.
*)
Inv1 == TypeOK

Inv3 ==
  \A i \in (bufValid \ bufDirty) :
    /\ bufBase + i < len
    => buf[i] = disk[bufBase + i]

Inv4 ==
  bufDirty \subseteq bufValid

Inv5 ==
  \A i \in bufValid :
    (bufBase + i) >= len => buf[i] = ArbitrarySymbol

(*
  Initialization.
  We begin with an arbitrary (unknown) disk image, empty/invalid buffer, and pos=0.
*)
Init ==
  /\ disk \in [Offsets -> Symbols]
  /\ len \in 0..MaxOffset
  /\ pos = 0
  /\ bufBase = 0
  /\ buf \in [BufIdx -> Symbols]
  /\ bufValid = {}
  /\ bufDirty = {}
  /\ lastRead = ArbitrarySymbol
  /\ Inv1

(*
  Concrete operations.
*)

SeekC ==
  /\ pos' \in 0..len
  /\ UNCHANGED << disk, len, bufBase, buf, bufValid, bufDirty, lastRead >>

(*
  Flush writes all dirty buffer entries that are within Offsets to disk and clears the dirty set.
*)
FlushC ==
  /\ disk' = OverlayDisk(disk, bufBase, buf, bufDirty)
  /\ bufDirty' = {}
  /\ UNCHANGED << len, pos, bufBase, buf, bufValid, lastRead >>

(*
  Refill (internal helper): rebase the buffer so it covers the current pos (unless pos=MaxOffset),
  load from disk for offsets < len and fill ArbitrarySymbol beyond len. Only permitted if no dirty data.
*)
RefillC ==
  /\ bufDirty = {}
  /\ \E newBase \in 0..MaxOffset :
        LET newValid == { i \in BufIdx : newBase + i < MaxOffset } IN
        /\ (pos = MaxOffset) \/ ( /\ pos >= newBase /\ pos < newBase + BuffSz )
        /\ bufBase' = newBase
        /\ buf' = [ i \in BufIdx |->
                     IF newBase + i < len
                     THEN disk[newBase + i]
                     ELSE ArbitrarySymbol
                  ]
        /\ bufValid' = newValid
        /\ bufDirty' = {}
        /\ UNCHANGED << disk, len, pos, lastRead >>

(*
  Write one symbol at the current position into the buffer.
  Extends the logical length if writing at/after the previous end.
  Requires the buffer to cover 'pos' (a refill may occur in a separate step).
*)
Write1C ==
  /\ pos < MaxOffset
  /\ BufCoversPos
  /\ \E v \in Symbols :
        LET i == pos - bufBase IN
        /\ i \in BufIdx
        /\ buf' = [buf EXCEPT ![i] = v]
        /\ bufValid' = bufValid \cup { i }
        /\ bufDirty' = bufDirty \cup { i }
        /\ pos' = pos + 1
        /\ len' = IF pos + 1 > len THEN pos + 1 ELSE len
        /\ UNCHANGED << disk, bufBase, lastRead >>

(*
  Read one symbol from the current position into 'lastRead'.
  If at/after EOF, returns ArbitrarySymbol and does not advance pos past len.
*)
Read1C ==
  /\ lastRead' = IF pos < len THEN AbsFile[pos] ELSE ArbitrarySymbol
  /\ pos' = IF pos < len THEN pos + 1 ELSE pos
  /\ UNCHANGED << disk, len, bufBase, buf, bufValid, bufDirty >>

(*
  Set the logical file length.
  Truncation makes bytes beyond newLen unknown (ArbitrarySymbol).
  Expansion leaves the new region explicitly unknown (ArbitrarySymbol).
*)
SetLengthC ==
  /\ \E newLen \in 0..MaxOffset :
        /\ len' = newLen
        /\ pos' = IF pos <= newLen THEN pos ELSE newLen
        /\ disk' = [ x \in Offsets |->
                       IF x < newLen THEN disk[x] ELSE ArbitrarySymbol
                   ]
        /\ buf' = [ i \in BufIdx |->
                       IF bufBase + i < newLen THEN buf[i] ELSE ArbitrarySymbol
                   ]
        /\ bufValid' = { i \in bufValid : bufBase + i < newLen }
        /\ bufDirty' = bufDirty \cap bufValid'
        /\ UNCHANGED lastRead

(*
  Next-state relation: a single concrete step is one of the operations above.
*)
Next == SeekC \/ FlushC \/ RefillC \/ Write1C \/ Read1C \/ SetLengthC

(*
  Specification: initialization, temporal closure, and weak fairness on maintenance steps
  so that buffer coverage can eventually be restored.
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(FlushC) /\ WF_vars(RefillC)

(*
  Safety-style invariants bundled under "Safety".
*)
Safety == [](Inv1 /\ Inv3 /\ Inv4 /\ Inv5)

(*
  Liveness and refinement-style properties for model checking.
*)

(*
  After any Flush step, the on-disk image equals the overlay of the prior disk with the dirty buffer,
  and the dirty set is cleared.
*)
FlushBufferCorrect ==
  [] ( FlushC
       => /\ disk' = OverlayDisk(disk, bufBase, buf, bufDirty)
          /\ bufDirty' = {}
     )

(*
  A Seek updates only the file pointer within bounds and leaves all other state unchanged.
*)
SeekCorrect ==
  [] ( SeekC
       => /\ pos' \in 0..len
          /\ UNCHANGED << disk, len, bufBase, buf, bufValid, bufDirty, lastRead >>
     )

(*
  After any Seek, the buffer coverage for the (new) position can eventually be restored.
*)
SeekEstablishesInv2 ==
  [] ( SeekC => <> BufCoversPos )

(*
  A single-byte write:
    - occurs within the buffer window
    - marks the written index valid and dirty
    - advances pos by 1 and extends len if needed
*)
Write1Correct ==
  [] ( Write1C
       => LET i == pos - bufBase IN
          /\ i \in BufIdx
          /\ i \in bufValid'
          /\ i \in bufDirty'
          /\ pos' = pos + 1
          /\ len' = IF pos + 1 > len THEN pos + 1 ELSE len
     )

(*
  A single-byte read returns the abstract-view byte at 'pos' and advances 'pos' iff pos < len.
*)
Read1Correct ==
  [] ( Read1C
       => /\ lastRead' = IF pos < len THEN AbsFile[pos] ELSE ArbitrarySymbol
          /\ pos' = IF pos < len THEN pos + 1 ELSE pos
     )

(*
  Writing never grows the file beyond MaxOffset.
*)
WriteAtMostCorrect ==
  [] ( Write1C => len' <= MaxOffset )

(*
  Read correctness (generalized restatement).
*)
ReadCorrect ==
  [] ( Read1C
       => /\ lastRead' \in Symbols
          /\ pos' <= len'
     )

(*
  Global liveness: buffer coverage can always eventually be (re)established.
*)
Inv2 ==
  BufCoversPos

Inv2CanAlwaysBeRestored ==
  []<>(Inv2)

==========================================================================================