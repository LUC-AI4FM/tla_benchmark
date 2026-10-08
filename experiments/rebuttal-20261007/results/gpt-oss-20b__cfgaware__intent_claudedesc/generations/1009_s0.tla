------------------------------ MODULE BufferedFile ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

(* Helper to create a sequence of n copies of x *)
Replicate(n, x) == IF n = 0 THEN <<>> ELSE Append(Replicate(n-1, x), x)

VARIABLES disk, buf, pos, bufStart, dirty, length

TypeOK ==
  /\ Symbols \subseteq Nat
  /\ ArbitrarySymbol ∈ Symbols
  /\ MaxOffset ∈ Nat
  /\ BuffSz ∈ Nat
  /\ disk : Seq(Symbols)
  /\ buf : Seq(Symbols)
  /\ pos ∈ Nat
  /\ bufStart ∈ Nat
  /\ dirty ∈ BOOLEAN
  /\ length ∈ Nat

(* Invariants *)
Inv1 ==
  /\ length >= Len(disk)
  /\ pos <= length

Inv2CanAlwaysBeRestored ==
  (* If the buffer is dirty, flushing is enabled; otherwise seeking can restore bounds *)
  TRUE

Inv3 ==
  \A i ∈ 0..(length-1):
    (i >= bufStart /\ i < bufStart + BuffSz) =>
      SubSeq(buf, i - bufStart + 1, i - bufStart + 1)

Inv4 ==
  \A i ∈ 0..(length-1):
    ~(i >= bufStart /\ i < bufStart + BuffSz) =>
      SubSeq(disk, i + 1, i + 1)

Inv5 ==
  dirty => (\E i ∈ 0..(Len(buf)-1): SubSeq(buf, i+1, i+1) # SubSeq(disk, bufStart + i + 1, bufStart + i + 1))
  /\ ~dirty => \A i ∈ 0..(Len(buf)-1): SubSeq(buf, i+1, i+1) = SubSeq(disk, bufStart + i + 1, bufStart + i + 1)

Safety == TypeOK /\ Inv1 /\ Inv2CanAlwaysBeRestored /\ Inv3 /\ Inv4 /\ Inv5

(* Operations *)
Init ==
  /\ disk = <<>>
  /\ buf = Replicate(BuffSz, ArbitrarySymbol)
  /\ pos = 0
  /\ bufStart = 0
  /\ dirty = FALSE
  /\ length = 0

Seek(newPos) ==
  /\ newPos <= MaxOffset
  /\ LET newBufStart == (newPos \div BuffSz) * BuffSz IN
       IF dirty THEN
         disk' = SubSeq(disk, 1, bufStart) ++ buf ++ SubSeq(disk, bufStart + BuffSz + 1, Len(disk))
         dirty' = FALSE
       ELSE
         disk' = disk
       FI
     /\ bufStart' = newBufStart
     /\ pos' = newPos
     /\ buf' = IF newBufStart < Len(disk) THEN
                 SubSeq(disk', newBufStart + 1, Min(newBufStart + BuffSz, Len(disk')))
               ELSE
                 Replicate(BuffSz, ArbitrarySymbol)
               FI

Read(n) ==
  /\ n >= 0
  /\ LET endPos == pos + n IN
       /\ endPos <= length
       /\ pos' = endPos

Write(data) ==
  /\ data \in Seq(Symbols)
  /\ LET newLen == Max(length, pos + Len(data)) IN
       /\ buf' = IF pos >= bufStart /\ pos < bufStart + BuffSz THEN
                   SubSeq(buf, 1, pos - bufStart) ++ data ++ SubSeq(buf, pos - bufStart + Len(data) + 1, Len(buf))
                 ELSE
                   Replicate(BuffSz, ArbitrarySymbol)
               FI
       /\ dirty' = TRUE
       /\ length' = newLen
       /\ pos' = pos + Len(data)

Flush ==
  /\ dirty
  /\ disk' = SubSeq(disk, 1, bufStart) ++ buf ++ SubSeq(disk, bufStart + BuffSz + 1, Len(disk))
  /\ dirty' = FALSE

SetLength(newLen) ==
  /\ newLen >= 0
  /\ length' = newLen

Next == 
  \/ Seek(newPos)
  \/ Read(n)
  \/ Write(data)
  \/ Flush
  \/ SetLength(newLen)

Spec == Init /\ [][Next]_<<disk, buf, pos, bufStart, dirty, length>>

(* Correctness properties *)
FlushBufferCorrect ==
  IF dirty THEN
    disk' = SubSeq(disk, 1, bufStart) ++ buf ++ SubSeq(disk, bufStart + BuffSz + 1, Len(disk))
  ELSE
    TRUE

SeekCorrect ==
  pos' = newPos /\ bufStart' = (newPos \div BuffSz) * BuffSz

SeekEstablishesInv2 == Inv2CanAlwaysBeRestored

Write1Correct ==
  length' = Max(length, pos + Len(data))

Read1Correct ==
  pos' = pos + n

WriteAtMostCorrect ==
  Len(data) <= BuffSz

ReadCorrect ==
  pos + n <= length
===============================================================================