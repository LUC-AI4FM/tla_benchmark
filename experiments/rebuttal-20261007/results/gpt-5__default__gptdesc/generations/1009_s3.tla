------------------------------ MODULE BufferedRandomAccessFile ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
System overview:
- Single-threaded buffered random-access file with write-back buffer.
- Concrete state includes: file pointer, logical length, disk image and its persisted length, an in-memory buffer (values plus a finite "dirty" set of indices), and the last bytes read.
- Abstract RandomAccessFile state includes: abstract pointer, length, and full array contents.
- The buffer is modeled as a total function buf: Indices -> Values together with a finite set dirty ⊆ Indices indicating which indices overlay the disk (write-back).
- Underspecified/unknown on-disk content is represented by ArbitrarySymbol ∉ ByteSet.
- Operations: seek, read, write, flush, setLength.
- Refinement: every concrete step also performs its abstract counterpart; invariants relate abstract and concrete states.
- Safety invariants and liveness (weak fairness for Next) are included.
- A suggested TLC configuration is included below as a comment.

Suggested TLC configuration (example):
(*
CONSTANTS
  MaxLen = 8
  BufCap = 4
  MaxIO  = 3
  ByteSet = 0..1
  ArbitrarySymbol = "⊥"

SPECIFICATION Spec
INVARIANTS
  TypeInv
  BufferInv
  AbstractionInv
  LogValueTypeInv

PROPERTIES
  RefinesAbs
  RefineSeek
  RefineRead
  RefineWrite
  RefineFlush
  RefineSetLength
*)
*)

CONSTANTS
  MaxLen,         \* Maximum file length modeled (positive Nat)
  BufCap,         \* Maximum number of buffered (dirty) indices allowed
  MaxIO,          \* Maximum length of a single read/write request
  ByteSet,        \* Set of concrete byte values (finite)
  ArbitrarySymbol \* Distinguished value not in ByteSet, used for unknowns

ASSUME
  /\ MaxLen \in Nat /\ MaxLen > 0
  /\ BufCap \in Nat
  /\ MaxIO \in Nat
  /\ ArbitrarySymbol \notin ByteSet

(*
Basic sets and utility operators
*)
Values  == ByteSet \cup {ArbitrarySymbol}
Indices == 0..(MaxLen - 1)

Min(a,b) == IF a < b THEN a ELSE b
Max(a,b) == IF a < b THEN b ELSE a

RangeSet(s, c) == s..(s + c - 1)

Overlay(f, s, w) ==
  [ i \in Indices |->
      IF i \in RangeSet(s, Len(w)) THEN w[i - s + 1] ELSE f[i]
  ]

(*
State variables:
- Concrete: pos, len, disk, diskLen, buf, dirty, lastRead
- Abstract: absPos, absLen, absArr
*)
VARIABLES
  pos, len, disk, diskLen, buf, dirty, lastRead,
  absPos, absLen, absArr

vars    == << pos, len, disk, diskLen, buf, dirty, lastRead, absPos, absLen, absArr >>
absVars == << absPos, absLen, absArr >>

(*
Concrete/logical view of a byte at index i:
- If dirty[i], return buffered value
- Else if i < diskLen, return on-disk value
- Else (i >= diskLen), unknown ArbitrarySymbol
Note: Only indices < len are logical file content; >= len is out of logical range.
*)
LogValue(i) ==
  IF i \in dirty THEN buf[i]
  ELSE IF i < diskLen THEN disk[i]
  ELSE ArbitrarySymbol

ReadSeqFromLog(start, count) ==
  [ k \in 1..count |-> LogValue(start + k - 1) ]

ReadSeqFromAbs(start, count) ==
  [ k \in 1..count |-> absArr[start + k - 1] ]

(*
Initial state:
- Pointer at 0.
- Logical length and disk length are arbitrary in 0..MaxLen (can be 0).
- Disk and buffer are total functions Indices -> Values (arbitrary).
- No dirty buffered indices initially; lastRead is empty sequence.
- Abstract state equals the concrete logical view initially (refinement holds initially).
*)
Init ==
  /\ pos \in 0..MaxLen
  /\ len \in 0..MaxLen
  /\ disk \in [Indices -> Values]
  /\ diskLen \in 0..MaxLen
  /\ buf \in [Indices -> Values]
  /\ dirty = {}
  /\ lastRead = <<>>
  /\ absPos = pos
  /\ absLen = len
  /\ absArr =
       [ i \in Indices |->
           IF i < len THEN (IF i < diskLen THEN disk[i] ELSE ArbitrarySymbol)
           ELSE ArbitrarySymbol
       ]

(*
Abstract operations (on absPos, absLen, absArr only)
*)
SeekAbs ==
  \E p \in 0..MaxLen:
    /\ absPos' = p
    /\ UNCHANGED << absLen, absArr >>

ReadAbs ==
  \E n \in 0..MaxIO:
    LET cnt == IF absPos < absLen THEN Min(n, absLen - absPos) ELSE 0
    IN
    /\ absPos' = absPos + cnt
    /\ UNCHANGED << absLen, absArr >>

WriteAbs ==
  \E w \in Seq(Values):
    /\ Len(w) <= MaxIO
    /\ absPos + Len(w) <= MaxLen
    /\ absArr' = Overlay(absArr, absPos, w)
    /\ absPos' = absPos + Len(w)
    /\ absLen' = Max(absLen, absPos + Len(w))

FlushAbs ==
  UNCHANGED absVars

SetLengthAbs ==
  \E L \in 0..MaxLen:
    /\ absPos' = absPos
    /\ absLen' = L
    /\ absArr' =
         [ i \in Indices |->
             IF /\ i >= absLen /\ i < L
             THEN ArbitrarySymbol
             ELSE absArr[i]
         ]

AbsNext == SeekAbs \/ ReadAbs \/ WriteAbs \/ FlushAbs \/ SetLengthAbs
AbsInit == Init  \* abs state is initialized in concert with concrete in Init
AbsSpec == AbsInit /\ [][AbsNext]_absVars

(*
Concrete operations, coupled with their abstract counterparts.
Each concrete operation simultaneously performs the corresponding abstract op
to make the step-wise refinement explicit and checkable.
*)

DoSeek ==
  \E p \in 0..MaxLen:
    /\ pos' = p
    /\ lastRead' = <<>>
    /\ UNCHANGED << len, disk, diskLen, buf, dirty >>
    /\ absPos' = p
    /\ UNCHANGED << absLen, absArr >>

DoRead ==
  \E n \in 0..MaxIO:
    LET cnt == IF pos < len THEN Min(n, len - pos) ELSE 0 IN
    LET r   == ReadSeqFromLog(pos, cnt) IN
    /\ pos' = pos + cnt
    /\ lastRead' = r
    /\ UNCHANGED << len, disk, diskLen, buf, dirty >>
    /\ absPos' = absPos + cnt
    /\ UNCHANGED << absLen, absArr >>

DoWrite ==
  \E w \in Seq(Values):
    /\ Len(w) <= MaxIO
    /\ pos + Len(w) <= MaxLen
    /\ Cardinality(dirty \cup RangeSet(pos, Len(w))) <= BufCap
    LET posNext == pos + Len(w) IN
    /\ buf'   = Overlay(buf, pos, w)
    /\ dirty' = dirty \cup RangeSet(pos, Len(w))
    /\ pos'   = posNext
    /\ len'   = Max(len, posNext)
    /\ lastRead' = <<>>
    /\ UNCHANGED << disk, diskLen >>
    /\ absArr' = Overlay(absArr, absPos, w)
    /\ absPos' = absPos + Len(w)
    /\ absLen' = Max(absLen, absPos + Len(w))

DoFlush ==
  /\ disk'    = [ i \in Indices |->
                    IF i \in dirty THEN buf[i] ELSE disk[i] ]
  /\ diskLen' = Max(diskLen, len)
  /\ dirty'   = {}
  /\ UNCHANGED << buf, pos, len, lastRead >>
  /\ UNCHANGED absVars

DoSetLength ==
  \E L \in 0..MaxLen:
    /\ pos' = pos
    /\ len' = L
    /\ dirty' = { i \in dirty : i < L }
    /\ UNCHANGED << buf, disk, diskLen, lastRead >>
    /\ absPos' = absPos
    /\ absLen' = L
    /\ absArr' =
         [ i \in Indices |->
             IF /\ i >= absLen /\ i < L
             THEN ArbitrarySymbol
             ELSE absArr[i]
         ]

Next == DoSeek \/ DoRead \/ DoWrite \/ DoFlush \/ DoSetLength

(*
Main specification with weak fairness to rule out infinite stuttering
when Next is continuously enabled (it is, due to Seek).
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
Safety invariants
*)
TypeInv ==
  /\ pos \in 0..MaxLen
  /\ len \in 0..MaxLen
  /\ disk \in [Indices -> Values]
  /\ diskLen \in 0..MaxLen
  /\ buf \in [Indices -> Values]
  /\ dirty \subseteq Indices
  /\ lastRead \in Seq(Values)
  /\ absPos \in 0..MaxLen
  /\ absLen \in 0..MaxLen
  /\ absArr \in [Indices -> Values]

BufferInv ==
  /\ Cardinality(dirty) <= BufCap

LogValueTypeInv ==
  \A i \in Indices:
     IF i < len THEN LogValue(i) \in Values ELSE TRUE

AbstractionInv ==
  /\ absPos = pos
  /\ absLen = len
  /\ \A i \in 0..(len - 1): absArr[i] = LogValue(i)

SafetyInvs == TypeInv /\ BufferInv /\ LogValueTypeInv /\ AbstractionInv

(*
Refinement properties
- Whole-behavior refinement: every behavior of Spec projects to a behavior of AbsSpec.
- Per-operation step refinement: each concrete action implies its abstract counterpart.
*)
RefinesAbs == AbsSpec

RefineSeek      == [](DoSeek      => SeekAbs)
RefineRead      == [](DoRead      => ReadAbs)
RefineWrite     == [](DoWrite     => WriteAbs)
RefineFlush     == [](DoFlush     => FlushAbs)
RefineSetLength == [](DoSetLength => SetLengthAbs)

=============================================================================