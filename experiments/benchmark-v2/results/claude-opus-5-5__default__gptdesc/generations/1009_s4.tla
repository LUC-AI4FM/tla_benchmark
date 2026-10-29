------------------------- MODULE BufferedRandomAccessFile -------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Shared array/file utilities (the "Common" part).                        *)
(***************************************************************************)

CONSTANTS
    Symbols,          \* the set of symbols that may be written to a file
    ArbitrarySymbol,  \* stands for underspecified file contents
    MaxOffset,        \* largest file offset / length considered
    BuffSize          \* capacity of the in-memory buffer

ASSUME ConstantsOK ==
    /\ IsFiniteSet(Symbols)
    /\ ArbitrarySymbol \notin Symbols
    /\ MaxOffset \in Nat
    /\ BuffSize \in Nat \ {0}

Offset == 0..MaxOffset

SymbolOrArbitrary == Symbols \cup {ArbitrarySymbol}

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

\* Arrays are sequences; offsets are 0-based, sequence indices are 1-based.
ArrayOfAnyLength(T) == UNION { [1..n -> T] : n \in Offset }

EmptyArray == << >>

\* Contents of array arr at 0-based offset p (arbitrary beyond its end).
ArrayAt(arr, p) == IF p < Len(arr) THEN arr[p + 1] ELSE ArbitrarySymbol

\* Write symbol c at 0-based offset off, filling any gap with ArbitrarySymbol.
WriteAt(arr, off, c) ==
    [i \in 1..Max(Len(arr), off + 1) |->
        IF i = off + 1 THEN c
        ELSE IF i <= Len(arr) THEN arr[i]
        ELSE ArbitrarySymbol]

\* Truncate or extend arr to length n; new positions are arbitrary.
SetLen(arr, n) ==
    [i \in 1..n |-> IF i <= Len(arr) THEN arr[i] ELSE ArbitrarySymbol]

(***************************************************************************)
(* Concrete state of the buffered random access file.                      *)
(***************************************************************************)

VARIABLES
    disk,      \* on-disk contents of the underlying file
    diskPos,   \* file pointer of the underlying (unbuffered) file
    dirty,     \* TRUE iff the buffer holds data not yet written to disk
    length,    \* logical length of the file
    curr,      \* logical file pointer
    lo,        \* the buffer covers offsets [lo, hi)
    hi,
    buff       \* buffer contents; buff[k] holds the symbol at offset lo + k - 1

vars == << disk, diskPos, dirty, length, curr, lo, hi, buff >>

TypeOK ==
    /\ disk \in ArrayOfAnyLength(SymbolOrArbitrary)
    /\ diskPos \in Offset
    /\ dirty \in BOOLEAN
    /\ length \in Offset
    /\ curr \in Offset
    /\ lo \in Offset
    /\ hi \in Offset
    /\ buff \in [1..BuffSize -> SymbolOrArbitrary]

(***************************************************************************)
(* Refinement mapping: the logical file seen by clients.                   *)
(***************************************************************************)

AbsContent ==
    [i \in 1..length |->
        IF lo <= i - 1 /\ i - 1 < hi
            THEN buff[i - lo]
            ELSE ArrayAt(disk, i - 1)]

AbsPointer == curr

absVars == << AbsContent, AbsPointer >>

(***************************************************************************)
(* Abstract RandomAccessFile specification, expressed over the mapping.    *)
(***************************************************************************)

AInit ==
    /\ AbsContent = EmptyArray
    /\ AbsPointer = 0

ASeek(pos) ==
    /\ pos \in Offset
    /\ AbsPointer' = pos
    /\ AbsContent' = AbsContent

ARead(c) ==
    /\ AbsPointer < Len(AbsContent)
    /\ c = AbsContent[AbsPointer + 1]
    /\ AbsPointer' = AbsPointer + 1
    /\ AbsContent' = AbsContent

AWrite(c) ==
    /\ c \in Symbols
    /\ AbsPointer < MaxOffset
    /\ AbsContent' = WriteAt(AbsContent, AbsPointer, c)
    /\ AbsPointer' = AbsPointer + 1

ASetLength(n) ==
    /\ n \in Offset
    /\ AbsContent' = SetLen(AbsContent, n)
    /\ AbsPointer' = Min(AbsPointer, n)

AFlush ==
    /\ AbsContent' = AbsContent
    /\ AbsPointer' = AbsPointer

ANext ==
    \/ \E pos \in Offset : ASeek(pos)
    \/ \E c \in SymbolOrArbitrary : ARead(c)
    \/ \E c \in Symbols : AWrite(c)
    \/ \E n \in Offset : ASetLength(n)
    \/ AFlush

(***************************************************************************)
(* Concrete operations.                                                    *)
(***************************************************************************)

\* Disk contents after writing a dirty buffer back.
FlushedDisk ==
    IF dirty
        THEN [i \in 1..Max(Len(disk), hi) |->
                IF lo < i /\ i <= hi THEN buff[i - lo] ELSE ArrayAt(disk, i - 1)]
        ELSE disk

FlushedPos == IF dirty THEN hi ELSE diskPos

Init ==
    /\ disk = EmptyArray
    /\ diskPos = 0
    /\ dirty = FALSE
    /\ length = 0
    /\ curr = 0
    /\ lo = 0
    /\ hi = 0
    /\ buff = [k \in 1..BuffSize |-> ArbitrarySymbol]

Seek(pos) ==
    /\ curr' = pos
    /\ UNCHANGED << disk, diskPos, dirty, length, lo, hi, buff >>

Read(c) ==
    /\ curr < length
    /\ IF lo <= curr /\ curr < hi
          THEN /\ c = buff[curr - lo + 1]
               /\ UNCHANGED << disk, diskPos, dirty, lo, hi, buff >>
          ELSE LET nd  == FlushedDisk
                   nhi == Min(curr + BuffSize, length)
               IN  /\ disk' = nd
                   /\ lo' = curr
                   /\ hi' = nhi
                   /\ buff' = [k \in 1..BuffSize |-> ArrayAt(nd, curr + k - 1)]
                   /\ diskPos' = nhi
                   /\ dirty' = FALSE
                   /\ c = ArrayAt(nd, curr)
    /\ curr' = curr + 1
    /\ UNCHANGED length

Write(c) ==
    /\ curr < MaxOffset
    /\ IF lo <= curr /\ curr <= hi /\ curr < lo + BuffSize
          THEN /\ buff' = [buff EXCEPT ![curr - lo + 1] = c]
               /\ hi' = Max(hi, curr + 1)
               /\ UNCHANGED << disk, diskPos, lo >>
          ELSE /\ disk' = FlushedDisk
               /\ diskPos' = FlushedPos
               /\ lo' = curr
               /\ hi' = curr + 1
               /\ buff' = [buff EXCEPT ![1] = c]
    /\ dirty' = TRUE
    /\ curr' = curr + 1
    /\ length' = Max(length, curr + 1)

Flush ==
    /\ disk' = FlushedDisk
    /\ diskPos' = FlushedPos
    /\ dirty' = FALSE
    /\ UNCHANGED << length, curr, lo, hi, buff >>

SetLength(n) ==
    LET nd == FlushedDisk IN
    /\ disk' = SetLen(nd, n)
    /\ diskPos' = Min(FlushedPos, n)
    /\ length' = n
    /\ lo' = Min(lo, n)
    /\ hi' = Min(hi, n)
    /\ curr' = Min(curr, n)
    /\ dirty' = FALSE
    /\ UNCHANGED buff

Next ==
    \/ \E pos \in Offset : Seek(pos)
    \/ \E c \in SymbolOrArbitrary : Read(c)
    \/ \E c \in Symbols : Write(c)
    \/ Flush
    \/ \E n \in Offset : SetLength(n)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Internal invariants.                                                    *)
(***************************************************************************)

BufferBounds ==
    /\ lo <= hi
    /\ hi - lo <= BuffSize
    /\ hi <= length

DiskNotLongerThanFile == Len(disk) <= length

LengthBounded == length <= MaxOffset

DirtyImpliesNonEmptyBuffer == dirty => lo < hi

CleanBufferMatchesDisk ==
    ~dirty => \A p \in lo..(hi - 1) : buff[p - lo + 1] = ArrayAt(disk, p)

DiskBeyondBufferMatchesLogical ==
    \A p \in 0..(length - 1) :
        (p < lo \/ p >= hi) => AbsContent[p + 1] = ArrayAt(disk, p)

LogicalContentWellTyped ==
    /\ AbsContent \in ArrayOfAnyLength(SymbolOrArbitrary)
    /\ Len(AbsContent) = length

Invariants ==
    /\ TypeOK
    /\ BufferBounds
    /\ DiskNotLongerThanFile
    /\ LengthBounded
    /\ DirtyImpliesNonEmptyBuffer
    /\ CleanBufferMatchesDisk
    /\ DiskBeyondBufferMatchesLogical
    /\ LogicalContentWellTyped

(***************************************************************************)
(* Refinement properties.                                                  *)
(***************************************************************************)

\* The whole behavior refines the abstract RandomAccessFile spec.
Refinement == AInit /\ [][ANext]_absVars

\* Each concrete operation refines its abstract counterpart.
SeekRefinesAbstract ==
    [][\A pos \in Offset : Seek(pos) => ASeek(pos)]_vars

ReadRefinesAbstract ==
    [][\A c \in SymbolOrArbitrary : Read(c) => ARead(c)]_vars

WriteRefinesAbstract ==
    [][\A c \in Symbols : Write(c) => AWrite(c)]_vars

FlushRefinesAbstract ==
    [][Flush => AFlush]_vars

SetLengthRefinesAbstract ==
    [][\A n \in Offset : SetLength(n) => ASetLength(n)]_vars

(***************************************************************************)
(* Model-checking helpers.                                                 *)
(***************************************************************************)

Symmetry == Permutations(Symbols)

Alias ==
    [ disk       |-> disk,
      diskPos    |-> diskPos,
      dirty      |-> dirty,
      length     |-> length,
      curr       |-> curr,
      lo         |-> lo,
      hi         |-> hi,
      buff       |-> buff,
      logical    |-> AbsContent ]

(***************************************************************************)
(* TLC configuration (BufferedRandomAccessFile.cfg):                       *)
(*                                                                         *)
(*   CONSTANTS                                                             *)
(*       Symbols = {a, b}                                                  *)
(*       ArbitrarySymbol = ArbitrarySymbol                                 *)
(*       MaxOffset = 3                                                     *)
(*       BuffSize = 2                                                      *)
(*   SYMMETRY Symmetry                                                     *)
(*   SPECIFICATION Spec                                                    *)
(*   ALIAS Alias                                                           *)
(*   INVARIANTS                                                            *)
(*       TypeOK                                                            *)
(*       BufferBounds                                                      *)
(*       DiskNotLongerThanFile                                             *)
(*       LengthBounded                                                     *)
(*       DirtyImpliesNonEmptyBuffer                                        *)
(*       CleanBufferMatchesDisk                                            *)
(*       DiskBeyondBufferMatchesLogical                                    *)
(*       LogicalContentWellTyped                                           *)
(*   PROPERTIES                                                            *)
(*       Refinement                                                        *)
(*       SeekRefinesAbstract                                               *)
(*       ReadRefinesAbstract                                               *)
(*       WriteRefinesAbstract                                              *)
(*       FlushRefinesAbstract                                              *)
(*       SetLengthRefinesAbstract                                          *)
(***************************************************************************)
=============================================================================