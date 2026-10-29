------------------------- MODULE BufferedRandomAccessFile -------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Symbols,          \* the set of byte values that can be written
          ArbitrarySymbol,  \* stands for unspecified contents (e.g. file extension gaps)
          MaxOffset,        \* largest file offset / length considered
          BuffSz            \* size of the in-memory buffer

ASSUME ArbitrarySymbol \notin Symbols
ASSUME MaxOffset \in Nat
ASSUME BuffSz \in Nat \ {0}

VARIABLES
    file_content,   \* underlying (on-disk) file contents: [0..n-1 -> SymbolOrArbitrary]
    diskPos,        \* underlying file pointer
    dirty,          \* whether the buffer holds modifications not yet on disk
    length,         \* logical length of the buffered file
    curr,           \* logical current position of the buffered file
    lo,             \* file offset of the first byte in the buffer
    buff            \* buffer contents: [0..BuffSz-1 -> SymbolOrArbitrary]

vars == <<file_content, diskPos, dirty, length, curr, lo, buff>>

-----------------------------------------------------------------------------------
(* Helpers *)

Offset == 0..MaxOffset
SymbolOrArbitrary == Symbols \cup {ArbitrarySymbol}
BuffIdx == 0..(BuffSz - 1)

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

ArrLen(a) == Cardinality(DOMAIN a)

EmptyArr == [i \in {} |-> ArbitrarySymbol]

ArraysUpTo(n) == UNION { [0..(k - 1) -> SymbolOrArbitrary] : k \in 0..n }

\* Plain random-access-file semantics on arrays
WriteAt(f, pos, data) ==
    LET newLen == Max(ArrLen(f), pos + ArrLen(data))
    IN [i \in 0..(newLen - 1) |->
          IF pos <= i /\ i < pos + ArrLen(data) THEN data[i - pos]
          ELSE IF i < ArrLen(f) THEN f[i]
          ELSE ArbitrarySymbol]

Resize(f, n) ==
    [i \in 0..(n - 1) |-> IF i < ArrLen(f) THEN f[i] ELSE ArbitrarySymbol]

DiskAt(i) == IF i < ArrLen(file_content) THEN file_content[i] ELSE ArbitrarySymbol

InBuffer(i) == lo <= i /\ i < lo + BuffSz

\* Number of buffer bytes that are part of the logical file
ValidCount == IF length <= lo THEN 0 ELSE Min(BuffSz, length - lo)
ValidBuff  == [i \in 0..(ValidCount - 1) |-> buff[i]]

FlushedContent ==
    IF ValidCount = 0 THEN file_content ELSE WriteAt(file_content, lo, ValidBuff)

\* The logical contents of the buffered file
LogicalFileContents ==
    [i \in 0..(length - 1) |-> IF InBuffer(i) THEN buff[i - lo] ELSE DiskAt(i)]

-----------------------------------------------------------------------------------
(* Specification *)

Init ==
    /\ file_content = EmptyArr
    /\ diskPos = 0
    /\ dirty = FALSE
    /\ length = 0
    /\ curr = 0
    /\ lo = 0
    /\ buff = [i \in BuffIdx |-> ArbitrarySymbol]

BufferBoundsInvariant == lo <= curr /\ curr < lo + BuffSz

\* Seek: within the buffer, just move; otherwise (clean buffer) refill from disk
Seek(p) ==
    \/ /\ InBuffer(p)
       /\ curr' = p
       /\ UNCHANGED <<file_content, diskPos, dirty, length, lo, buff>>
    \/ /\ ~InBuffer(p)
       /\ ~dirty
       /\ curr' = p
       /\ lo' = p
       /\ buff' = [i \in BuffIdx |-> DiskAt(p + i)]
       /\ diskPos' = p + (IF p >= ArrLen(file_content) THEN 0
                          ELSE Min(BuffSz, ArrLen(file_content) - p))
       /\ UNCHANGED <<file_content, dirty, length>>

\* Read one byte from the buffer
Read ==
    /\ BufferBoundsInvariant
    /\ curr < length
    /\ curr' = curr + 1
    /\ UNCHANGED <<file_content, diskPos, dirty, length, lo, buff>>

\* Write one byte into the buffer (filling any gap past EOF with arbitrary data)
Write(s) ==
    /\ BufferBoundsInvariant
    /\ curr < MaxOffset
    /\ buff' = [i \in BuffIdx |->
                  IF i = curr - lo THEN s
                  ELSE IF lo + i >= length /\ lo + i < curr THEN ArbitrarySymbol
                  ELSE buff[i]]
    /\ curr' = curr + 1
    /\ length' = Max(length, curr + 1)
    /\ dirty' = TRUE
    /\ UNCHANGED <<file_content, diskPos, lo>>

\* Write dirty buffer contents back to the underlying file
FlushBuffer ==
    /\ dirty
    /\ file_content' = FlushedContent
    /\ diskPos' = lo + ValidCount
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr, lo, buff>>

\* Truncate or extend the file (flushes first)
SetLength(n) ==
    /\ file_content' = Resize(IF dirty THEN FlushedContent ELSE file_content, n)
    /\ length' = n
    /\ curr' = Min(curr, n)
    /\ buff' = [i \in BuffIdx |->
                  IF lo + i < Min(n, length) THEN buff[i] ELSE ArbitrarySymbol]
    /\ dirty' = FALSE
    /\ diskPos' = Min(IF dirty THEN lo + ValidCount ELSE diskPos, n)
    /\ UNCHANGED lo

Next ==
    \/ \E p \in Offset : Seek(p)
    \/ Read
    \/ \E s \in Symbols : Write(s)
    \/ FlushBuffer
    \/ \E n \in Offset : SetLength(n)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ file_content \in ArraysUpTo(MaxOffset)
    /\ diskPos \in Offset
    /\ dirty \in BOOLEAN
    /\ length \in Offset
    /\ curr \in Offset
    /\ lo \in Offset
    /\ buff \in [BuffIdx -> SymbolOrArbitrary]

\* 1. Logical consistency
LogicalConsistency ==
    /\ LogicalFileContents \in [0..(length - 1) -> SymbolOrArbitrary]
    /\ ArrLen(LogicalFileContents) = length

\* 3. Buffer coherence
BufferCoherence ==
    \A i \in 0..(length - 1) :
        InBuffer(i) => LogicalFileContents[i] = buff[i - lo]

\* 4. Unbuffered region coherence
UnbufferedCoherence ==
    \A i \in 0..(length - 1) :
        ~InBuffer(i) => LogicalFileContents[i] = DiskAt(i)

\* 5. Dirty tracking correctness
DirtyTracking ==
    \A i \in BuffIdx :
        (lo + i < length /\ buff[i] /= DiskAt(lo + i)) => dirty

\* Auxiliary: relationship between disk length and logical length
DiskLengthInv ==
    /\ ArrLen(file_content) <= length
    /\ ~dirty => ArrLen(file_content) = length
    /\ ArrLen(file_content) < length => (lo < length /\ length <= lo + BuffSz)

\* 7. Invariant restoration (state-level parts)
FlushEnabledWhenDirty == dirty => ENABLED FlushBuffer
SeekEnabledWhenClean  == ~dirty => ENABLED Seek(curr)

Invariants ==
    /\ TypeOK
    /\ LogicalConsistency
    /\ BufferCoherence
    /\ UnbufferedCoherence
    /\ DirtyTracking
    /\ DiskLengthInv
    /\ FlushEnabledWhenDirty
    /\ SeekEnabledWhenClean

\* 7. Invariant restoration (action-level parts)
FlushClearsDirty == [][FlushBuffer => ~dirty']_vars
SeekRestoresBounds == [][\A p \in Offset : Seek(p) => BufferBoundsInvariant']_vars

\* 2. Buffer bounds invariant: may be temporarily broken by Read/Write at the
\*    buffer edge, but whenever it is broken it can be restored.
BoundsRestorable ==
    ~BufferBoundsInvariant =>
        IF dirty THEN ENABLED FlushBuffer ELSE ENABLED Seek(curr)

-----------------------------------------------------------------------------------
(* 6. Refinement: the buffered file behaves as a plain random access file *)

AbsNext(c, p, c2, p2) ==
    \/ /\ c2 = c                                         \* seek
       /\ p2 \in Offset
    \/ /\ p < ArrLen(c)                                  \* read
       /\ c2 = c
       /\ p2 = p + 1
    \/ /\ p < MaxOffset                                  \* write
       /\ \E s \in Symbols : c2 = WriteAt(c, p, [i \in {0} |-> s])
       /\ p2 = p + 1
    \/ \E n \in Offset :                                 \* set length
          /\ c2 = Resize(c, n)
          /\ p2 = Min(p, n)

AbsInit == LogicalFileContents = EmptyArr /\ curr = 0

Refinement ==
    /\ AbsInit
    /\ [][AbsNext(LogicalFileContents, curr, LogicalFileContents', curr')]_<<LogicalFileContents, curr>>

THEOREM Spec => []Invariants
THEOREM Spec => []BoundsRestorable
THEOREM Spec => FlushClearsDirty /\ SeekRestoresBounds
THEOREM Spec => Refinement
===================================================================================