---------------------- MODULE BufferedRandomAccessFile ----------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

ASSUME ArbitrarySymbol \notin Symbols
ASSUME MaxOffset \in Nat
ASSUME BuffSz \in Nat \ {0}

VARIABLES
    dirty,          \* buffer has unflushed writes
    length,         \* logical file length
    curr,           \* logical file position
    lo,             \* disk offset of first buffered byte
    buff,           \* buffer contents
    diskPos,        \* actual disk head position
    file_content,   \* underlying disk contents
    file_pointer    \* underlying disk pointer

vars == <<dirty, length, curr, lo, buff, diskPos, file_content, file_pointer>>

Offset            == 0..MaxOffset
SymbolOrArbitrary == Symbols \cup {ArbitrarySymbol}
BuffIdx           == 0..(BuffSz - 1)
Min(a, b)         == IF a < b THEN a ELSE b
Max(a, b)         == IF a > b THEN a ELSE b

ArrLen(a)              == Cardinality(DOMAIN a)
ArrayOfLen(n, T)       == [0..(n - 1) -> T]
ArrayOfAnyLength(T)    == UNION {ArrayOfLen(n, T) : n \in Offset}
EmptyArray             == [i \in {} |-> ArbitrarySymbol]
BoundedSeq             == UNION {[1..n -> Symbols] : n \in 1..BuffSz}

InWindow(i) == lo <= i /\ i < lo + BuffSz

\* The logical view: buffer overlaid on the disk contents.
LogicalFileContent ==
    [i \in 0..(length - 1) |->
        IF InWindow(i) THEN buff[i - lo]
        ELSE IF i < ArrLen(file_content) THEN file_content[i]
        ELSE ArbitrarySymbol]

Refill(newLo, content) ==
    [j \in BuffIdx |->
        IF newLo + j < ArrLen(content) THEN content[newLo + j]
        ELSE ArbitrarySymbol]

-----------------------------------------------------------------------------
(* Internal invariants *)

TypeOK ==
    /\ dirty \in BOOLEAN
    /\ length \in Offset
    /\ curr \in Offset
    /\ lo \in Offset
    /\ buff \in [BuffIdx -> SymbolOrArbitrary]
    /\ diskPos \in Offset
    /\ file_content \in ArrayOfAnyLength(SymbolOrArbitrary)
    /\ file_pointer \in Offset

\* Inv1: well-formedness of the buffered state
Inv1 == TypeOK

\* Inv2: the current position lies within the buffer window
Inv2 == lo <= curr /\ curr < lo + BuffSz

\* Inv3: buffer slots beyond the logical end hold no data; a clean buffer
\*       agrees with the disk
Inv3 ==
    /\ \A j \in BuffIdx : lo + j >= length => buff[j] = ArbitrarySymbol
    /\ ~dirty => \A j \in BuffIdx :
                    lo + j < length => buff[j] = file_content[lo + j]

\* Inv4: disk is never longer than the logical file; a clean buffer means
\*       the disk length equals the logical length
Inv4 ==
    /\ ArrLen(file_content) <= length
    /\ ~dirty => ArrLen(file_content) = length

\* Inv5: the modeled disk position matches the disk pointer
Inv5 == diskPos = file_pointer

-----------------------------------------------------------------------------
(* Actions *)

Init ==
    /\ dirty = FALSE
    /\ length = 0
    /\ curr = 0
    /\ lo = 0
    /\ buff = [j \in BuffIdx |-> ArbitrarySymbol]
    /\ diskPos = 0
    /\ file_content = EmptyArray
    /\ file_pointer = 0

FlushBuffer ==
    /\ dirty
    /\ file_content' = LogicalFileContent
    /\ dirty' = FALSE
    /\ diskPos' = lo
    /\ file_pointer' = lo
    /\ UNCHANGED <<length, curr, lo, buff>>

Seek(pos) ==
    IF lo <= pos /\ pos < lo + BuffSz
    THEN /\ curr' = pos
         /\ UNCHANGED <<dirty, length, lo, buff, diskPos, file_content, file_pointer>>
    ELSE LET fc == IF dirty THEN LogicalFileContent ELSE file_content
         IN /\ file_content' = fc
            /\ dirty' = FALSE
            /\ lo' = pos
            /\ curr' = pos
            /\ buff' = Refill(pos, fc)
            /\ diskPos' = pos
            /\ file_pointer' = pos
            /\ UNCHANGED length

SetLength(n) ==
    LET old == LogicalFileContent
        fc  == [i \in 0..(n - 1) |-> IF i < length THEN old[i] ELSE ArbitrarySymbol]
    IN /\ file_content' = fc
       /\ length' = n
       /\ dirty' = FALSE
       /\ buff' = Refill(lo, fc)
       /\ curr' = Min(curr, n)
       /\ UNCHANGED <<lo, diskPos, file_pointer>>

Read1 ==
    /\ Inv2
    /\ curr < length
    /\ curr' = curr + 1
    /\ UNCHANGED <<dirty, length, lo, buff, diskPos, file_content, file_pointer>>

Write1(s) ==
    /\ Inv2
    /\ curr < MaxOffset
    /\ buff' = [buff EXCEPT ![curr - lo] = s]
    /\ dirty' = TRUE
    /\ length' = Max(length, curr + 1)
    /\ curr' = curr + 1
    /\ UNCHANGED <<lo, diskPos, file_content, file_pointer>>

Read ==
    /\ Inv2
    /\ curr < length
    /\ \E k \in 1..(Min(lo + BuffSz, length) - curr) : curr' = curr + k
    /\ UNCHANGED <<dirty, length, lo, buff, diskPos, file_content, file_pointer>>

WriteAtMost(data) ==
    LET k == Min(Len(data), lo + BuffSz - curr)
    IN /\ Inv2
       /\ curr + k <= MaxOffset
       /\ buff' = [j \in BuffIdx |->
                    IF curr <= lo + j /\ lo + j < curr + k
                    THEN data[lo + j - curr + 1]
                    ELSE buff[j]]
       /\ dirty' = TRUE
       /\ length' = Max(length, curr + k)
       /\ curr' = curr + k
       /\ UNCHANGED <<lo, diskPos, file_content, file_pointer>>

Next ==
    \/ FlushBuffer
    \/ \E p \in Offset : Seek(p)
    \/ \E n \in Offset : SetLength(n)
    \/ Read1
    \/ \E s \in Symbols : Write1(s)
    \/ Read
    \/ \E d \in BoundedSeq : WriteAtMost(d)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Refinement of the abstract RandomAccessFile *)

RAF == INSTANCE RandomAccessFile
        WITH file_content <- LogicalFileContent,
             file_pointer <- curr

Refinement == RAF!Spec

\* Each concrete action refines its abstract counterpart
FlushRefines       == [][FlushBuffer => UNCHANGED <<LogicalFileContent, curr>>]_vars
SeekRefines        == [][\A p \in Offset : Seek(p) => RAF!Seek(p)]_vars
SetLengthRefines   == [][\A n \in Offset : SetLength(n) => RAF!SetLength(n)]_vars
Read1Refines       == [][Read1 => RAF!Read1]_vars
Write1Refines      == [][\A s \in Symbols : Write1(s) => RAF!Write1(s)]_vars
ReadRefines        == [][Read => RAF!Read]_vars
WriteAtMostRefines == [][\A d \in BoundedSeq : WriteAtMost(d) => RAF!WriteAtMost(d)]_vars

\* Inv2 can always be restored: after a flush, seeking to curr re-establishes it
Inv2Restorable ==
    [](~Inv2 => ENABLED (Seek(curr) /\ Inv2'))

FlushThenSeekRestoresInv2 ==
    [][ (~dirty /\ \E p \in Offset : Seek(p) /\ curr' = p /\ ~(lo <= p /\ p < lo + BuffSz))
          => Inv2' ]_vars

=============================================================================