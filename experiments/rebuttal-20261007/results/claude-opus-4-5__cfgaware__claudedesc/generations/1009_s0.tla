---------------------------- MODULE BufferedRandomAccessFile ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

VARIABLES dirty, length, curr, lo, buff, diskPos, file_content, file_pointer

vars == <<dirty, length, curr, lo, buff, diskPos, file_content, file_pointer>>

Offsets == 0..MaxOffset

BuffOffsets == 0..(BuffSz - 1)

\* The logical file content is the disk content with the buffer overlaid
LogicalFileContent ==
    [i \in Offsets |-> 
        IF i >= lo /\ i < lo + BuffSz /\ i < length
        THEN buff[i - lo]
        ELSE file_content[i]]

\* Type invariant
TypeOK ==
    /\ dirty \in BOOLEAN
    /\ length \in 0..(MaxOffset + 1)
    /\ curr \in Offsets
    /\ lo \in Offsets
    /\ buff \in [BuffOffsets -> Symbols]
    /\ diskPos \in Offsets
    /\ file_content \in [Offsets -> Symbols]
    /\ file_pointer \in Offsets

\* Inv1: curr is within valid range
Inv1 == curr <= length

\* Inv2: buffer window invariant - lo <= curr < lo + BuffSz
Inv2 == lo <= curr /\ curr < lo + BuffSz

\* Inv3: lo + BuffSz does not exceed MaxOffset + 1
Inv3 == lo + BuffSz <= MaxOffset + 1

\* Inv4: if not dirty, buffer matches disk in the buffered region
Inv4 == ~dirty => \A i \in BuffOffsets : 
    (lo + i < length) => buff[i] = file_content[lo + i]

\* Inv5: disk position consistency
Inv5 == diskPos <= length

\* Initialize the system
Init ==
    /\ dirty = FALSE
    /\ length = 0
    /\ curr = 0
    /\ lo = 0
    /\ buff = [i \in BuffOffsets |-> ArbitrarySymbol]
    /\ diskPos = 0
    /\ file_content = [i \in Offsets |-> ArbitrarySymbol]
    /\ file_pointer = 0

\* Flush the buffer to disk
FlushBuffer ==
    /\ dirty
    /\ file_content' = [i \in Offsets |->
        IF i >= lo /\ i < lo + BuffSz /\ i < length
        THEN buff[i - lo]
        ELSE file_content[i]]
    /\ diskPos' = lo + BuffSz
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr, lo, buff, file_pointer>>

\* Seek to a new position
Seek(newPos) ==
    /\ newPos \in Offsets
    /\ newPos <= length
    /\ IF newPos < lo \/ newPos >= lo + BuffSz
       THEN \* Need to flush and refill
            /\ IF dirty
               THEN file_content' = [i \in Offsets |->
                        IF i >= lo /\ i < lo + BuffSz /\ i < length
                        THEN buff[i - lo]
                        ELSE file_content[i]]
               ELSE file_content' = file_content
            /\ LET newLo == IF newPos + BuffSz <= MaxOffset + 1 
                            THEN newPos 
                            ELSE MaxOffset + 1 - BuffSz
               IN /\ lo' = newLo
                  /\ buff' = [i \in BuffOffsets |-> 
                        IF newLo + i < length
                        THEN file_content'[newLo + i]
                        ELSE ArbitrarySymbol]
            /\ dirty' = FALSE
            /\ diskPos' = newPos
       ELSE \* Position within buffer, no flush needed
            /\ UNCHANGED <<dirty, lo, buff, file_content, diskPos>>
    /\ curr' = newPos
    /\ UNCHANGED <<length, file_pointer>>

\* Set the length of the file
SetLength(newLen) ==
    /\ newLen \in 0..(MaxOffset + 1)
    /\ length' = newLen
    /\ curr' = IF curr > newLen THEN newLen ELSE curr
    /\ IF newLen < lo + BuffSz /\ dirty
       THEN /\ file_content' = [i \in Offsets |->
                IF i >= lo /\ i < lo + BuffSz /\ i < newLen
                THEN buff[i - lo]
                ELSE IF i < newLen THEN file_content[i] ELSE ArbitrarySymbol]
            /\ dirty' = FALSE
       ELSE /\ file_content' = [i \in Offsets |->
                IF i < newLen THEN file_content[i] ELSE ArbitrarySymbol]
            /\ UNCHANGED dirty
    /\ UNCHANGED <<lo, buff, diskPos, file_pointer>>

\* Read a single byte
Read1 ==
    /\ curr < length
    /\ curr >= lo
    /\ curr < lo + BuffSz
    /\ curr' = curr + 1
    /\ UNCHANGED <<dirty, length, lo, buff, diskPos, file_content, file_pointer>>

\* Write a single byte
Write1(sym) ==
    /\ sym \in Symbols
    /\ curr < lo + BuffSz
    /\ curr >= lo
    /\ buff' = [buff EXCEPT ![curr - lo] = sym]
    /\ dirty' = TRUE
    /\ length' = IF curr >= length THEN curr + 1 ELSE length
    /\ curr' = curr + 1
    /\ UNCHANGED <<lo, diskPos, file_content, file_pointer>>

\* Read multiple bytes (up to n bytes)
Read(n) ==
    /\ n \in 1..MaxOffset
    /\ curr < length
    /\ curr >= lo
    /\ curr < lo + BuffSz
    /\ LET bytesToRead == IF curr + n <= length 
                          THEN IF curr + n <= lo + BuffSz THEN n ELSE lo + BuffSz - curr
                          ELSE IF length <= lo + BuffSz THEN length - curr ELSE lo + BuffSz - curr
       IN curr' = curr + bytesToRead
    /\ UNCHANGED <<dirty, length, lo, buff, diskPos, file_content, file_pointer>>

\* Write multiple bytes (at most n bytes)
WriteAtMost(n, sym) ==
    /\ n \in 1..MaxOffset
    /\ sym \in Symbols
    /\ curr >= lo
    /\ curr < lo + BuffSz
    /\ LET bytesToWrite == IF curr + n <= lo + BuffSz THEN n ELSE lo + BuffSz - curr
       IN /\ buff' = [i \in BuffOffsets |->
                IF i >= curr - lo /\ i < curr - lo + bytesToWrite
                THEN sym
                ELSE buff[i]]
          /\ curr' = curr + bytesToWrite
          /\ length' = IF curr + bytesToWrite > length THEN curr + bytesToWrite ELSE length
    /\ dirty' = TRUE
    /\ UNCHANGED <<lo, diskPos, file_content, file_pointer>>

\* Next state relation
Next ==
    \/ FlushBuffer
    \/ \E pos \in Offsets : Seek(pos)
    \/ \E len \in 0..(MaxOffset + 1) : SetLength(len)
    \/ Read1
    \/ \E sym \in Symbols : Write1(sym)
    \/ \E n \in 1..MaxOffset : Read(n)
    \/ \E n \in 1..MaxOffset, sym \in Symbols : WriteAtMost(n, sym)

\* Specification with stuttering
Spec == Init /\ [][Next]_vars

\* RandomAccessFile refinement mapping
RAF_file_content == LogicalFileContent
RAF_file_pointer == curr

\* Safety: refinement of RandomAccessFile
Safety == 
    /\ TypeOK
    /\ Inv1
    /\ Inv3
    /\ Inv4
    /\ Inv5

\* Inv2 can always be restored by flush then seek
Inv2CanAlwaysBeRestored ==
    [](~Inv2 => 
        <>(\/ Inv2 
           \/ (dirty /\ ENABLED FlushBuffer)))

\* Correctness properties for individual actions
FlushBufferCorrect ==
    [][FlushBuffer => 
        /\ dirty
        /\ dirty' = FALSE
        /\ LogicalFileContent' = LogicalFileContent]_vars

SeekCorrect ==
    [][\E pos \in Offsets : Seek(pos) => curr' <= length']_vars

SeekEstablishesInv2 ==
    [][\E pos \in Offsets : Seek(pos) => (lo' <= curr' /\ curr' < lo' + BuffSz)]_vars

Write1Correct ==
    [][\E sym \in Symbols : Write1(sym) => 
        /\ curr' = curr + 1
        /\ dirty']_vars

Read1Correct ==
    [][Read1 => curr' = curr + 1]_vars

WriteAtMostCorrect ==
    [][\E n \in 1..MaxOffset, sym \in Symbols : WriteAtMost(n, sym) =>
        /\ curr' > curr
        /\ dirty']_vars

ReadCorrect ==
    [][\E n \in 1..MaxOffset : Read(n) => curr' > curr]_vars

=============================================================================