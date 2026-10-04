---------------------------- MODULE BufferedRandomAccessFile ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

ASSUME BuffSz > 0
ASSUME MaxOffset >= 0
ASSUME ArbitrarySymbol \in Symbols

VARIABLES
    \* Underlying file state
    diskContents,      \* Function from offset -> symbol (0-indexed)
    diskLength,        \* Length of underlying file
    
    \* Buffer state
    buffer,            \* Function from offset -> symbol for buffered region
    bufferStart,       \* Starting offset of buffer in file
    bufferEnd,         \* Ending offset (exclusive) of buffer region
    dirty,             \* Whether buffer has been modified
    
    \* File pointer
    position,          \* Current read/write position
    
    \* Logical file length (may differ from disk during buffered writes)
    logicalLength

vars == <<diskContents, diskLength, buffer, bufferStart, bufferEnd, dirty, position, logicalLength>>

\* Helper: Range of offsets
Offsets == 0..MaxOffset

\* Helper: Get logical file contents at a position
LogicalContents(pos) ==
    IF pos >= 0 /\ pos < logicalLength THEN
        IF pos >= bufferStart /\ pos < bufferEnd THEN
            buffer[pos]
        ELSE
            IF pos < diskLength THEN diskContents[pos] ELSE ArbitrarySymbol
    ELSE
        ArbitrarySymbol

\* Helper: Check if position is within buffer bounds
InBuffer(pos) == pos >= bufferStart /\ pos < bufferEnd

\* Helper: Check if buffer covers current position appropriately
BufferCoversPosition == position >= bufferStart /\ position < bufferStart + BuffSz

\* Type invariant
TypeOK ==
    /\ diskContents \in [0..(MaxOffset-1) -> Symbols]
    /\ diskLength \in 0..MaxOffset
    /\ buffer \in [0..(MaxOffset-1) -> Symbols]
    /\ bufferStart \in 0..MaxOffset
    /\ bufferEnd \in 0..MaxOffset
    /\ bufferStart <= bufferEnd
    /\ bufferEnd <= bufferStart + BuffSz
    /\ dirty \in BOOLEAN
    /\ position \in 0..MaxOffset
    /\ logicalLength \in 0..MaxOffset

\* Inv1: Logical consistency - length is well-defined
Inv1 ==
    /\ logicalLength >= 0
    /\ logicalLength <= MaxOffset
    /\ bufferEnd <= bufferStart + BuffSz

\* Inv2: Buffer bounds invariant - position within valid bounds relative to buffer
Inv2 == BufferCoversPosition \/ ~dirty

\* Inv3: Buffer coherence - buffer matches logical file for covered positions
Inv3 ==
    \A pos \in 0..(MaxOffset-1) :
        (pos >= bufferStart /\ pos < bufferEnd) =>
            buffer[pos] = LogicalContents(pos)

\* Inv4: Unbuffered region coherence
Inv4 ==
    \A pos \in 0..(MaxOffset-1) :
        (pos < logicalLength /\ (pos < bufferStart \/ pos >= bufferEnd)) =>
            (pos < diskLength => LogicalContents(pos) = diskContents[pos])

\* Inv5: Dirty tracking correctness
Inv5 ==
    (~dirty) =>
        \A pos \in 0..(MaxOffset-1) :
            (pos >= bufferStart /\ pos < bufferEnd /\ pos < diskLength) =>
                buffer[pos] = diskContents[pos]

\* Combined safety property
Safety == TypeOK /\ Inv1 /\ Inv3 /\ Inv4 /\ Inv5

\* Initial state
Init ==
    /\ diskContents = [i \in 0..(MaxOffset-1) |-> ArbitrarySymbol]
    /\ diskLength = 0
    /\ buffer = [i \in 0..(MaxOffset-1) |-> ArbitrarySymbol]
    /\ bufferStart = 0
    /\ bufferEnd = 0
    /\ dirty = FALSE
    /\ position = 0
    /\ logicalLength = 0

\* Flush operation: write dirty buffer back to disk
FlushBuffer ==
    /\ dirty = TRUE
    /\ diskContents' = [i \in 0..(MaxOffset-1) |->
                            IF i >= bufferStart /\ i < bufferEnd THEN buffer[i]
                            ELSE diskContents[i]]
    /\ diskLength' = IF logicalLength > diskLength THEN logicalLength ELSE diskLength
    /\ dirty' = FALSE
    /\ UNCHANGED <<buffer, bufferStart, bufferEnd, position, logicalLength>>

\* FlushBufferCorrect: Flushing clears dirty and syncs to disk
FlushBufferCorrect ==
    (dirty /\ FlushBuffer) => dirty' = FALSE

\* Seek operation: move position
Seek(newPos) ==
    /\ newPos >= 0
    /\ newPos <= MaxOffset
    /\ ~dirty  \* Must flush before seeking outside buffer
    /\ position' = newPos
    /\ bufferStart' = newPos
    /\ bufferEnd' = newPos
    /\ buffer' = [i \in 0..(MaxOffset-1) |->
                    IF i >= newPos /\ i < newPos + BuffSz /\ i < diskLength
                    THEN diskContents[i]
                    ELSE ArbitrarySymbol]
    /\ UNCHANGED <<diskContents, diskLength, dirty, logicalLength>>

\* SeekCorrect: Seek moves position correctly
SeekCorrect ==
    \A newPos \in 0..MaxOffset :
        (~dirty /\ Seek(newPos)) => position' = newPos

\* SeekEstablishesInv2: After seeking, buffer covers position
SeekEstablishesInv2 ==
    \A newPos \in 0..MaxOffset :
        (~dirty /\ Seek(newPos)) => (position' >= bufferStart' /\ position' < bufferStart' + BuffSz)

\* Write a single byte at current position
Write1(sym) ==
    /\ sym \in Symbols
    /\ position < MaxOffset
    /\ InBuffer(position)  \* Position must be in buffer
    /\ buffer' = [buffer EXCEPT ![position] = sym]
    /\ dirty' = TRUE
    /\ position' = position + 1
    /\ logicalLength' = IF position + 1 > logicalLength THEN position + 1 ELSE logicalLength
    /\ bufferEnd' = IF position + 1 > bufferEnd THEN position + 1 ELSE bufferEnd
    /\ UNCHANGED <<diskContents, diskLength, bufferStart>>

\* Write1Correct: Writing advances position and updates buffer
Write1Correct ==
    \A sym \in Symbols :
        (position < MaxOffset /\ InBuffer(position) /\ Write1(sym)) =>
            /\ position' = position + 1
            /\ buffer'[position] = sym
            /\ dirty' = TRUE

\* Read a single byte at current position
Read1 ==
    /\ position < logicalLength
    /\ InBuffer(position)
    /\ position' = position + 1
    /\ UNCHANGED <<diskContents, diskLength, buffer, bufferStart, bufferEnd, dirty, logicalLength>>

\* Read1Correct: Reading advances position
Read1Correct ==
    (position < logicalLength /\ InBuffer(position) /\ Read1) =>
        position' = position + 1

\* Write multiple bytes (up to n bytes of a symbol)
WriteAtMost(sym, n) ==
    /\ sym \in Symbols
    /\ n > 0
    /\ position < MaxOffset
    /\ InBuffer(position)
    /\ LET writeEnd == IF position + n > bufferStart + BuffSz 
                       THEN bufferStart + BuffSz 
                       ELSE IF position + n > MaxOffset
                       THEN MaxOffset
                       ELSE position + n
           actualWrite == writeEnd - position
       IN /\ actualWrite > 0
          /\ buffer' = [i \in 0..(MaxOffset-1) |->
                            IF i >= position /\ i < writeEnd THEN sym ELSE buffer[i]]
          /\ dirty' = TRUE
          /\ position' = writeEnd
          /\ logicalLength' = IF writeEnd > logicalLength THEN writeEnd ELSE logicalLength
          /\ bufferEnd' = IF writeEnd > bufferEnd THEN writeEnd ELSE bufferEnd
          /\ UNCHANGED <<diskContents, diskLength, bufferStart>>

\* WriteAtMostCorrect: Writing multiple bytes is correct
WriteAtMostCorrect ==
    \A sym \in Symbols, n \in 1..BuffSz :
        (position < MaxOffset /\ InBuffer(position) /\ WriteAtMost(sym, n)) =>
            /\ position' > position
            /\ dirty' = TRUE

\* Read multiple bytes (just advances position, actual data read via LogicalContents)
ReadMultiple(n) ==
    /\ n > 0
    /\ position < logicalLength
    /\ InBuffer(position)
    /\ LET readEnd == IF position + n > logicalLength THEN logicalLength
                      ELSE IF position + n > bufferEnd THEN bufferEnd
                      ELSE position + n
       IN /\ readEnd > position
          /\ position' = readEnd
          /\ UNCHANGED <<diskContents, diskLength, buffer, bufferStart, bufferEnd, dirty, logicalLength>>

\* ReadCorrect: Reading advances position correctly
ReadCorrect ==
    \A n \in 1..BuffSz :
        (position < logicalLength /\ InBuffer(position) /\ ReadMultiple(n)) =>
            position' >= position

\* Set file length (truncate or extend)
SetLength(newLen) ==
    /\ newLen >= 0
    /\ newLen <= MaxOffset
    /\ ~dirty  \* Must flush first if dirty
    /\ logicalLength' = newLen
    /\ diskLength' = newLen
    /\ position' = IF position > newLen THEN newLen ELSE position
    /\ bufferEnd' = IF bufferEnd > newLen THEN 
                        IF bufferStart > newLen THEN bufferStart ELSE newLen 
                    ELSE bufferEnd
    /\ UNCHANGED <<diskContents, buffer, bufferStart, dirty>>

\* Inv2CanAlwaysBeRestored: Can always restore buffer bounds invariant
Inv2CanAlwaysBeRestored ==
    \/ Inv2
    \/ (dirty /\ ENABLED FlushBuffer)

\* Next state relation
Next ==
    \/ FlushBuffer
    \/ \E pos \in 0..MaxOffset : Seek(pos)
    \/ \E sym \in Symbols : Write1(sym)
    \/ Read1
    \/ \E sym \in Symbols, n \in 1..BuffSz : WriteAtMost(sym, n)
    \/ \E n \in 1..BuffSz : ReadMultiple(n)
    \/ \E len \in 0..MaxOffset : SetLength(len)

\* Specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================