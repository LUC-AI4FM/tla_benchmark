---------------------------- MODULE BufferedRandomAccessFile ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxFileSize,      \* Maximum possible file size
    BufferSize,       \* Size of the in-memory buffer
    MaxDataValue      \* Maximum value for a byte (e.g., 255 for real bytes)

VARIABLES
    \* Underlying file state
    diskContents,     \* Function from offset to data value (the actual disk)
    diskLength,       \* Current length of the underlying file
    
    \* Buffer state
    buffer,           \* Function from buffer index to data value
    bufferStart,      \* Starting offset in file that buffer represents
    bufferValid,      \* How many bytes in buffer are valid (contain meaningful data)
    dirty,            \* Boolean: has buffer been modified since last flush?
    
    \* File position
    position,         \* Current logical position in the file
    
    \* Logical file state (for refinement checking)
    logicalContents,  \* The logical view of file contents
    logicalLength     \* The logical length of the file

vars == <<diskContents, diskLength, buffer, bufferStart, bufferValid, dirty, position, logicalContents, logicalLength>>

\* Helper: Range of valid positions
ValidPositions == 0..MaxFileSize

\* Helper: Range of valid data values
DataValues == 0..MaxDataValue

\* Helper: Check if a position is within the current buffer window
InBuffer(pos) ==
    /\ pos >= bufferStart
    /\ pos < bufferStart + bufferValid

\* Helper: Get the logical content at a position
LogicalRead(pos) ==
    IF InBuffer(pos)
    THEN buffer[pos - bufferStart]
    ELSE IF pos < diskLength
         THEN diskContents[pos]
         ELSE 0  \* Reading beyond file returns 0

\* Helper: Compute logical contents based on buffer and disk
ComputeLogicalContents ==
    [pos \in 0..(MaxFileSize-1) |->
        IF InBuffer(pos)
        THEN buffer[pos - bufferStart]
        ELSE IF pos < diskLength
             THEN diskContents[pos]
             ELSE 0]

\* Helper: Compute logical length
ComputeLogicalLength ==
    LET bufferEnd == bufferStart + bufferValid
    IN IF dirty
       THEN IF bufferEnd > diskLength THEN bufferEnd ELSE diskLength
       ELSE diskLength

\* Type invariant
TypeInvariant ==
    /\ diskContents \in [0..(MaxFileSize-1) -> DataValues]
    /\ diskLength \in 0..MaxFileSize
    /\ buffer \in [0..(BufferSize-1) -> DataValues]
    /\ bufferStart \in ValidPositions
    /\ bufferValid \in 0..BufferSize
    /\ dirty \in BOOLEAN
    /\ position \in ValidPositions
    /\ logicalContents \in [0..(MaxFileSize-1) -> DataValues]
    /\ logicalLength \in 0..MaxFileSize

\* Initial state
Init ==
    /\ diskContents = [pos \in 0..(MaxFileSize-1) |-> 0]
    /\ diskLength = 0
    /\ buffer = [idx \in 0..(BufferSize-1) |-> 0]
    /\ bufferStart = 0
    /\ bufferValid = 0
    /\ dirty = FALSE
    /\ position = 0
    /\ logicalContents = [pos \in 0..(MaxFileSize-1) |-> 0]
    /\ logicalLength = 0

\* Flush operation: write dirty buffer back to disk
Flush ==
    /\ dirty = TRUE
    /\ diskContents' = [pos \in 0..(MaxFileSize-1) |->
                         IF pos >= bufferStart /\ pos < bufferStart + bufferValid
                         THEN buffer[pos - bufferStart]
                         ELSE diskContents[pos]]
    /\ diskLength' = IF bufferStart + bufferValid > diskLength
                     THEN bufferStart + bufferValid
                     ELSE diskLength
    /\ dirty' = FALSE
    /\ UNCHANGED <<buffer, bufferStart, bufferValid, position>>
    /\ logicalContents' = ComputeLogicalContents'
    /\ logicalLength' = ComputeLogicalLength'

\* Seek operation: move to a new position
Seek(newPos) ==
    /\ newPos \in ValidPositions
    /\ newPos <= logicalLength  \* Can only seek within file bounds
    /\ position' = newPos
    /\ UNCHANGED <<diskContents, diskLength, buffer, bufferStart, bufferValid, dirty>>
    /\ UNCHANGED <<logicalContents, logicalLength>>

\* Refill buffer at a new starting position (internal operation after flush)
RefillBuffer(newStart) ==
    /\ dirty = FALSE
    /\ newStart \in ValidPositions
    /\ bufferStart' = newStart
    /\ bufferValid' = IF newStart + BufferSize <= diskLength
                      THEN BufferSize
                      ELSE IF newStart < diskLength
                           THEN diskLength - newStart
                           ELSE 0
    /\ buffer' = [idx \in 0..(BufferSize-1) |->
                   IF idx < bufferValid' /\ newStart + idx < diskLength
                   THEN diskContents[newStart + idx]
                   ELSE 0]
    /\ UNCHANGED <<diskContents, diskLength, dirty, position>>
    /\ logicalContents' = ComputeLogicalContents'
    /\ logicalLength' = ComputeLogicalLength'

\* Combined seek with potential buffer management
SeekWithBufferManagement(newPos) ==
    /\ newPos \in ValidPositions
    /\ newPos <= logicalLength
    /\ IF InBuffer(newPos) \/ bufferValid = 0
       THEN \* Position is in buffer or buffer empty, just move position
            /\ position' = newPos
            /\ UNCHANGED <<diskContents, diskLength, buffer, bufferStart, bufferValid, dirty>>
            /\ UNCHANGED <<logicalContents, logicalLength>>
       ELSE \* Need to potentially flush and refill
            IF dirty
            THEN \* Must flush first - this is handled by Flush action
                 FALSE
            ELSE \* Can refill buffer
                 LET newBufferStart == (newPos \div BufferSize) * BufferSize
                 IN /\ bufferStart' = newBufferStart
                    /\ bufferValid' = IF newBufferStart + BufferSize <= diskLength
                                      THEN BufferSize
                                      ELSE IF newBufferStart < diskLength
                                           THEN diskLength - newBufferStart
                                           ELSE 0
                    /\ buffer' = [idx \in 0..(BufferSize-1) |->
                                   IF newBufferStart + idx < diskLength
                                   THEN diskContents[newBufferStart + idx]
                                   ELSE 0]
                    /\ position' = newPos
                    /\ UNCHANGED <<diskContents, diskLength, dirty>>
                    /\ logicalContents' = ComputeLogicalContents'
                    /\ logicalLength' = ComputeLogicalLength'

\* Read operation (simplified - reads one byte)
Read ==
    /\ position < logicalLength
    /\ InBuffer(position)
    /\ position' = position + 1
    /\ UNCHANGED <<diskContents, diskLength, buffer, bufferStart, bufferValid, dirty>>
    /\ UNCHANGED <<logicalContents, logicalLength>>

\* Write operation (simplified - writes one byte)
Write(value) ==
    /\ value \in DataValues
    /\ position < MaxFileSize
    /\ \/ InBuffer(position)
       \/ /\ ~dirty
          /\ bufferValid = 0  \* Empty buffer, can start fresh
    /\ IF InBuffer(position)
       THEN \* Write to existing buffer position
            /\ buffer' = [buffer EXCEPT ![position - bufferStart] = value]
            /\ bufferValid' = IF position - bufferStart >= bufferValid
                              THEN position - bufferStart + 1
                              ELSE bufferValid
            /\ UNCHANGED <<bufferStart>>
       ELSE \* Start fresh buffer at position
            /\ bufferStart' = position
            /\ buffer' = [idx \in 0..(BufferSize-1) |-> IF idx = 0 THEN value ELSE 0]
            /\ bufferValid' = 1
    /\ dirty' = TRUE
    /\ position' = position + 1
    /\ UNCHANGED <<diskContents, diskLength>>
    /\ logicalContents' = [logicalContents EXCEPT ![position] = value]
    /\ logicalLength' = IF position >= logicalLength THEN position + 1 ELSE logicalLength

\* Set length operation (truncate or extend)
SetLength(newLen) ==
    /\ newLen \in 0..MaxFileSize
    /\ dirty = FALSE  \* Must flush before truncating
    /\ diskLength' = newLen
    /\ diskContents' = [pos \in 0..(MaxFileSize-1) |->
                         IF pos < newLen THEN diskContents[pos] ELSE 0]
    /\ \* Invalidate buffer if it extends beyond new length
       IF bufferStart >= newLen
       THEN /\ bufferValid' = 0
            /\ bufferStart' = 0
            /\ buffer' = [idx \in 0..(BufferSize-1) |-> 0]
       ELSE IF bufferStart + bufferValid > newLen
            THEN /\ bufferValid' = newLen - bufferStart
                 /\ UNCHANGED <<bufferStart, buffer>>
            ELSE UNCHANGED <<buffer, bufferStart, bufferValid>>
    /\ position' = IF position > newLen THEN newLen ELSE position
    /\ UNCHANGED <<dirty>>
    /\ logicalContents' = [pos \in 0..(MaxFileSize-1) |->
                            IF pos < newLen THEN logicalContents[pos] ELSE 0]
    /\ logicalLength' = newLen

\* Next state relation
Next ==
    \/ Flush
    \/ \E pos \in ValidPositions : SeekWithBufferManagement(pos)
    \/ Read
    \/ \E v \in DataValues : Write(v)
    \/ \E len \in 0..MaxFileSize : SetLength(len)
    \/ \E start \in ValidPositions : RefillBuffer(start)

\* Fairness: Flush should eventually happen if buffer is dirty
Fairness == WF_vars(Flush)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================