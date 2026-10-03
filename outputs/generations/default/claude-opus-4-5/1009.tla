---------------------------- MODULE BufferedRandomAccessFile ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxFileSize,        \* Maximum file size for model checking
    BufferSize,         \* Size of the in-memory buffer
    MaxSeekPos,         \* Maximum seek position
    DataValues,         \* Set of possible data values (e.g., 0..255 for bytes)
    ArbitrarySymbol     \* Symbol representing uninitialized/unknown file content

ASSUME BufferSize > 0
ASSUME MaxFileSize >= 0
ASSUME MaxSeekPos >= 0

VARIABLES
    \* Concrete buffered file state
    filePointer,        \* Current position in the logical file
    buffer,             \* In-memory buffer (sequence of data values)
    bufferStart,        \* File position where buffer starts
    bufferEnd,          \* File position where buffer ends (exclusive)
    bufferModified,     \* Whether buffer has been modified (dirty flag)
    diskContent,        \* On-disk file content (function from position to value)
    diskLength,         \* Length of on-disk file
    logicalLength,      \* Logical file length (may differ from disk during buffering)
    
    \* Abstract RandomAccessFile state (for refinement)
    absFilePointer,     \* Abstract file pointer
    absContent,         \* Abstract file content
    absLength,          \* Abstract file length
    
    \* Operation tracking
    lastOp              \* Last operation performed (for refinement checking)

vars == <<filePointer, buffer, bufferStart, bufferEnd, bufferModified,
          diskContent, diskLength, logicalLength,
          absFilePointer, absContent, absLength, lastOp>>

concreteVars == <<filePointer, buffer, bufferStart, bufferEnd, bufferModified,
                  diskContent, diskLength, logicalLength>>

abstractVars == <<absFilePointer, absContent, absLength>>

-----------------------------------------------------------------------------
\* Helper Functions

\* Get logical content at position (buffer takes precedence over disk)
LogicalContentAt(pos) ==
    IF pos >= 0 /\ pos < logicalLength THEN
        IF pos >= bufferStart /\ pos < bufferEnd THEN
            buffer[pos - bufferStart + 1]
        ELSE IF pos < diskLength THEN
            diskContent[pos]
        ELSE
            ArbitrarySymbol
    ELSE
        ArbitrarySymbol

\* Check if position is within buffer bounds
InBuffer(pos) ==
    pos >= bufferStart /\ pos < bufferEnd

\* Buffer length
BufferLength == bufferEnd - bufferStart

\* Valid data value
ValidData(d) == d \in DataValues \/ d = ArbitrarySymbol

\* Range of positions
Range(start, end) == {i \in 0..(end-1) : i >= start}

-----------------------------------------------------------------------------
\* Initial State

Init ==
    /\ filePointer = 0
    /\ buffer = <<>>
    /\ bufferStart = 0
    /\ bufferEnd = 0
    /\ bufferModified = FALSE
    /\ diskContent = [i \in {} |-> ArbitrarySymbol]
    /\ diskLength = 0
    /\ logicalLength = 0
    /\ absFilePointer = 0
    /\ absContent = [i \in {} |-> ArbitrarySymbol]
    /\ absLength = 0
    /\ lastOp = "init"

-----------------------------------------------------------------------------
\* Internal Operations

\* Flush buffer to disk
FlushBuffer ==
    /\ bufferModified = TRUE
    /\ BufferLength > 0
    /\ LET newDiskContent == 
           [i \in 0..(logicalLength-1) |->
               IF i >= bufferStart /\ i < bufferEnd THEN
                   buffer[i - bufferStart + 1]
               ELSE IF i < diskLength THEN
                   diskContent[i]
               ELSE
                   ArbitrarySymbol]
       IN
       /\ diskContent' = newDiskContent
       /\ diskLength' = logicalLength
       /\ bufferModified' = FALSE
       /\ UNCHANGED <<filePointer, buffer, bufferStart, bufferEnd, logicalLength>>

\* Fill buffer from disk at given position
FillBuffer(pos) ==
    LET start == pos
        end == IF pos + BufferSize > logicalLength 
               THEN logicalLength 
               ELSE pos + BufferSize
        newBuffer == [i \in 1..(end - start) |->
                        IF start + i - 1 < diskLength THEN
                            diskContent[start + i - 1]
                        ELSE
                            ArbitrarySymbol]
    IN
    /\ buffer' = newBuffer
    /\ bufferStart' = start
    /\ bufferEnd' = end
    /\ bufferModified' = FALSE

-----------------------------------------------------------------------------
\* Seek Operation

Seek(newPos) ==
    /\ newPos >= 0
    /\ newPos <= MaxSeekPos
    /\ filePointer' = newPos
    /\ absFilePointer' = newPos
    /\ lastOp' = "seek"
    /\ UNCHANGED <<buffer, bufferStart, bufferEnd, bufferModified,
                   diskContent, diskLength, logicalLength,
                   absContent, absLength>>

-----------------------------------------------------------------------------
\* Read Operation

Read ==
    /\ filePointer < logicalLength
    /\ filePointer >= 0
    /\ LET data == LogicalContentAt(filePointer)
       IN
       \* If position not in buffer, we need to refill (simplified: assume in buffer or disk)
       /\ IF InBuffer(filePointer) THEN
              UNCHANGED <<buffer, bufferStart, bufferEnd, bufferModified,
                         diskContent, diskLength>>
          ELSE
              \* Flush if modified, then fill buffer
              /\ IF bufferModified THEN
                     /\ LET newDiskContent == 
                            [i \in 0..(logicalLength-1) |->
                                IF i >= bufferStart /\ i < bufferEnd THEN
                                    buffer[i - bufferStart + 1]
                                ELSE IF i < diskLength THEN
                                    diskContent[i]
                                ELSE
                                    ArbitrarySymbol]
                        IN diskContent' = newDiskContent
                     /\ diskLength' = logicalLength
                 ELSE
                     UNCHANGED <<diskContent, diskLength>>
              /\ LET start == filePointer
                     end == IF filePointer + BufferSize > logicalLength 
                            THEN logicalLength 
                            ELSE filePointer + BufferSize
                     newBuffer == [i \in 1..(end - start) |->
                                     IF start + i - 1 < diskLength THEN
                                         diskContent[start + i - 1]
                                     ELSE
                                         ArbitrarySymbol]
                 IN
                 /\ buffer' = newBuffer
                 /\ bufferStart' = start
                 /\ bufferEnd' = end
              /\ bufferModified' = FALSE
    /\ filePointer' = filePointer + 1
    /\ absFilePointer' = absFilePointer + 1
    /\ lastOp' = "read"
    /\ UNCHANGED <<logicalLength, absContent, absLength>>

\* Simplified Read that assumes buffer is properly positioned
ReadSimple ==
    /\ filePointer >= 0
    /\ filePointer < logicalLength
    /\ filePointer' = filePointer + 1
    /\ absFilePointer' = absFilePointer + 1
    /\ lastOp' = "read"
    /\ UNCHANGED <<buffer, bufferStart, bufferEnd, bufferModified,
                   diskContent, diskLength, logicalLength,
                   absContent, absLength>>

-----------------------------------------------------------------------------
\* Write Operation

Write(data) ==
    /\ ValidData(data)
    /\ filePointer >= 0
    /\ filePointer < MaxFileSize
    /\ LET newLogicalLength == IF filePointer >= logicalLength 
                               THEN filePointer + 1 
                               ELSE logicalLength
           newAbsLength == IF absFilePointer >= absLength
                          THEN absFilePointer + 1
                          ELSE absLength
       IN
       \* Check if we can write to current buffer
       /\ IF InBuffer(filePointer) THEN
              /\ buffer' = [buffer EXCEPT ![filePointer - bufferStart + 1] = data]
              /\ bufferModified' = TRUE
              /\ UNCHANGED <<bufferStart, bufferEnd, diskContent, diskLength>>
          ELSE IF BufferLength < BufferSize /\ 
                  (BufferLength = 0 \/ filePointer = bufferEnd) THEN
              \* Extend buffer
              /\ buffer' = Append(buffer, data)
              /\ bufferEnd' = bufferEnd + 1
              /\ bufferModified' = TRUE
              /\ IF BufferLength = 0 THEN bufferStart' = filePointer
                 ELSE UNCHANGED bufferStart
              /\ UNCHANGED <<diskContent, diskLength>>
          ELSE
              \* Need to flush and start new buffer
              /\ IF bufferModified /\ BufferLength > 0 THEN
                     LET newDiskContent == 
                         [i \in 0..(newLogicalLength-1) |->
                             IF i >= bufferStart /\ i < bufferEnd THEN
                                 buffer[i - bufferStart + 1]
                             ELSE IF i < diskLength THEN
                                 diskContent[i]
                             ELSE
                                 ArbitrarySymbol]
                     IN diskContent' = newDiskContent
                 ELSE
                     UNCHANGED diskContent
              /\ diskLength' = IF bufferModified THEN newLogicalLength ELSE diskLength
              /\ buffer' = <<data>>
              /\ bufferStart' = filePointer
              /\ bufferEnd' = filePointer + 1
              /\ bufferModified' = TRUE
       /\ filePointer' = filePointer + 1
       /\ logicalLength' = newLogicalLength
       /\ absFilePointer' = absFilePointer + 1
       /\ absContent' = [i \in 0..(newAbsLength-1) |->
                           IF i = absFilePointer THEN data
                           ELSE IF i < absLength THEN absContent[i]
                           ELSE ArbitrarySymbol]
       /\ absLength' = newAbsLength
       /\ lastOp' = "write"

\* Simplified write for model checking tractability
WriteSimple(data) ==
    /\ ValidData(data)
    /\ filePointer >= 0
    /\ filePointer < MaxFileSize
    /\ LET newLogicalLength == IF filePointer >= logicalLength 
                               THEN filePointer + 1 
                               ELSE logicalLength
           newAbsLength == IF absFilePointer >= absLength
                          THEN absFilePointer + 1
                          ELSE absLength
       IN
       /\ logicalLength' = newLogicalLength
       /\ filePointer' = filePointer + 1
       /\ bufferModified' = TRUE
       /\ absFilePointer' = absFilePointer + 1
       /\ absContent' = [i \in 0..(newAbsLength-1) |->
                           IF i = absFilePointer THEN data
                           ELSE IF i < absLength THEN absContent[i]
                           ELSE ArbitrarySymbol]
       /\ absLength' = newAbsLength
       /\ lastOp' = "write"
       /\ UNCHANGED <<buffer, bufferStart, bufferEnd, diskContent, diskLength>>

-----------------------------------------------------------------------------
\* Flush Operation

Flush ==
    /\ IF bufferModified /\ BufferLength > 0 THEN
           LET newDiskContent == 
               [i \in 0..(logicalLength-1) |->
                   IF i >= bufferStart /\ i < bufferEnd THEN
                       buffer[i - bufferStart + 1]
                   ELSE IF i < diskLength THEN
                       diskContent[i]
                   ELSE
                       ArbitrarySymbol]
           IN
           /\ diskContent' = newDiskContent
           /\ diskLength' = logicalLength
           /\ bufferModified' = FALSE
       ELSE
           UNCHANGED <<diskContent, diskLength, bufferModified>>
    /\ lastOp' = "flush"
    /\ UNCHANGED <<filePointer, buffer, bufferStart, bufferEnd, logicalLength,
                   absFilePointer, absContent, absLength>>

-----------------------------------------------------------------------------
\* SetLength Operation

SetLength(newLength) ==
    /\ newLength >= 0
    /\ newLength <= MaxFileSize
    /\ logicalLength' = newLength
    /\ absLength' = newLength
    \* Truncate buffer if necessary
    /\ IF bufferEnd > newLength THEN
           /\ bufferEnd' = IF bufferStart >= newLength THEN bufferStart ELSE newLength
           /\ buffer' = IF bufferStart >= newLength THEN <<>>
                        ELSE SubSeq(buffer, 1, newLength - bufferStart)
       ELSE
           UNCHANGED <<buffer, bufferEnd>>
    \* Truncate disk if necessary
    /\ IF diskLength > newLength THEN
           /\ diskContent' = [i \in 0..(newLength-1) |-> 
                               IF i < diskLength THEN diskContent[i] 
                               ELSE ArbitrarySymbol]
           /\ diskLength' = newLength
       ELSE
           UNCHANGED <<diskContent, diskLength>>
    /\ absContent' = [i \in 0..(newLength-1) |->
                        IF i < absLength THEN absContent[i]
                        ELSE ArbitrarySymbol]
    \* Adjust file pointer if beyond new length
    /\ filePointer' = IF filePointer > newLength THEN newLength ELSE filePointer
    /\ absFilePointer' = IF absFilePointer > newLength THEN newLength ELSE absFilePointer
    /\ lastOp' = "setLength"
    /\ UNCHANGED <<bufferStart, bufferModified>>

-----------------------------------------------------------------------------
\* Next State Relation

Next ==
    \/ \E pos \in 0..MaxSeekPos : Seek(pos)
    \/ ReadSimple
    \/ \E d \in DataValues : WriteSimple(d)
    \/ Flush
    \/ \E len \in 0..MaxFileSize : SetLength(len)

-----------------------------------------------------------------------------
\* Specification with Fairness

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety Invariants

\* Type invariant
TypeInvariant ==
    /\ filePointer \in Int
    /\ filePointer >= 0
    /\ bufferStart \in Int
    /\ bufferStart >= 0
    /\ bufferEnd \in Int
    /\ bufferEnd >= 0
    /\ bufferModified \in BOOLEAN
    /\ diskLength \in Int
    /\ diskLength >= 0
    /\ logicalLength \in Int
    /\ logicalLength >= 0
    /\ absFilePointer \in Int
    /\ absFilePointer >= 0
    /\ absLength \in Int
    /\ absLength >= 0

\* Buffer bounds invariant
BufferBoundsInvariant ==
    /\ bufferStart <= bufferEnd
    /\ bufferEnd <= logicalLength \/ bufferEnd = bufferStart
    /\ BufferLength <= BufferSize

\* Buffer content consistency
BufferConsistencyInvariant ==
    Len(buffer) = BufferLength

\* Disk content consistency
DiskConsistencyInvariant ==
    \A i \in DOMAIN diskContent : i >= 0 /\ i < diskLength

\* File pointer bounds
FilePointerInvariant ==
    filePointer >= 0

\* Logical length consistency
LogicalLengthInvariant ==
    logicalLength >= diskLength \/ ~bufferModified

\* Abstract-Concrete pointer consistency
PointerRefinementInvariant ==
    filePointer = absFilePointer

\* Abstract-Concrete length consistency  
LengthRefinementInvariant ==
    logicalLength = absLength

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ BufferBoundsInvariant
    /\ BufferConsistencyInvariant
    /\ FilePointerInvariant
    /\ PointerRefinementInvariant
    /\ LengthRefinementInvariant

-----------------------------------------------------------------------------
\* Refinement Properties

\* Abstract RandomAccessFile specification
AbstractTypeOK ==
    /\ absFilePointer >= 0
    /\ absLength >= 0

\* Refinement mapping: concrete state refines abstract state
RefinementMapping ==
    /\ filePointer = absFilePointer
    /\ logicalLength = absLength

\* Content refinement (logical content matches abstract content)
ContentRefinement ==
    \A i \in 0..(absLength-1) :
        i < absLength => 
            (LogicalContentAt(i) = absContent[i] \/ 
             LogicalContentAt(i) = ArbitrarySymbol \/
             absContent[i] = ArbitrarySymbol)

-----------------------------------------------------------------------------
\* Liveness Properties

\* Eventually flush if buffer is modified
EventuallyFlush == 
    bufferModified ~> ~bufferModified

\* Progress: some operation eventually happens
Progress == 
    <>(\E pos \in 0..MaxSeekPos : ENABLED Seek(pos))

-----------------------------------------------------------------------------
\* TLC Configuration

\* Symmetry set for data values (if applicable)
DataSymmetry == Permutations(DataValues)

\* State constraint for bounded model checking
StateConstraint ==
    /\ filePointer <= MaxSeekPos
    /\ logicalLength <= MaxFileSize
    /\ diskLength <= MaxFileSize
    /\ absLength <= MaxFileSize
    /\ BufferLength <= BufferSize

\* Alias for debugging
Alias == [
    fp |-> filePointer,
    buf |-> buffer,
    bufStart |-> bufferStart,
    bufEnd |-> bufferEnd,
    bufMod |-> bufferModified,
    diskLen |-> diskLength,
    logLen |-> logicalLength,
    absFp |-> absFilePointer,
    absLen |-> absLength,
    op |-> lastOp
]

=============================================================================