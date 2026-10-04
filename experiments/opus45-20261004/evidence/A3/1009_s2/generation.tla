---------------------------- MODULE BufferedRandomAccessFile ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxFileSize,        \* Maximum size of the file
    BufferSize,         \* Size of the in-memory buffer
    MaxSeekPos,         \* Maximum seek position
    DataValues,         \* Set of possible data values
    ArbitrarySymbol     \* Represents underspecified/unknown file contents

ASSUME MaxFileSize \in Nat /\ MaxFileSize > 0
ASSUME BufferSize \in Nat /\ BufferSize > 0
ASSUME MaxSeekPos \in Nat /\ MaxSeekPos >= MaxFileSize
ASSUME ArbitrarySymbol \notin DataValues

AllSymbols == DataValues \cup {ArbitrarySymbol}

VARIABLES
    \* Concrete buffered file state
    diskFile,           \* The actual on-disk file contents (sequence)
    diskFileLength,     \* Length of on-disk file
    buffer,             \* In-memory buffer (function from offset to value)
    bufferStart,        \* File offset where buffer starts
    bufferEnd,          \* File offset where buffer valid data ends
    bufferModified,     \* Whether buffer has unflushed modifications
    filePointer,        \* Current logical file pointer position
    logicalLength,      \* Logical length of file (may differ from disk during writes)
    
    \* Abstract RandomAccessFile state (for refinement)
    absFile,            \* Abstract file contents
    absFilePointer,     \* Abstract file pointer
    absFileLength,      \* Abstract file length
    
    \* Operation tracking
    pc                  \* Program counter for operations

vars == <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd, 
          bufferModified, filePointer, logicalLength, 
          absFile, absFilePointer, absFileLength, pc>>

concreteVars == <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                  bufferModified, filePointer, logicalLength>>

abstractVars == <<absFile, absFilePointer, absFileLength>>

--------------------------------------------------------------------------------
\* Helper functions for array/file utilities

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

\* Create a sequence of length n filled with ArbitrarySymbol
ArbitrarySeq(n) == [i \in 1..n |-> ArbitrarySymbol]

\* Extend a sequence to length n with ArbitrarySymbol if needed
ExtendSeq(s, n) == 
    IF Len(s) >= n THEN s
    ELSE s \o ArbitrarySeq(n - Len(s))

\* Update sequence at position pos (1-indexed) with value val
UpdateSeq(s, pos, val) ==
    [i \in 1..Len(s) |-> IF i = pos THEN val ELSE s[i]]

\* Get logical file content at position (0-indexed), accounting for buffer
LogicalContentAt(pos) ==
    IF pos < 0 \/ pos >= logicalLength THEN ArbitrarySymbol
    ELSE IF pos >= bufferStart /\ pos < bufferEnd THEN
        buffer[pos - bufferStart]
    ELSE IF pos < diskFileLength THEN
        diskFile[pos + 1]  \* Convert to 1-indexed
    ELSE ArbitrarySymbol

--------------------------------------------------------------------------------
\* Type invariant

TypeOK ==
    /\ diskFile \in Seq(AllSymbols)
    /\ diskFileLength \in 0..MaxFileSize
    /\ diskFileLength = Len(diskFile)
    /\ buffer \in [0..(BufferSize-1) -> AllSymbols]
    /\ bufferStart \in 0..MaxSeekPos
    /\ bufferEnd \in 0..MaxSeekPos
    /\ bufferStart <= bufferEnd
    /\ bufferEnd - bufferStart <= BufferSize
    /\ bufferModified \in BOOLEAN
    /\ filePointer \in 0..MaxSeekPos
    /\ logicalLength \in 0..MaxFileSize
    /\ absFile \in Seq(AllSymbols)
    /\ absFilePointer \in 0..MaxSeekPos
    /\ absFileLength \in 0..MaxFileSize
    /\ absFileLength = Len(absFile)
    /\ pc \in {"idle", "seek", "read", "write", "flush", "setLength"}

--------------------------------------------------------------------------------
\* Buffer invariants - how buffer relates to logical and disk contents

\* Buffer contains valid data for positions within its range
BufferValidInvariant ==
    \A i \in 0..(bufferEnd - bufferStart - 1) :
        bufferStart + i < logicalLength =>
            buffer[i] = LogicalContentAt(bufferStart + i)

\* If buffer is not modified, buffer contents match disk for overlapping region
BufferCleanMatchesDisk ==
    ~bufferModified =>
        \A i \in 0..(bufferEnd - bufferStart - 1) :
            bufferStart + i < diskFileLength =>
                buffer[i] = diskFile[bufferStart + i + 1]

\* Logical length is at least disk length when buffer has modifications beyond disk
LogicalLengthInvariant ==
    logicalLength >= diskFileLength \/ ~bufferModified

\* Buffer boundaries are consistent
BufferBoundaryInvariant ==
    /\ bufferStart <= bufferEnd
    /\ bufferEnd <= bufferStart + BufferSize
    /\ (bufferModified => bufferEnd > bufferStart)

\* File pointer is within valid range
FilePointerInvariant ==
    filePointer <= MaxSeekPos

--------------------------------------------------------------------------------
\* Refinement mapping - concrete state maps to abstract state

RefinementMapping ==
    /\ absFileLength = logicalLength
    /\ absFilePointer = filePointer
    /\ \A i \in 1..logicalLength :
        absFile[i] = LogicalContentAt(i - 1)

--------------------------------------------------------------------------------
\* Initial state

InitBuffer == [i \in 0..(BufferSize-1) |-> ArbitrarySymbol]

Init ==
    /\ diskFile = <<>>
    /\ diskFileLength = 0
    /\ buffer = InitBuffer
    /\ bufferStart = 0
    /\ bufferEnd = 0
    /\ bufferModified = FALSE
    /\ filePointer = 0
    /\ logicalLength = 0
    /\ absFile = <<>>
    /\ absFilePointer = 0
    /\ absFileLength = 0
    /\ pc = "idle"

--------------------------------------------------------------------------------
\* Flush operation - writes modified buffer to disk

FlushBuffer ==
    IF bufferModified THEN
        LET 
            newDiskFile == 
                LET extended == ExtendSeq(diskFile, bufferEnd) IN
                [i \in 1..Max(diskFileLength, bufferEnd) |->
                    IF i > bufferStart /\ i <= bufferEnd 
                    THEN buffer[i - bufferStart - 1]
                    ELSE IF i <= Len(extended) THEN extended[i]
                    ELSE ArbitrarySymbol]
        IN
        /\ diskFile' = newDiskFile
        /\ diskFileLength' = Len(newDiskFile)
        /\ bufferModified' = FALSE
    ELSE
        /\ UNCHANGED <<diskFile, diskFileLength, bufferModified>>

DoFlush ==
    /\ pc = "idle"
    /\ pc' = "flush"
    /\ FlushBuffer
    /\ UNCHANGED <<buffer, bufferStart, bufferEnd, filePointer, logicalLength>>
    /\ absFile' = absFile
    /\ absFilePointer' = absFilePointer
    /\ absFileLength' = absFileLength

CompleteFlush ==
    /\ pc = "flush"
    /\ pc' = "idle"
    /\ UNCHANGED <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                   bufferModified, filePointer, logicalLength,
                   absFile, absFilePointer, absFileLength>>

--------------------------------------------------------------------------------
\* Seek operation

DoSeek(pos) ==
    /\ pc = "idle"
    /\ pos \in 0..MaxSeekPos
    /\ pos <= MaxFileSize
    /\ pc' = "seek"
    /\ filePointer' = pos
    /\ absFilePointer' = pos
    /\ UNCHANGED <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                   bufferModified, logicalLength, absFile, absFileLength>>

CompleteSeek ==
    /\ pc = "seek"
    /\ pc' = "idle"
    /\ UNCHANGED <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                   bufferModified, filePointer, logicalLength,
                   absFile, absFilePointer, absFileLength>>

--------------------------------------------------------------------------------
\* Read operation

\* Check if position is within buffer
InBuffer(pos) ==
    pos >= bufferStart /\ pos < bufferEnd

\* Load buffer starting at given position
LoadBuffer(startPos) ==
    LET 
        endPos == Min(startPos + BufferSize, Max(logicalLength, diskFileLength))
        newBuffer == [i \in 0..(BufferSize-1) |->
            IF startPos + i < diskFileLength 
            THEN diskFile[startPos + i + 1]
            ELSE ArbitrarySymbol]
    IN
    /\ buffer' = newBuffer
    /\ bufferStart' = startPos
    /\ bufferEnd' = endPos

DoRead ==
    /\ pc = "idle"
    /\ filePointer < logicalLength  \* Can only read if not at EOF
    /\ pc' = "read"
    /\ IF InBuffer(filePointer) THEN
        \* Read from buffer
        LET val == buffer[filePointer - bufferStart] IN
        /\ filePointer' = filePointer + 1
        /\ absFilePointer' = absFilePointer + 1
        /\ UNCHANGED <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                       bufferModified, logicalLength, absFile, absFileLength>>
       ELSE
        \* Need to load buffer first (flush if modified)
        /\ IF bufferModified THEN
            FlushBuffer
           ELSE
            UNCHANGED <<diskFile, diskFileLength, bufferModified>>
        /\ LoadBuffer(filePointer)
        /\ filePointer' = filePointer + 1
        /\ absFilePointer' = absFilePointer + 1
        /\ UNCHANGED <<logicalLength, absFile, absFileLength>>

CompleteRead ==
    /\ pc = "read"
    /\ pc' = "idle"
    /\ UNCHANGED <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                   bufferModified, filePointer, logicalLength,
                   absFile, absFilePointer, absFileLength>>

--------------------------------------------------------------------------------
\* Write operation

DoWrite(val) ==
    /\ pc = "idle"
    /\ val \in DataValues
    /\ filePointer < MaxFileSize  \* Don't exceed max file size
    /\ pc' = "write"
    /\ IF InBuffer(filePointer) \/ 
          (filePointer = bufferEnd /\ bufferEnd - bufferStart < BufferSize) THEN
        \* Write to current buffer
        LET bufOffset == filePointer - bufferStart IN
        /\ buffer' = [buffer EXCEPT ![bufOffset] = val]
        /\ bufferEnd' = Max(bufferEnd, filePointer + 1)
        /\ bufferModified' = TRUE
        /\ filePointer' = filePointer + 1
        /\ logicalLength' = Max(logicalLength, filePointer + 1)
        /\ UNCHANGED <<diskFile, diskFileLength, bufferStart>>
       ELSE
        \* Need new buffer position (flush current first)
        /\ IF bufferModified THEN
            FlushBuffer
           ELSE
            UNCHANGED <<diskFile, diskFileLength, bufferModified>>
        /\ bufferStart' = filePointer
        /\ buffer' = [buffer EXCEPT ![0] = val]
        /\ bufferEnd' = filePointer + 1
        /\ bufferModified' = TRUE
        /\ filePointer' = filePointer + 1
        /\ logicalLength' = Max(logicalLength, filePointer + 1)
    \* Update abstract state
    /\ LET newAbsFile == 
           IF absFilePointer < absFileLength THEN
               UpdateSeq(absFile, absFilePointer + 1, val)
           ELSE
               ExtendSeq(absFile, absFilePointer) \o <<val>>
       IN
       /\ absFile' = newAbsFile
       /\ absFileLength' = Len(newAbsFile)
       /\ absFilePointer' = absFilePointer + 1

CompleteWrite ==
    /\ pc = "write"
    /\ pc' = "idle"
    /\ UNCHANGED <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                   bufferModified, filePointer, logicalLength,
                   absFile, absFilePointer, absFileLength>>

--------------------------------------------------------------------------------
\* SetLength operation

DoSetLength(newLen) ==
    /\ pc = "idle"
    /\ newLen \in 0..MaxFileSize
    /\ pc' = "setLength"
    \* Flush buffer first if it contains data beyond new length
    /\ IF bufferModified /\ bufferStart < newLen THEN
        FlushBuffer
       ELSE IF bufferModified THEN
        /\ bufferModified' = FALSE
        /\ UNCHANGED <<diskFile, diskFileLength>>
       ELSE
        UNCHANGED <<diskFile, diskFileLength, bufferModified>>
    \* Adjust buffer if it's beyond new length
    /\ IF bufferStart >= newLen THEN
        /\ bufferStart' = 0
        /\ bufferEnd' = 0
        /\ buffer' = InitBuffer
       ELSE IF bufferEnd > newLen THEN
        /\ bufferEnd' = newLen
        /\ UNCHANGED <<bufferStart, buffer>>
       ELSE
        UNCHANGED <<bufferStart, bufferEnd, buffer>>
    /\ logicalLength' = newLen
    /\ filePointer' = Min(filePointer, newLen)
    \* Update abstract state
    /\ absFileLength' = newLen
    /\ absFile' = IF newLen <= Len(absFile) 
                  THEN SubSeq(absFile, 1, newLen)
                  ELSE ExtendSeq(absFile, newLen)
    /\ absFilePointer' = Min(absFilePointer, newLen)

CompleteSetLength ==
    /\ pc = "setLength"
    /\ pc' = "idle"
    /\ UNCHANGED <<diskFile, diskFileLength, buffer, bufferStart, bufferEnd,
                   bufferModified, filePointer, logicalLength,
                   absFile, absFilePointer, absFileLength>>

--------------------------------------------------------------------------------
\* Next state relation

Next ==
    \/ DoFlush
    \/ CompleteFlush
    \/ \E pos \in 0..MaxSeekPos : DoSeek(pos)
    \/ CompleteSeek
    \/ DoRead
    \/ CompleteRead
    \/ \E val \in DataValues : DoWrite(val)
    \/ CompleteWrite
    \/ \E len \in 0..MaxFileSize : DoSetLength(len)
    \/ CompleteSetLength

--------------------------------------------------------------------------------
\* Fairness conditions

Fairness ==
    /\ WF_vars(CompleteFlush)
    /\ WF_vars(CompleteSeek)
    /\ WF_vars(CompleteRead)
    /\ WF_vars(CompleteWrite)
    /\ WF_vars(CompleteSetLength)

--------------------------------------------------------------------------------
\* Specification

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* Safety invariants

SafetyInvariants ==
    /\ TypeOK
    /\ BufferBoundaryInvariant
    /\ FilePointerInvariant
    /\ LogicalLengthInvariant

--------------------------------------------------------------------------------
\* Refinement properties

\* The concrete state refines the abstract state when idle
RefinementInvariant ==
    pc = "idle" => 
        /\ absFilePointer = filePointer
        /\ absFileLength = logicalLength

--------------------------------------------------------------------------------
\* Liveness properties

\* Every operation eventually completes
OperationsComplete ==
    /\ pc = "flush" ~> pc = "idle"
    /\ pc = "seek" ~> pc = "idle"
    /\ pc = "read" ~> pc = "idle"
    /\ pc = "write" ~> pc = "idle"
    /\ pc = "setLength" ~> pc = "idle"

================================================================================