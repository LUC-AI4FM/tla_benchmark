---------------------------- MODULE BufferedRandomAccessFile ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

ASSUME BuffSz > 0
ASSUME MaxOffset >= 0
ASSUME ArbitrarySymbol \in Symbols

VARIABLES
    \* Underlying file state
    underlyingFile,      \* Function from offset to symbol (or undefined)
    underlyingLength,    \* Length of underlying file
    
    \* Buffered file state
    buffer,              \* Function from buffer index to symbol
    bufferStart,         \* Starting offset in file that buffer represents
    bufferLength,        \* Number of valid bytes in buffer
    dirty,               \* Whether buffer has unflushed writes
    
    \* Logical state
    filePointer,         \* Current position in file
    logicalLength,       \* Logical length of file (may differ from underlying during buffering)
    
    \* Abstract file (for refinement)
    abstractFile,        \* The abstract file contents
    abstractLength,      \* Abstract file length
    abstractPointer      \* Abstract file pointer

vars == <<underlyingFile, underlyingLength, buffer, bufferStart, bufferLength, 
          dirty, filePointer, logicalLength, abstractFile, abstractLength, abstractPointer>>

\* Helper: Create empty file
EmptyFile == [o \in {} |-> ArbitrarySymbol]

\* Helper: File as function with given length
FileWithLength(f, len) == [o \in 0..(len-1) |-> IF o \in DOMAIN f THEN f[o] ELSE ArbitrarySymbol]

\* Helper: Get logical file content (underlying + buffer overlay)
LogicalFile == 
    LET base == FileWithLength(underlyingFile, logicalLength)
        bufEnd == bufferStart + bufferLength
    IN [o \in 0..(logicalLength-1) |-> 
        IF o >= bufferStart /\ o < bufEnd /\ dirty
        THEN buffer[o - bufferStart]
        ELSE IF o \in DOMAIN base THEN base[o] ELSE ArbitrarySymbol]

\* Type invariant
TypeOK ==
    /\ underlyingFile \in [0..MaxOffset -> Symbols] \cup {EmptyFile}
    /\ underlyingLength \in 0..MaxOffset
    /\ buffer \in [0..(BuffSz-1) -> Symbols]
    /\ bufferStart \in 0..MaxOffset
    /\ bufferLength \in 0..BuffSz
    /\ dirty \in BOOLEAN
    /\ filePointer \in 0..MaxOffset
    /\ logicalLength \in 0..MaxOffset
    /\ abstractFile \in [0..MaxOffset -> Symbols] \cup {EmptyFile}
    /\ abstractLength \in 0..MaxOffset
    /\ abstractPointer \in 0..MaxOffset

\* Inv1: Buffer bounds are valid
Inv1 ==
    /\ bufferStart + bufferLength <= MaxOffset
    /\ bufferLength <= BuffSz

\* Inv2: Buffer can be restored (dirty implies buffer region within logical file)
Inv2CanAlwaysBeRestored ==
    dirty => (bufferStart + bufferLength <= logicalLength)

\* Inv3: Logical file equals underlying file updated by buffer modifications
Inv3 ==
    \A o \in 0..(logicalLength-1) :
        LET inBuffer == o >= bufferStart /\ o < bufferStart + bufferLength
            bufIdx == o - bufferStart
        IN IF inBuffer /\ dirty
           THEN (bufIdx \in DOMAIN buffer => LogicalFile[o] = buffer[bufIdx])
           ELSE (o \in DOMAIN underlyingFile => LogicalFile[o] = underlyingFile[o])

\* Inv4: After flush, file pointer relationship holds
Inv4 ==
    ~dirty => (filePointer = abstractPointer)

\* Inv5: Abstract and logical state consistency
Inv5 ==
    /\ logicalLength = abstractLength
    /\ filePointer = abstractPointer

\* Combined safety invariant
Safety == TypeOK /\ Inv1 /\ Inv3

\* Initialize buffer with zeros/arbitrary
InitBuffer == [i \in 0..(BuffSz-1) |-> ArbitrarySymbol]

\* Initial state
Init ==
    /\ underlyingFile = EmptyFile
    /\ underlyingLength = 0
    /\ buffer = InitBuffer
    /\ bufferStart = 0
    /\ bufferLength = 0
    /\ dirty = FALSE
    /\ filePointer = 0
    /\ logicalLength = 0
    /\ abstractFile = EmptyFile
    /\ abstractLength = 0
    /\ abstractPointer = 0

\* Flush buffer to underlying file
FlushBuffer ==
    /\ dirty
    /\ LET newUnderlying == 
           [o \in 0..(logicalLength-1) |->
               IF o >= bufferStart /\ o < bufferStart + bufferLength
               THEN buffer[o - bufferStart]
               ELSE IF o \in DOMAIN underlyingFile 
                    THEN underlyingFile[o] 
                    ELSE ArbitrarySymbol]
       IN /\ underlyingFile' = newUnderlying
          /\ underlyingLength' = logicalLength
    /\ dirty' = FALSE
    /\ UNCHANGED <<buffer, bufferStart, bufferLength, filePointer, logicalLength,
                   abstractFile, abstractLength, abstractPointer>>

\* Flush correctness: after flush, underlying equals logical
FlushBufferCorrect ==
    [][dirty /\ FlushBuffer => 
       underlyingFile' = FileWithLength(LogicalFile, logicalLength)]_vars

\* Refill buffer at given offset
RefillBuffer(offset) ==
    LET newStart == offset
        newLen == IF newStart + BuffSz <= logicalLength 
                  THEN BuffSz 
                  ELSE IF newStart < logicalLength 
                       THEN logicalLength - newStart 
                       ELSE 0
        newBuf == [i \in 0..(BuffSz-1) |->
                   IF i < newLen /\ (newStart + i) \in DOMAIN underlyingFile
                   THEN underlyingFile[newStart + i]
                   ELSE ArbitrarySymbol]
    IN /\ buffer' = newBuf
       /\ bufferStart' = newStart
       /\ bufferLength' = newLen

\* Seek operation
Seek(pos) ==
    /\ pos >= 0
    /\ pos <= MaxOffset
    /\ filePointer' = pos
    /\ abstractPointer' = pos
    /\ UNCHANGED <<underlyingFile, underlyingLength, buffer, bufferStart, 
                   bufferLength, dirty, logicalLength, abstractFile, abstractLength>>

SeekCorrect ==
    [][\A pos \in 0..MaxOffset : Seek(pos) => filePointer' = pos]_vars

SeekEstablishesInv2 ==
    [][\A pos \in 0..MaxOffset : Seek(pos) => Inv2CanAlwaysBeRestored']_vars

\* Check if offset is in buffer
InBuffer(offset) ==
    /\ offset >= bufferStart
    /\ offset < bufferStart + bufferLength

\* Read single byte
Read1(result) ==
    /\ filePointer < logicalLength
    /\ InBuffer(filePointer)
    /\ result = buffer[filePointer - bufferStart]
    /\ filePointer' = filePointer + 1
    /\ abstractPointer' = abstractPointer + 1
    /\ UNCHANGED <<underlyingFile, underlyingLength, buffer, bufferStart,
                   bufferLength, dirty, logicalLength, abstractFile, abstractLength>>

Read1Correct ==
    [][\E r \in Symbols : Read1(r) => 
       r = LogicalFile[filePointer]]_vars

\* Write single byte
Write1(sym) ==
    /\ sym \in Symbols
    /\ filePointer < MaxOffset
    /\ LET newLogLen == IF filePointer >= logicalLength 
                        THEN filePointer + 1 
                        ELSE logicalLength
           inBuf == InBuffer(filePointer)
       IN IF inBuf
          THEN /\ buffer' = [buffer EXCEPT ![filePointer - bufferStart] = sym]
               /\ dirty' = TRUE
               /\ UNCHANGED <<bufferStart, bufferLength>>
          ELSE UNCHANGED <<buffer, bufferStart, bufferLength, dirty>>
    /\ logicalLength' = IF filePointer >= logicalLength 
                        THEN filePointer + 1 
                        ELSE logicalLength
    /\ abstractLength' = logicalLength'
    /\ abstractFile' = [o \in 0..(abstractLength'-1) |->
                        IF o = filePointer THEN sym
                        ELSE IF o \in DOMAIN abstractFile THEN abstractFile[o]
                        ELSE ArbitrarySymbol]
    /\ filePointer' = filePointer + 1
    /\ abstractPointer' = abstractPointer + 1
    /\ UNCHANGED <<underlyingFile, underlyingLength>>

Write1Correct ==
    [][\A s \in Symbols : Write1(s) => 
       LogicalFile'[filePointer] = s]_vars

\* Read multiple bytes (up to n bytes)
Read(n, result) ==
    /\ n > 0
    /\ n <= BuffSz
    /\ filePointer + n <= logicalLength
    /\ \A i \in 0..(n-1) : InBuffer(filePointer + i)
    /\ result = [i \in 0..(n-1) |-> buffer[filePointer + i - bufferStart]]
    /\ filePointer' = filePointer + n
    /\ abstractPointer' = abstractPointer + n
    /\ UNCHANGED <<underlyingFile, underlyingLength, buffer, bufferStart,
                   bufferLength, dirty, logicalLength, abstractFile, abstractLength>>

ReadCorrect ==
    [][\A n \in 1..BuffSz : \A r \in [0..(n-1) -> Symbols] :
       Read(n, r) => \A i \in 0..(n-1) : r[i] = LogicalFile[filePointer + i]]_vars

\* Write multiple bytes (up to n bytes)
WriteAtMost(data, n) ==
    /\ n > 0
    /\ n <= BuffSz
    /\ data \in [0..(n-1) -> Symbols]
    /\ filePointer + n <= MaxOffset
    /\ \A i \in 0..(n-1) : InBuffer(filePointer + i)
    /\ buffer' = [buffer EXCEPT ![j \in 0..(BuffSz-1)] = 
                  IF j >= (filePointer - bufferStart) /\ j < (filePointer - bufferStart + n)
                  THEN data[j - (filePointer - bufferStart)]
                  ELSE buffer[j]]
    /\ dirty' = TRUE
    /\ logicalLength' = IF filePointer + n > logicalLength 
                        THEN filePointer + n 
                        ELSE logicalLength
    /\ abstractLength' = logicalLength'
    /\ abstractFile' = [o \in 0..(abstractLength'-1) |->
                        IF o >= filePointer /\ o < filePointer + n
                        THEN data[o - filePointer]
                        ELSE IF o \in DOMAIN abstractFile THEN abstractFile[o]
                        ELSE ArbitrarySymbol]
    /\ filePointer' = filePointer + n
    /\ abstractPointer' = abstractPointer + n
    /\ UNCHANGED <<underlyingFile, underlyingLength, bufferStart, bufferLength>>

WriteAtMostCorrect ==
    [][\A n \in 1..BuffSz : \A d \in [0..(n-1) -> Symbols] :
       WriteAtMost(d, n) => \A i \in 0..(n-1) : LogicalFile'[filePointer + i] = d[i]]_vars

\* SetLength operation
SetLength(newLen) ==
    /\ newLen >= 0
    /\ newLen <= MaxOffset
    /\ logicalLength' = newLen
    /\ abstractLength' = newLen
    /\ filePointer' = IF filePointer > newLen THEN newLen ELSE filePointer
    /\ abstractPointer' = filePointer'
    /\ abstractFile' = [o \in 0..(newLen-1) |->
                        IF o \in DOMAIN abstractFile THEN abstractFile[o]
                        ELSE ArbitrarySymbol]
    /\ IF newLen < bufferStart + bufferLength
       THEN /\ bufferLength' = IF newLen <= bufferStart THEN 0 ELSE newLen - bufferStart
            /\ UNCHANGED <<buffer, bufferStart>>
       ELSE UNCHANGED <<buffer, bufferStart, bufferLength>>
    /\ UNCHANGED <<underlyingFile, underlyingLength, dirty>>

\* Next state relation
Next ==
    \/ FlushBuffer
    \/ \E pos \in 0..MaxOffset : Seek(pos)
    \/ \E sym \in Symbols : Write1(sym)
    \/ \E r \in Symbols : Read1(r)
    \/ \E n \in 1..BuffSz : \E data \in [0..(n-1) -> Symbols] : WriteAtMost(data, n)
    \/ \E n \in 1..BuffSz : \E r \in [0..(n-1) -> Symbols] : Read(n, r)
    \/ \E len \in 0..MaxOffset : SetLength(len)

\* Fairness
Fairness == WF_vars(FlushBuffer)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================