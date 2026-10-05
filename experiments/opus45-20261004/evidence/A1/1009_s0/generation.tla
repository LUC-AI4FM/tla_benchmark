---------------------------- MODULE BufferedRandomAccessFile ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

ASSUME ArbitrarySymbol \in Symbols
ASSUME BuffSz > 0
ASSUME MaxOffset >= 0

VARIABLES
    \* Concrete state (buffered file)
    filePtr,        \* Current position in the logical file
    diskFile,       \* The on-disk file contents (sequence)
    diskLength,     \* Length of the on-disk file
    buffer,         \* In-memory buffer (sequence of length BuffSz)
    bufferStart,    \* File offset where buffer starts
    bufferEnd,      \* File offset where valid buffer data ends
    bufferModified, \* Whether buffer has unflushed modifications
    fileLength,     \* Logical file length (may differ from diskLength if buffer extends file)
    \* Abstract state for refinement
    aFilePtr,
    aFileContents,
    aFileLength

vars == <<filePtr, diskFile, diskLength, buffer, bufferStart, bufferEnd, bufferModified, fileLength, aFilePtr, aFileContents, aFileLength>>

concreteVars == <<filePtr, diskFile, diskLength, buffer, bufferStart, bufferEnd, bufferModified, fileLength>>
abstractVars == <<aFilePtr, aFileContents, aFileLength>>

---------------------------------------------------------------------------------------------
\* Helper functions

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

\* Extend a sequence with ArbitrarySymbol to length n
ExtendTo(seq, n) ==
    IF Len(seq) >= n THEN seq
    ELSE seq \o [i \in 1..(n - Len(seq)) |-> ArbitrarySymbol]

\* Get logical file contents (combining disk and buffer)
LogicalFileContents ==
    LET base == ExtendTo(diskFile, fileLength)
        withBuffer == [i \in 1..fileLength |->
            IF i > bufferStart /\ i <= bufferEnd
            THEN buffer[i - bufferStart]
            ELSE base[i]]
    IN withBuffer

\* Read a byte from logical file at position pos (1-indexed)
ReadByte(pos) ==
    IF pos < 1 \/ pos > fileLength THEN ArbitrarySymbol
    ELSE IF pos > bufferStart /\ pos <= bufferEnd
         THEN buffer[pos - bufferStart]
         ELSE IF pos <= Len(diskFile) THEN diskFile[pos] ELSE ArbitrarySymbol

---------------------------------------------------------------------------------------------
\* Type invariant

TypeOK ==
    /\ filePtr \in 0..MaxOffset
    /\ diskFile \in Seq(Symbols)
    /\ Len(diskFile) <= MaxOffset
    /\ diskLength \in 0..MaxOffset
    /\ diskLength = Len(diskFile)
    /\ buffer \in [1..BuffSz -> Symbols]
    /\ bufferStart \in 0..MaxOffset
    /\ bufferEnd \in 0..MaxOffset
    /\ bufferModified \in BOOLEAN
    /\ fileLength \in 0..MaxOffset
    /\ aFilePtr \in 0..MaxOffset
    /\ aFileContents \in Seq(Symbols)
    /\ Len(aFileContents) <= MaxOffset
    /\ aFileLength \in 0..MaxOffset

---------------------------------------------------------------------------------------------
\* Invariants about buffer-file relationship

\* Inv1: Buffer bounds are valid
Inv1 ==
    /\ bufferStart >= 0
    /\ bufferEnd >= bufferStart
    /\ bufferEnd <= bufferStart + BuffSz
    /\ bufferEnd <= fileLength \/ (bufferModified /\ bufferEnd <= bufferStart + BuffSz)

\* Inv2: Buffer can always be restored/flushed - buffer region is within reasonable bounds
Inv2CanAlwaysBeRestored ==
    /\ bufferStart <= MaxOffset
    /\ bufferEnd <= MaxOffset
    /\ (bufferModified => bufferEnd <= fileLength)

\* Inv3: Logical file length consistency
Inv3 ==
    /\ fileLength >= diskLength \/ ~bufferModified
    /\ (bufferModified => fileLength >= bufferEnd)

\* Inv4: Buffer contents match logical file in unmodified regions
Inv4 ==
    ~bufferModified =>
        \A i \in 1..(bufferEnd - bufferStart) :
            (bufferStart + i <= Len(diskFile)) =>
                buffer[i] = diskFile[bufferStart + i]

\* Inv5: File pointer is within valid range
Inv5 ==
    /\ filePtr >= 0
    /\ filePtr <= fileLength

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ Inv1
    /\ Inv3
    /\ Inv5

---------------------------------------------------------------------------------------------
\* Initial state

Init ==
    /\ filePtr = 0
    /\ diskFile = <<>>
    /\ diskLength = 0
    /\ buffer = [i \in 1..BuffSz |-> ArbitrarySymbol]
    /\ bufferStart = 0
    /\ bufferEnd = 0
    /\ bufferModified = FALSE
    /\ fileLength = 0
    /\ aFilePtr = 0
    /\ aFileContents = <<>>
    /\ aFileLength = 0

---------------------------------------------------------------------------------------------
\* Actions

\* Flush buffer to disk
FlushBuffer ==
    /\ bufferModified
    /\ LET newDisk == ExtendTo(diskFile, bufferEnd)
           flushedDisk == [i \in 1..bufferEnd |->
               IF i > bufferStart /\ i <= bufferEnd
               THEN buffer[i - bufferStart]
               ELSE newDisk[i]]
       IN /\ diskFile' = flushedDisk
          /\ diskLength' = Len(flushedDisk)
    /\ bufferModified' = FALSE
    /\ UNCHANGED <<filePtr, buffer, bufferStart, bufferEnd, fileLength>>
    /\ UNCHANGED abstractVars

\* Flush is correct: after flush, disk matches logical file up to bufferEnd
FlushBufferCorrect ==
    [](bufferModified /\ ENABLED FlushBuffer =>
        [FlushBuffer => ~bufferModified']_vars)

\* Seek to a new position
Seek(pos) ==
    /\ pos >= 0
    /\ pos <= MaxOffset
    /\ filePtr' = pos
    /\ aFilePtr' = pos
    /\ UNCHANGED <<diskFile, diskLength, buffer, bufferStart, bufferEnd, bufferModified, fileLength>>
    /\ UNCHANGED <<aFileContents, aFileLength>>

SeekCorrect ==
    \A pos \in 0..MaxOffset :
        [][Seek(pos) => filePtr' = pos]_vars

SeekEstablishesInv2 ==
    \A pos \in 0..MaxOffset :
        [][Seek(pos) => Inv2CanAlwaysBeRestored']_vars

\* Write one byte at current position
Write1(sym) ==
    /\ sym \in Symbols
    /\ filePtr < MaxOffset
    /\ LET newPos == filePtr + 1
           inBuffer == filePtr >= bufferStart /\ filePtr < bufferStart + BuffSz
       IN IF inBuffer
          THEN /\ buffer' = [buffer EXCEPT ![filePtr - bufferStart + 1] = sym]
               /\ bufferEnd' = Max(bufferEnd, newPos)
               /\ bufferModified' = TRUE
               /\ fileLength' = Max(fileLength, newPos)
               /\ UNCHANGED <<diskFile, diskLength, bufferStart>>
          ELSE /\ bufferStart' = filePtr
               /\ buffer' = [buffer EXCEPT ![1] = sym]
               /\ bufferEnd' = newPos
               /\ bufferModified' = TRUE
               /\ fileLength' = Max(fileLength, newPos)
               /\ UNCHANGED <<diskFile, diskLength>>
    /\ filePtr' = filePtr + 1
    /\ aFilePtr' = aFilePtr + 1
    /\ aFileContents' = ExtendTo(aFileContents, Max(aFileLength, filePtr + 1))
    /\ aFileContents' = [aFileContents' EXCEPT ![filePtr + 1] = sym]
    /\ aFileLength' = Max(aFileLength, filePtr + 1)

Write1Correct ==
    \A sym \in Symbols :
        [][Write1(sym) => filePtr' = filePtr + 1]_vars

\* Read one byte at current position
Read1 ==
    /\ filePtr < fileLength
    /\ filePtr' = filePtr + 1
    /\ aFilePtr' = aFilePtr + 1
    /\ UNCHANGED <<diskFile, diskLength, buffer, bufferStart, bufferEnd, bufferModified, fileLength>>
    /\ UNCHANGED <<aFileContents, aFileLength>>

Read1Correct ==
    [][Read1 => filePtr' = filePtr + 1]_vars

\* Write multiple bytes (up to n)
WriteAtMost(data, n) ==
    /\ n > 0
    /\ Len(data) > 0
    /\ LET writeLen == Min(n, Min(Len(data), MaxOffset - filePtr))
       IN /\ writeLen > 0
          /\ filePtr' = filePtr + writeLen
          /\ fileLength' = Max(fileLength, filePtr + writeLen)
          /\ bufferModified' = TRUE
          /\ UNCHANGED <<diskFile, diskLength, buffer, bufferStart, bufferEnd>>
          /\ aFilePtr' = aFilePtr + writeLen
          /\ aFileLength' = Max(aFileLength, aFilePtr + writeLen)
          /\ UNCHANGED aFileContents

WriteAtMostCorrect ==
    \A data \in Seq(Symbols), n \in 1..MaxOffset :
        [][WriteAtMost(data, n) => filePtr' >= filePtr]_vars

\* Read multiple bytes
ReadN(n) ==
    /\ n > 0
    /\ filePtr < fileLength
    /\ LET readLen == Min(n, fileLength - filePtr)
       IN /\ filePtr' = filePtr + readLen
          /\ aFilePtr' = aFilePtr + readLen
    /\ UNCHANGED <<diskFile, diskLength, buffer, bufferStart, bufferEnd, bufferModified, fileLength>>
    /\ UNCHANGED <<aFileContents, aFileLength>>

ReadCorrect ==
    \A n \in 1..MaxOffset :
        [][ReadN(n) => filePtr' >= filePtr]_vars

\* Set file length
SetLength(newLen) ==
    /\ newLen >= 0
    /\ newLen <= MaxOffset
    /\ fileLength' = newLen
    /\ filePtr' = Min(filePtr, newLen)
    /\ IF newLen < diskLength
       THEN /\ diskFile' = SubSeq(diskFile, 1, newLen)
            /\ diskLength' = newLen
       ELSE UNCHANGED <<diskFile, diskLength>>
    /\ IF bufferEnd > newLen
       THEN bufferEnd' = Max(bufferStart, newLen)
       ELSE UNCHANGED bufferEnd
    /\ UNCHANGED <<buffer, bufferStart, bufferModified>>
    /\ aFileLength' = newLen
    /\ aFilePtr' = Min(aFilePtr, newLen)
    /\ aFileContents' = IF newLen < Len(aFileContents)
                        THEN SubSeq(aFileContents, 1, newLen)
                        ELSE aFileContents

---------------------------------------------------------------------------------------------
\* Next state relation

Next ==
    \/ FlushBuffer
    \/ \E pos \in 0..Min(fileLength + 1, MaxOffset) : Seek(pos)
    \/ \E sym \in Symbols : Write1(sym)
    \/ Read1
    \/ \E n \in 1..MaxOffset : ReadN(n)
    \/ \E newLen \in 0..MaxOffset : SetLength(newLen)

---------------------------------------------------------------------------------------------
\* Specification

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------------------------
\* Refinement - abstract RandomAccessFile specification

AbstractTypeOK ==
    /\ aFilePtr \in 0..MaxOffset
    /\ aFileContents \in Seq(Symbols)
    /\ aFileLength \in 0..MaxOffset

AbstractInit ==
    /\ aFilePtr = 0
    /\ aFileContents = <<>>
    /\ aFileLength = 0

AbstractNext ==
    \/ \E pos \in 0..MaxOffset : aFilePtr' = pos /\ UNCHANGED <<aFileContents, aFileLength>>
    \/ \E sym \in Symbols :
        /\ aFilePtr < MaxOffset
        /\ aFilePtr' = aFilePtr + 1
        /\ aFileContents' = ExtendTo(aFileContents, Max(aFileLength, aFilePtr + 1))
        /\ aFileContents' = [aFileContents' EXCEPT ![aFilePtr + 1] = sym]
        /\ aFileLength' = Max(aFileLength, aFilePtr + 1)
    \/ /\ aFilePtr < aFileLength
       /\ aFilePtr' = aFilePtr + 1
       /\ UNCHANGED <<aFileContents, aFileLength>>

AbstractSpec == AbstractInit /\ [][AbstractNext]_abstractVars

\* Refinement mapping
Refinement == Spec => AbstractSpec

=============================================================================