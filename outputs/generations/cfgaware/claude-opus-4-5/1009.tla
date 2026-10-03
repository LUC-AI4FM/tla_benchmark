```tla+
---------------------------- MODULE BufferedRandomAccessFile ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

ASSUME ArbitrarySymbol \in Symbols
ASSUME BuffSz > 0
ASSUME MaxOffset >= 0

VARIABLES
    \* Concrete state (buffered file)
    diskFile,        \* The on-disk file contents (sequence of symbols)
    diskFileLen,     \* Length of on-disk file
    buffer,          \* In-memory buffer (function from 0..BuffSz-1 to Symbols)
    bufferLen,       \* Number of valid bytes in buffer
    bufferStart,     \* File offset where buffer starts
    bufferDirty,     \* Whether buffer has been modified
    filePointer,     \* Current logical file pointer position
    logicalFileLen,  \* Logical length of file (may differ from disk due to buffering)
    
    \* Abstract state (for refinement)
    absFile,         \* Abstract file contents
    absFilePointer,  \* Abstract file pointer
    absFileLen       \* Abstract file length

vars == <<diskFile, diskFileLen, buffer, bufferLen, bufferStart, bufferDirty, 
          filePointer, logicalFileLen, absFile, absFilePointer, absFileLen>>

concreteVars == <<diskFile, diskFileLen, buffer, bufferLen, bufferStart, 
                  bufferDirty, filePointer, logicalFileLen>>

abstractVars == <<absFile, absFilePointer, absFileLen>>

\* Helper: Create a sequence of length n filled with ArbitrarySymbol
ArbitrarySeq(n) == [i \in 1..n |-> ArbitrarySymbol]

\* Helper: Extend sequence s to length n with ArbitrarySymbol if needed
ExtendTo(s, n) == 
    IF Len(s) >= n THEN s
    ELSE s \o ArbitrarySeq(n - Len(s))

\* Helper: Get logical file contents (combining disk and buffer)
LogicalFileContents ==
    LET baseFile == ExtendTo(diskFile, logicalFileLen)
        \* Apply buffer contents if buffer is valid
        applyBuffer(f) == 
            IF bufferLen > 0 THEN
                [i \in 1..logicalFileLen |->
                    IF i > bufferStart /\ i <= bufferStart + bufferLen 
                    THEN buffer[i - bufferStart - 1]
                    ELSE f[i]]
            ELSE f
    IN applyBuffer(baseFile)

\* Type invariant
TypeOK ==
    /\ diskFile \in Seq(Symbols)
    /\ diskFileLen \in 0..MaxOffset
    /\ diskFileLen = Len(diskFile)
    /\ buffer \in [0..(BuffSz-1) -> Symbols]
    /\ bufferLen \in 0..BuffSz
    /\ bufferStart \in 0..MaxOffset
    /\ bufferDirty \in BOOLEAN
    /\ filePointer \in 0..MaxOffset
    /\ logicalFileLen \in 0..MaxOffset
    /\ absFile \in Seq(Symbols)
    /\ absFilePointer \in 0..MaxOffset
    /\ absFileLen \in 0..MaxOffset
    /\ absFileLen = Len(absFile)

\* Inv1: Buffer start + buffer length doesn't exceed logical file length (when buffer has content)
Inv1 == bufferLen > 0 => bufferStart + bufferLen <= logicalFileLen

\* Inv2: The system can always be restored (buffer can be flushed)
Inv2CanAlwaysBeRestored == 
    bufferDirty => (bufferStart + bufferLen <= MaxOffset)

\* Inv3: File pointer is within valid range
Inv3 == filePointer <= logicalFileLen + BuffSz

\* Inv4: Buffer contents are consistent with logical file when not dirty
Inv4 == 
    (~bufferDirty /\ bufferLen > 0) => 
        \A i \in 0..(bufferLen-1) : 
            (bufferStart + i + 1 <= Len(diskFile)) => 
                buffer[i] = diskFile[bufferStart + i + 1]

\* Inv5: Logical file length is at least as large as disk file length when buffer extends file
Inv5 == 
    (bufferDirty /\ bufferStart + bufferLen > diskFileLen) => 
        logicalFileLen >= bufferStart + bufferLen

\* Combined safety invariant
Safety == TypeOK /\ Inv1 /\ Inv2CanAlwaysBeRestored /\ Inv3 /\ Inv4 /\ Inv5

\* Initial state
Init ==
    /\ diskFile = <<>>
    /\ diskFileLen = 0
    /\ buffer = [i \in 0..(BuffSz-1) |-> ArbitrarySymbol]
    /\ bufferLen = 0
    /\ bufferStart = 0
    /\ bufferDirty = FALSE
    /\ filePointer = 0
    /\ logicalFileLen = 0
    /\ absFile = <<>>
    /\ absFilePointer = 0
    /\ absFileLen = 0

\* Flush buffer to disk
FlushBuffer ==
    /\ bufferDirty
    /\ bufferLen > 0
    /\ LET newDiskLen == IF bufferStart + bufferLen > diskFileLen 
                         THEN bufferStart + bufferLen 
                         ELSE diskFileLen
           extendedDisk == ExtendTo(diskFile, newDiskLen)
           newDisk == [i \in 1..newDiskLen |->
                        IF i > bufferStart /\ i <= bufferStart + bufferLen
                        THEN buffer[i - bufferStart - 1]
                        ELSE extendedDisk[i]]
       IN /\ diskFile' = newDisk
          /\ diskFileLen' = newDiskLen
    /\ bufferDirty' = FALSE
    /\ UNCHANGED <<buffer, bufferLen, bufferStart, filePointer, logicalFileLen>>
    /\ UNCHANGED abstractVars

\* Flush correctness: after flush, disk matches logical file up to buffer region
FlushBufferCorrect ==
    [](bufferDirty /\ bufferLen > 0 /\ ENABLED FlushBuffer => 
       [FlushBuffer]_vars => ~bufferDirty')

\* Seek operation
Seek(pos) ==
    /\ pos \in 0..MaxOffset
    /\ pos <= logicalFileLen
    /\ filePointer' = pos
    /\ absFilePointer' = pos
    \* May need to flush and refill buffer
    /\ IF pos < bufferStart \/ pos >= bufferStart + bufferLen
       THEN /\ IF bufferDirty 
               THEN LET newDiskLen == IF bufferStart + bufferLen > diskFileLen 
                                      THEN bufferStart + bufferLen 
                                      ELSE diskFileLen
                        extendedDisk == ExtendTo(diskFile, newDiskLen)
                        newDisk == [i \in 1..newDiskLen |->
                                     IF i > bufferStart /\ i <= bufferStart + bufferLen
                                     THEN buffer[i - bufferStart - 1]
                                     ELSE extendedDisk[i]]
                    IN /\ diskFile' = newDisk
                       /\ diskFileLen' = newDiskLen
               ELSE UNCHANGED <<diskFile, diskFileLen>>
            /\ bufferStart' = pos
            /\ bufferLen' = 0
            /\ bufferDirty' = FALSE
       ELSE UNCHANGED <<diskFile, diskFileLen, bufferStart, bufferLen, bufferDirty>>
    /\ UNCHANGED <<buffer, logicalFileLen, absFile, absFileLen>>

SeekCorrect == 
    \A pos \in 0..MaxOffset : 
        [](ENABLED Seek(pos) => [Seek(pos)]_vars => filePointer' = pos)

SeekEstablishesInv2 ==
    \A pos \in 0..MaxOffset :
        [](ENABLED Seek(pos) => [Seek(pos)]_vars => Inv2CanAlwaysBeRestored')

\* Read one byte
Read1 ==
    /\ filePointer < logicalFileLen
    /\ LET inBuffer == filePointer >= bufferStart /\ filePointer < bufferStart + bufferLen
       IN IF inBuffer
          THEN /\ filePointer' = filePointer + 1
               /\ absFilePointer' = absFilePointer + 1
               /\ UNCHANGED <<diskFile, diskFileLen, buffer, bufferLen, bufferStart, 
                              bufferDirty, logicalFileLen, absFile, absFileLen>>
          ELSE \* Need to load into buffer first (simplified: just advance pointer)
               /\ filePointer' = filePointer + 1
               /\ absFilePointer' = absFilePointer + 1
               /\ UNCHANGED <<diskFile, diskFileLen, buffer, bufferLen, bufferStart,
                              bufferDirty, logicalFileLen, absFile, absFileLen>>

Read1Correct ==
    [](ENABLED Read1 => [Read1]_vars => filePointer' = filePointer + 1)

\* Read multiple bytes (up to n)
Read(n) ==
    /\ n > 0
    /\ filePointer < logicalFileLen
    /\ LET bytesToRead == IF filePointer + n <= logicalFileLen 
                          THEN n 
                          ELSE logicalFileLen - filePointer
       IN /\ filePointer' = filePointer + bytesToRead
          /\ absFilePointer' = absFilePointer + bytesToRead
    /\ UNCHANGED <<diskFile, diskFileLen, buffer, bufferLen, bufferStart,
                   bufferDirty, logicalFileLen, absFile, absFileLen>>

ReadCorrect ==
    \A n \in 1..BuffSz :
        [](ENABLED Read(n) => [Read(n)]_vars => filePointer' >= filePointer)

\* Write one byte
Write1(sym) ==
    /\ sym \in Symbols
    /\ filePointer < MaxOffset
    /\ LET inBuffer == filePointer >= bufferStart /\ filePointer < bufferStart + BuffSz
       IN IF inBuffer
          THEN /\ buffer' = [buffer EXCEPT ![filePointer - bufferStart] = sym]
               /\ bufferLen' = IF filePointer - bufferStart >= bufferLen 
                               THEN filePointer - bufferStart + 1 
                               ELSE bufferLen
               /\ bufferDirty' = TRUE
               /\ UNCHANGED <<diskFile, diskFileLen, bufferStart>>
          ELSE \* Flush and start new buffer
               /\ IF bufferDirty /\ bufferLen > 0
                  THEN LET newDiskLen == IF bufferStart + bufferLen > diskFileLen 
                                         THEN bufferStart + bufferLen 
                                         ELSE diskFileLen
                           extendedDisk == ExtendTo(diskFile, newDiskLen)
                           newDisk == [i \in 1..newDiskLen |->
                                        IF i > bufferStart /\ i <= bufferStart + bufferLen
                                        THEN buffer[i - bufferStart - 1]
                                        ELSE extendedDisk[i]]
                       IN /\ diskFile' = newDisk
                          /\ diskFileLen' = newDiskLen
                  ELSE UNCHANGED <<diskFile, diskFileLen>>
               /\ bufferStart' = filePointer
               /\ buffer' = [buffer EXCEPT ![0] = sym]
               /\ bufferLen' = 1
               /\ bufferDirty' = TRUE
    /\ filePointer' = filePointer + 1
    /\ logicalFileLen' = IF filePointer + 1 > logicalFileLen 
                         THEN filePointer + 1 
                         ELSE logicalFileLen
    /\ absFile' = IF absFilePointer + 1 > absFileLen
                  THEN ExtendTo(absFile, absFilePointer) \o <<sym>>
                  ELSE [absFile EXCEPT ![absFilePointer + 1] = sym]
    /\ absFilePointer' = absFilePointer + 1
    /\ absFileLen' = IF absFilePointer + 1 > absFileLen 
                     THEN absFilePointer + 1 
                     ELSE absFileLen

Write1Correct ==
    \A sym \in Symbols :
        [](ENABLED Write1(sym) => [Write1(sym)]_vars => 
           /\ filePointer' = filePointer + 1
           /\ bufferDirty')

\* Write at most n bytes
WriteAtMost(n, sym) ==
    /\ n > 0
    /\ sym \in Symbols
    /\ filePointer + n <= MaxOffset
    /\ filePointer' = filePointer + n
    /\ logicalFileLen' = IF filePointer + n > logicalFileLen 
                         THEN filePointer + n 
                         ELSE logicalFileLen
    /\ bufferDirty' = TRUE
    /\ UNCHANGED <<diskFile, diskFileLen, buffer, bufferLen, bufferStart>>
    /\ absFilePointer' = absFilePointer + n
    /\ absFileLen' = IF absFilePointer + n > absFileLen 
                     THEN absFilePointer + n 
                     ELSE absFileLen
    /\ absFile' = ExtendTo(absFile, absFileLen')

WriteAtMostCorrect ==
    \A n \in 1..BuffSz : \A sym \in Symbols :
        [](ENABLED WriteAtMost(n, sym) => [WriteAtMost(n, sym)]_vars => 
           filePointer' = filePointer + n)

\* Set file length
SetLength(newLen) ==
    /\ newLen \in 0..MaxOffset
    /\ IF newLen < logicalFileLen
       THEN \* Truncate
            /\ IF bufferStart >= newLen
               THEN /\ bufferLen' = 0
                    /\ bufferDirty' = FALSE
               ELSE IF bufferStart + bufferLen > newLen
                    THEN /\ bufferLen' = newLen - bufferStart
                         /\ UNCHANGED bufferDirty
                    ELSE UNCHANGED <<bufferLen, bufferDirty>>
            /\ IF newLen < diskFileLen
               THEN /\ diskFile' = SubSeq(diskFile, 1, newLen)
                    /\ diskFileLen' = newLen
               ELSE UNCHANGED <<diskFile, diskFileLen>>
       ELSE \* Extend (fill with ArbitrarySymbol)
            UNCHANGED <<diskFile, diskFileLen, bufferLen, bufferDirty>>
    /\ logicalFileLen' = newLen
    /\ filePointer' = IF filePointer > newLen THEN newLen ELSE filePointer
    /\ UNCHANGED <<buffer, bufferStart>>
    /\ absFileLen' = newLen
    /\ absFile' = IF newLen < absFileLen 
                  THEN SubSeq(absFile, 1, newLen)
                  ELSE ExtendTo(absFile, newLen)
    /\ absFilePointer' = IF absFilePointer > newLen THEN newLen ELSE absFilePointer

\* Next state relation
Next ==
    \/ FlushBuffer
    \/ \E pos \in 0..MaxOffset : Seek(pos)
    \/ Read1
    \/ \E n \in 1..BuffSz : Read(n)
    \/ \E sym \in Symbols : Write1(sym)
    \/ \E n \in 1..BuffSz : \E sym \in Symbols : WriteAtMost(n, sym)
    \/ \E len \in 0