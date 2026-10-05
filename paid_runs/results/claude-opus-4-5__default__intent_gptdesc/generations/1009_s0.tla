---------------------------- MODULE BufferedRandomAccessFile ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxFileSize,        \* Maximum file size
    BufferSize,         \* Size of the in-memory buffer
    MaxBytes,           \* Maximum byte value (e.g., 255 for 8-bit bytes)
    NullByte            \* Represents uninitialized/zero byte

ASSUME BufferSize > 0
ASSUME MaxFileSize >= BufferSize
ASSUME MaxBytes > 0

VARIABLES
    \* Underlying file state
    underlyingFile,     \* Function from offset -> byte value (the physical file)
    underlyingLength,   \* Length of underlying file
    
    \* Buffer state
    buffer,             \* Function from buffer index -> byte value
    bufferStart,        \* Start offset in file that buffer maps to
    bufferLength,       \* How many bytes are currently valid in buffer
    bufferDirty,        \* Boolean: true if buffer has unflushed writes
    
    \* File pointer and logical state
    filePointer,        \* Current position in the logical file
    logicalLength,      \* Logical length of file (may differ during buffered ops)
    
    \* Abstract specification state (for refinement)
    abstractFile,       \* The abstract file contents
    abstractPointer,    \* Abstract file pointer
    abstractLength      \* Abstract file length

vars == <<underlyingFile, underlyingLength, buffer, bufferStart, bufferLength,
          bufferDirty, filePointer, logicalLength, abstractFile, abstractPointer, abstractLength>>

-----------------------------------------------------------------------------
(* Helper Operators *)

\* Range of valid byte values
ByteValue == 0..MaxBytes

\* Valid file offsets
FileOffset == 0..MaxFileSize

\* Create an empty file (function with no mappings)
EmptyFile == [o \in {} |-> NullByte]

\* Get byte from file at offset, NullByte if beyond length
GetByte(file, len, offset) ==
    IF offset < len /\ offset \in DOMAIN file
    THEN file[offset]
    ELSE NullByte

\* Set byte in file at offset, extending domain if needed
SetByte(file, offset, value) ==
    [o \in (DOMAIN file \union {offset}) |-> IF o = offset THEN value ELSE file[o]]

\* Check if offset falls within buffer window
InBufferWindow(offset) ==
    offset >= bufferStart /\ offset < bufferStart + bufferLength

\* Get buffer index for a file offset
BufferIndex(offset) == offset - bufferStart

\* Compute the logical file contents (underlying + buffered modifications)
LogicalFile ==
    [o \in 0..logicalLength-1 |->
        IF InBufferWindow(o)
        THEN buffer[BufferIndex(o)]
        ELSE GetByte(underlyingFile, underlyingLength, o)]

-----------------------------------------------------------------------------
(* Flush Operation - writes dirty buffer to underlying file *)

FlushBuffer ==
    /\ bufferDirty = TRUE
    /\ LET newUnderlying == 
           [o \in 0..Max(underlyingLength-1, bufferStart + bufferLength - 1) |->
               IF o >= bufferStart /\ o < bufferStart + bufferLength
               THEN buffer[BufferIndex(o)]
               ELSE GetByte(underlyingFile, underlyingLength, o)]
           newUnderlyingLen == Max(underlyingLength, bufferStart + bufferLength)
       IN
       /\ underlyingFile' = newUnderlying
       /\ underlyingLength' = newUnderlyingLen
       /\ bufferDirty' = FALSE
       /\ UNCHANGED <<buffer, bufferStart, bufferLength, filePointer, logicalLength>>
       \* Abstract state update
       /\ abstractFile' = [o \in 0..abstractLength-1 |-> GetByte(abstractFile, abstractLength, o)]
       /\ UNCHANGED <<abstractPointer, abstractLength>>

FlushBufferClean ==
    /\ bufferDirty = FALSE
    /\ UNCHANGED vars

Flush == FlushBuffer \/ FlushBufferClean

-----------------------------------------------------------------------------
(* Refill Buffer - load buffer from underlying file at new position *)

RefillBuffer(newStart) ==
    LET actualLen == Min(BufferSize, Max(0, logicalLength - newStart))
        newBuf == [i \in 0..BufferSize-1 |->
                      IF i < actualLen
                      THEN GetByte(underlyingFile, underlyingLength, newStart + i)
                      ELSE NullByte]
    IN
    /\ bufferStart' = newStart
    /\ buffer' = newBuf
    /\ bufferLength' = actualLen
    /\ bufferDirty' = FALSE

-----------------------------------------------------------------------------
(* Seek Operation *)

SeekOp(newPos) ==
    /\ newPos >= 0
    /\ newPos <= MaxFileSize
    /\ filePointer' = newPos
    /\ abstractPointer' = newPos
    \* If seeking outside buffer, may need to flush and refill
    /\ IF ~InBufferWindow(newPos) /\ bufferDirty
       THEN \* Flush first, then refill
            LET flushUnderlying == 
                [o \in 0..Max(underlyingLength-1, bufferStart + bufferLength - 1) |->
                    IF o >= bufferStart /\ o < bufferStart + bufferLength
                    THEN buffer[BufferIndex(o)]
                    ELSE GetByte(underlyingFile, underlyingLength, o)]
                flushLen == Max(underlyingLength, bufferStart + bufferLength)
                newBufStart == (newPos \div BufferSize) * BufferSize
                actualLen == Min(BufferSize, Max(0, logicalLength - newBufStart))
            IN
            /\ underlyingFile' = flushUnderlying
            /\ underlyingLength' = flushLen
            /\ bufferStart' = newBufStart
            /\ buffer' = [i \in 0..BufferSize-1 |->
                            IF i < actualLen
                            THEN GetByte(flushUnderlying, flushLen, newBufStart + i)
                            ELSE NullByte]
            /\ bufferLength' = actualLen
            /\ bufferDirty' = FALSE
       ELSE IF ~InBufferWindow(newPos)
            THEN \* Just refill
                 LET newBufStart == (newPos \div BufferSize) * BufferSize
                     actualLen == Min(BufferSize, Max(0, logicalLength - newBufStart))
                 IN
                 /\ bufferStart' = newBufStart
                 /\ buffer' = [i \in 0..BufferSize-1 |->
                                 IF i < actualLen
                                 THEN GetByte(underlyingFile, underlyingLength, newBufStart + i)
                                 ELSE NullByte]
                 /\ bufferLength' = actualLen
                 /\ bufferDirty' = FALSE
                 /\ UNCHANGED <<underlyingFile, underlyingLength>>
            ELSE UNCHANGED <<underlyingFile, underlyingLength, buffer, bufferStart, bufferLength, bufferDirty>>
    /\ UNCHANGED <<logicalLength, abstractFile, abstractLength>>

Seek == \E pos \in 0..MaxFileSize: SeekOp(pos)

-----------------------------------------------------------------------------
(* SetLength Operation *)

SetLengthOp(newLen) ==
    /\ newLen >= 0
    /\ newLen <= MaxFileSize
    /\ logicalLength' = newLen
    /\ abstractLength' = newLen
    \* Adjust file pointer if beyond new length
    /\ filePointer' = IF filePointer > newLen THEN newLen ELSE filePointer
    /\ abstractPointer' = IF abstractPointer > newLen THEN newLen ELSE abstractPointer
    \* Adjust abstract file
    /\ abstractFile' = [o \in 0..Max(0, newLen-1) |->
                           IF o < abstractLength
                           THEN GetByte(abstractFile, abstractLength, o)
                           ELSE NullByte]
    \* If truncating, may affect buffer
    /\ IF newLen < bufferStart + bufferLength
       THEN bufferLength' = Max(0, newLen - bufferStart)
       ELSE UNCHANGED bufferLength
    /\ UNCHANGED <<underlyingFile, underlyingLength, buffer, bufferStart, bufferDirty>>

SetLength == \E len \in 0..MaxFileSize: SetLengthOp(len)

-----------------------------------------------------------------------------
(* Read Single Byte Operation *)

ReadByteOp(result) ==
    /\ filePointer < logicalLength
    /\ InBufferWindow(filePointer)
    /\ result = buffer[BufferIndex(filePointer)]
    /\ filePointer' = filePointer + 1
    /\ abstractPointer' = abstractPointer + 1
    /\ UNCHANGED <<underlyingFile, underlyingLength, buffer, bufferStart, 
                   bufferLength, bufferDirty, logicalLength, abstractFile, abstractLength>>

ReadByteEOF ==
    /\ filePointer >= logicalLength
    /\ UNCHANGED vars

ReadByte == \E b \in ByteValue: ReadByteOp(b) \/ ReadByteEOF

-----------------------------------------------------------------------------
(* Write Single Byte Operation *)

WriteByteOp(value) ==
    /\ value \in ByteValue
    /\ filePointer < MaxFileSize
    /\ InBufferWindow(filePointer)
    /\ buffer' = [buffer EXCEPT ![BufferIndex(filePointer)] = value]
    /\ bufferDirty' = TRUE
    /\ filePointer' = filePointer + 1
    /\ logicalLength' = Max(logicalLength, filePointer + 1)
    /\ bufferLength' = Max(bufferLength, filePointer - bufferStart + 1)
    \* Abstract state update
    /\ abstractFile' = SetByte(abstractFile, abstractPointer, value)
    /\ abstractPointer' = abstractPointer + 1
    /\ abstractLength' = Max(abstractLength, abstractPointer + 1)
    /\ UNCHANGED <<underlyingFile, underlyingLength, bufferStart>>

WriteByte == \E v \in ByteValue: WriteByteOp(v)

-----------------------------------------------------------------------------
(* Read Multiple Bytes Operation - simplified to read up to BufferSize bytes *)

ReadMultiOp(count, data) ==
    /\ count > 0
    /\ count <= BufferSize
    /\ filePointer + count <= logicalLength
    /\ \A i \in 0..count-1: InBufferWindow(filePointer + i)
    /\ data = [i \in 0..count-1 |-> buffer[BufferIndex(filePointer + i)]]
    /\ filePointer' = filePointer + count
    /\ abstractPointer' = abstractPointer + count
    /\ UNCHANGED <<underlyingFile, underlyingLength, buffer, bufferStart,
                   bufferLength, bufferDirty, logicalLength, abstractFile, abstractLength>>

ReadMulti == \E c \in 1..BufferSize: \E d \in [0..c-1 -> ByteValue]: ReadMultiOp(c, d)

-----------------------------------------------------------------------------
(* Write Multiple Bytes Operation *)

WriteMultiOp(count, data) ==
    /\ count > 0
    /\ count <= BufferSize
    /\ filePointer + count <= MaxFileSize
    /\ \A i \in 0..count-1: InBufferWindow(filePointer + i)
    /\ buffer' = [i \in 0..BufferSize-1 |->
                     IF i >= BufferIndex(filePointer) /\ i < BufferIndex(filePointer) + count
                     THEN data[i - BufferIndex(filePointer)]
                     ELSE buffer[i]]
    /\ bufferDirty' = TRUE
    /\ filePointer' = filePointer + count
    /\ logicalLength' = Max(logicalLength, filePointer + count)
    /\ bufferLength' = Max(bufferLength, filePointer - bufferStart + count)
    \* Abstract state update
    /\ abstractFile' = [o \in 0..Max(abstractLength-1, abstractPointer + count - 1) |->
                           IF o >= abstractPointer /\ o < abstractPointer + count
                           THEN data[o - abstractPointer]
                           ELSE GetByte(abstractFile, abstractLength, o)]
    /\ abstractPointer' = abstractPointer + count
    /\ abstractLength' = Max(abstractLength, abstractPointer + count)
    /\ UNCHANGED <<underlyingFile, underlyingLength, bufferStart>>

WriteMulti == \E c \in 1..BufferSize: \E d \in [0..c-1 -> ByteValue]: WriteMultiOp(c, d)

-----------------------------------------------------------------------------
(* Min/Max helpers *)

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ underlyingFile = EmptyFile
    /\ underlyingLength = 0
    /\ buffer = [i \in 0..BufferSize-1 |-> NullByte]
    /\ bufferStart = 0
    /\ bufferLength = 0
    /\ bufferDirty = FALSE
    /\ filePointer = 0
    /\ logicalLength = 0
    /\ abstractFile = EmptyFile
    /\ abstractPointer = 0
    /\ abstractLength = 0

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \/ Flush
    \/ Seek
    \/ SetLength
    \/ ReadByte
    \/ WriteByte
    \/ ReadMulti
    \/ WriteMulti

-----------------------------------------------------------------------------
(* Fairness Conditions *)

\* Weak fairness on flush ensures dirty buffer can always be flushed
Fairness == WF_vars(FlushBuffer)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Buffer bounds invariant
BufferBoundsInvariant ==
    /\ bufferStart >= 0
    /\ bufferLength >= 0
    /\ bufferLength <= BufferSize
    /\ bufferStart + bufferLength <= MaxFileSize

\* File pointer invariant
FilePointerInvariant ==
    /\ filePointer >= 0
    /\ filePointer <= MaxFileSize
    /\ abstractPointer = filePointer

\* Length invariant
LengthInvariant ==
    /\ logicalLength >= 0
    /\ logicalLength <= MaxFileSize
    /\ underlyingLength >= 0
    /\ underlyingLength <= MaxFileSize
    /\ abstractLength = logicalLength

\* Buffer content consistency: logical file equals underlying + buffered mods
BufferContentInvariant ==
    \A o \in 0..logicalLength-1:
        IF InBufferWindow(o)
        THEN GetByte(abstractFile, abstractLength, o) = buffer[BufferIndex(o)]
        ELSE GetByte(abstractFile, abstractLength, o) = GetByte(underlyingFile, underlyingLength, o)

\* Dirty flag consistency
DirtyFlagInvariant ==
    bufferDirty = FALSE => 
        \A o \in 0..bufferLength-1:
            buffer[o] = GetByte(underlyingFile, underlyingLength, bufferStart + o)

\* Combined type invariant
TypeInvariant ==
    /\ underlyingLength \in 0..MaxFileSize
    /\ bufferStart \in 0..MaxFileSize
    /\ bufferLength \in 0..BufferSize
    /\ bufferDirty \in BOOLEAN
    /\ filePointer \in 0..MaxFileSize
    /\ logicalLength \in 0..MaxFileSize
    /\ abstractPointer \in 0..MaxFileSize
    /\ abstractLength \in 0..MaxFileSize

\* Master invariant
Invariant ==
    /\ TypeInvariant
    /\ BufferBoundsInvariant
    /\ FilePointerInvariant
    /\ LengthInvariant

-----------------------------------------------------------------------------
(* Refinement Properties *)

\* The buffered implementation refines the abstract RandomAccessFile
\* Abstract state is always consistent with logical view
RefinementMapping ==
    /\ abstractPointer = filePointer
    /\ abstractLength = logicalLength

\* After flush, underlying file matches abstract file for written regions
FlushRefinement ==
    bufferDirty = FALSE =>
        \A o \in 0..Min(underlyingLength, logicalLength)-1:
            ~InBufferWindow(o) => 
                GetByte(underlyingFile, underlyingLength, o) = GetByte(abstractFile, abstractLength, o)

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* A dirty buffer can eventually be flushed
CanFlush == bufferDirty = TRUE ~> bufferDirty = FALSE

\* Buffer invariants can always be restored
BufferRestoreProperty == 
    [](bufferDirty = TRUE => <>(bufferDirty = FALSE))

=============================================================================