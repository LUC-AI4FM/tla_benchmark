------------------------------- MODULE BufferedRandomAccessFile -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    BUFFER_SIZE \* Size of the buffer

VARIABLES 
    filePointer, \* Current position in the logical file
    underlyingFile, \* The actual file contents as a sequence of bytes
    buffer, \* In-memory buffer containing a window of the file
    bufferStart, \* Start index of the current buffer window in the file
    dirty, \* Flag indicating if the buffer has unsaved changes

Init == 
    /\ filePointer = 0
    /\ underlyingFile = << >>
    /\ buffer = << >>
    /\ bufferStart = 0
    /\ dirty = FALSE

Seek(newPos) ==
    \/ newPos >= 0
    \/ \/ newPos < 0
       \/ newPos \notin DOMAIN underlyingFile

SetLength(newLen) ==
    \/ newLen >= 0
    \/ \/ newLen < 0
       \/ newLen \notin DOMAIN underlyingFile

ReadSingleByte() ==
    /\ filePointer \in DOMAIN buffer
    /\ LET byte == buffer[filePointer - bufferStart + 1] IN
        \/ UNCHANGED filePointer
        \/ UNCHANGED underlyingFile
        \/ UNCHANGED buffer
        \/ UNCHANGED bufferStart
        \/ UNCHANGED dirty

ReadMultiByte(n) ==
    /\ n >= 0
    /\ \A i \in 1..n: filePointer + i - 1 \in DOMAIN buffer
    /\ LET bytes == <<buffer[filePointer - bufferStart + i]: i \in 1..n>> IN
        \/ UNCHANGED filePointer
        \/ UNCHANGED underlyingFile
        \/ UNCHANGED buffer
        \/ UNCHANGED bufferStart
        \/ UNCHANGED dirty

WriteSingleByte(byte) ==
    /\ filePointer \in DOMAIN buffer
    /\ \/ LET newBuffer == [buffer EXCEPT ![filePointer - bufferStart + 1] = byte] IN
           \/ filePointer' = filePointer + 1
           \/ underlyingFile' = underlyingFile
           \/ buffer' = newBuffer
           \/ bufferStart' = bufferStart
           \/ dirty' = TRUE

WriteMultiByte(bytes) ==
    /\ Len(bytes) > 0
    /\ \A i \in 1..Len(bytes): filePointer + i - 1 \in DOMAIN buffer
    /\ \/ LET newBuffer == [buffer EXCEPT ![filePointer - bufferStart + i] = bytes[i]: i \in 1..Len(bytes)] IN
           \/ filePointer' = filePointer + Len(bytes)
           \/ underlyingFile' = underlyingFile
           \/ buffer' = newBuffer
           \/ bufferStart' = bufferStart
           \/ dirty' = TRUE

Flush() ==
    /\ dirty
    /\ \/ LET updatedUnderlying == [underlyingFile EXCEPT ![i] = buffer[i - bufferStart + 1]: i \in DOMAIN buffer] IN
           \/ filePointer' = filePointer
           \/ underlyingFile' = updatedUnderlying
           \/ buffer' = buffer
           \/ bufferStart' = bufferStart
           \/ dirty' = FALSE

RefillBuffer() ==
    /\ \/ LET newBuffer == <<underlyingFile[i]: i \in {bufferStart + 1 .. bufferStart + BUFFER_SIZE}>> IN
           \/ filePointer' = filePointer
           \/ underlyingFile' = underlyingFile
           \/ buffer' = newBuffer
           \/ bufferStart' = filePointer
           \/ dirty' = FALSE

Next ==
    \/ /\ Seek(newPos) 
       /\ \/ filePointer' = newPos
          /\ underlyingFile' = underlyingFile
          /\ buffer' = << >>
          /\ bufferStart' = 0
          /\ dirty' = FALSE
    \/ /\ SetLength(newLen)
       /\ \/ filePointer' \in {filePointer, newLen}
          /\ underlyingFile' = (IF newLen >= Len(underlyingFile) THEN Append(underlyingFile, <<0>>:newLen - Len(underlyingFile)) ELSE SubSeq(underlyingFile, 1, newLen))
          /\ buffer' = << >>
          /\ bufferStart' = 0
          /\ dirty' = FALSE
    \/ ReadSingleByte()
    \/ ReadMultiByte(n)
    \/ WriteSingleByte(byte)
    \/ WriteMultiByte(bytes)
    \/ Flush()
    \/ RefillBuffer()

Spec ==
    Init /\ [][Next]_<<filePointer, underlyingFile, buffer, bufferStart, dirty>>

Invariants ==
    /\ filePointer \in 0..Len(underlyingFile)
    /\ Len(buffer) <= BUFFER_SIZE
    /\ \A i \in DOMAIN buffer: buffer[i] = underlyingFile[bufferStart + i - 1]
    /\ \/ ~dirty \/ \E i \in DOMAIN buffer: buffer[i] # underlyingFile[bufferStart + i - 1]

Liveness ==
    <>[](\A i \in DOMAIN buffer: buffer[i] = underlyingFile[bufferStart + i - 1])

Fairness ==
    WF_next(Next)

=============================================================================