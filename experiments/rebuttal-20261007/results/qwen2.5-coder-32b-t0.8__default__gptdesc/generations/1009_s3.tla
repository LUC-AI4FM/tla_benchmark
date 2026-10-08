------------------------------- MODULE BufferedRandomAccessFile -------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS 
    MAX_BUFFER_SIZE,
    ArbitrarySymbol

VARIABLES 
    buffer,          \* In-memory buffer of bytes
    bufferPos,       \* Current position in the buffer (0-based)
    fileLength,      \* Length of the logical file
    diskContent,     \* On-disk content represented as a sequence of bytes or ArbitrarySymbol
    seekPos          \* Current seek position in the file

Init == 
    /\ buffer = << >>
    /\ bufferPos = 0
    /\ fileLength = 0
    /\ diskContent = << >>
    /\ seekPos = 0

Seek(newSeekPos) ==
    /\ newSeekPos >= 0
    /\ seekPos' = newSeekPos

Read(n) ==
    /\ n >= 0
    /\ LET availableInBuffer == Min(n, fileLength - seekPos)
       IN
           /\ buffer' = << diskContent[seekPos + 1 .. seekPos + availableInBuffer] >> @@ (buffer EXCEPT [0 .. n - availableInBuffer - 1] =<< >>
           /\ bufferPos' = availableInBuffer
           /\ seekPos' = seekPos + availableInBuffer

Write(bytes) ==
    /\ /\ bytes \in Seq(Nat)
       /\ Len(bytes) <= MAX_BUFFER_SIZE
    /\ LET newLength == Max(fileLength, seekPos + Len(bytes))
       IN
           /\ buffer' = bytes @@ (buffer EXCEPT [Len(bytes) .. MAX_BUFFER_SIZE - 1] =<< >>)
           /\ fileLength' = newLength
           /\ diskContent' = << diskContent[1 .. seekPos] >> @@ bytes @@ << diskContent[fileLength + 1 .. newLength] >>
           /\ bufferPos' = Len(bytes)
           /\ seekPos' = seekPos + Len(bytes)

Flush ==
    /\ diskContent' = << diskContent[1 .. seekPos - fileLength] >> @@ buffer @@ << diskContent[fileLength + 1 .. fileLength] >>
    /\ buffer' = << >>
    /\ bufferPos' = 0

SetLength(newLength) ==
    /\ newLength >= 0
    /\ /\ IF newLength < fileLength THEN
           /\ diskContent' = << diskContent[1 .. newLength] >>
       [] ELSE 
           /\ diskContent' = << diskContent >> @@ << ArbitrarySymbol :> [fileLength + 1 .. newLength] >>
    /\ fileLength' = newLength

Next ==
    \/ \E newSeekPos \in Nat: Seek(newSeekPos)
    \/ \E n \in Nat: Read(n)
    \/ \E bytes \in Seq(Nat): Write(bytes)
    \/ Flush
    \/ \E newLength \in Nat: SetLength(newLength)

Spec == Init /\ [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>

Invariant1 ==
    /\ bufferPos >= 0
    /\ bufferPos <= MAX_BUFFER_SIZE

Invariant2 ==
    /\ seekPos >= 0
    /\ seekPos <= fileLength

Invariant3 ==
    /\ Len(diskContent) = fileLength
    /\ \A i \in 1..fileLength: diskContent[i] \in Nat \/ diskContent[i] = ArbitrarySymbol

RefinementSeek ==
    \A newSeekPos \in Nat: 
        <seekPos, diskContent> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>
        => <newSeekPos, diskContent> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>

RefinementRead ==
    \A n \in Nat:
        /\ <seekPos, diskContent, buffer, bufferPos, fileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>
        => \E newBuffer \in Seq(Nat), newPos \in Nat: 
            Read(n) => <newBuffer, newPos, diskContent, fileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>

RefinementWrite ==
    \A bytes \in Seq(Nat):
        /\ Len(bytes) <= MAX_BUFFER_SIZE
        /\ <seekPos, diskContent, buffer, bufferPos, fileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>
        => \E newDiskContent \in Seq(Nat), newPos \in Nat, newFileLength \in Nat: 
            Write(bytes) => <newDiskContent, buffer, newPos, newFileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>

RefinementFlush ==
    \A <seekPos, diskContent, buffer, bufferPos, fileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>:
        => \E newDiskContent \in Seq(Nat): 
            Flush => <newDiskContent, << >>, 0, fileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>

RefinementSetLength ==
    \A newLength \in Nat:
        /\ <seekPos, diskContent, buffer, bufferPos, fileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>
        => \E newDiskContent \in Seq(Nat), newFileLength \in Nat: 
            SetLength(newLength) => <newDiskContent, buffer, bufferPos, newFileLength> \in [][Next]_<<buffer, bufferPos, fileLength, diskContent, seekPos>>

Refinement ==
    /\ RefinementSeek
    /\ RefinementRead
    /\ RefinementWrite
    /\ RefinementFlush
    /\ RefinementSetLength

CompleteSpec == Spec /\ Invariant1 /\ Invariant2 /\ Invariant3 /\ Refinement

=============================================================================