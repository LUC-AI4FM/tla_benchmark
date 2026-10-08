------------------------------- MODULE BufferedRandomAccessFile ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS DiskSize, BufferSize, ArbitrarySymbol

VARIABLES 
    buffer,            \* The in-memory buffer
    bufStart,          \* Logical file position corresponding to the start of the buffer
    fileLength,        \* Length of the logical file
    diskContents       \* Actual contents of the on-disk file

Init == 
    /\ buffer = <<>>
    /\ bufStart = 0
    /\ fileLength = 0
    /\ diskContents = [i \in 0..DiskSize-1 -> ArbitrarySymbol]

Seek(newPos) ==
    \/ newPos < 0 \/ newPos > fileLength
    \/ /\ bufStart' = (newPos \div BufferSize) * BufferSize
       /\ buffer' = [j \in 0..BufferSize-1 ->
           IF bufStart' + j < fileLength
           THEN diskContents[bufStart' + j]
           ELSE ArbitrarySymbol]

Read(len) ==
    \/ len <= 0
    \/ /\ LET endPos == bufStart + LenInBuffer(bufStart, len)
          IN /\ buffer' = [j \in 0..BufferSize-1 ->
              IF bufStart' + j < fileLength
              THEN diskContents[bufStart' + j]
              ELSE ArbitrarySymbol]
         /\ bufStart' = (endPos \div BufferSize) * BufferSize

Write(data) ==
    \/ Len(data) <= 0
    \/ /\ LET endPos == bufStart + LenInBuffer(bufStart, Len(data))
          IN /\ buffer' = [buffer EXCEPT ![j] = data[j] : j \in 0..Len(data)-1]
         /\ fileLength' = Max(fileLength, endPos)
         /\ IF endPos > bufStart + BufferSize
            THEN bufStart' = (endPos \div BufferSize) * BufferSize
            ELSE bufStart' = bufStart

Flush() ==
    /\ diskContents' = [diskContents EXCEPT ![i] = buffer[i - bufStart] : i \in bufStart..bufStart + Len(buffer)-1]
    /\ UNCHANGED fileLength
    /\ UNCHANGED bufStart
    /\ buffer' = <<>>

SetLength(newLen) ==
    \/ newLen < 0
    \/ /\ IF newLen < fileLength
          THEN diskContents' = [diskContents EXCEPT ![i] = ArbitrarySymbol : i \in newLen..fileLength-1]
          ELSE UNCHANGED diskContents
         /\ fileLength' = newLen
         /\ bufStart' = (bufStart \div BufferSize) * BufferSize

LenInBuffer(startPos, len) ==
    MIN(BufferSize - startPos MOD BufferSize, len)

Next == 
    \/ \E newPos \in Int : Seek(newPos)
    \/ \E len \in Int : Read(len)
    \/ \E data \in Seq(Nat) : Write(data)
    \/ Flush()
    \/ \E newLen \in Int : SetLength(newLen)

Spec == Init /\ [][Next]_<<buffer, bufStart, fileLength, diskContents>>

Invariant1 == 
    /\ Len(buffer) = BufferSize
    /\ bufStart % BufferSize = 0

Invariant2 ==
    \/ fileLength <= bufStart
    \/ \A j \in 0..BufferSize-1 : bufStart + j >= fileLength => buffer[j] = ArbitrarySymbol

RefinementSeek ==
    \/ \E newPos \in Int :
        (newPos < 0 \/ newPos > fileLength) =>
            (\A s, s' : Seek(newPos) /\ [s -> s'] => s'.bufStart = s.bufStart)
        \/ (newPos >= 0 /\ newPos <= fileLength) =>
            (\A s, s' : Seek(newPos) /\ [s -> s'] => s'.bufStart = (newPos \div BufferSize) * BufferSize)

RefinementRead ==
    \/ \E len \in Int :
        (len <= 0) =>
            (\A s, s' : Read(len) /\ [s -> s'] => s'.bufStart = s.bufStart)
        \/ (len > 0) =>
            (\A s, s' : Read(len) /\ [s -> s'] => \E endPos \in Int : s'.bufStart = (endPos \div BufferSize) * BufferSize)

RefinementWrite ==
    \/ \E data \in Seq(Nat) :
        (Len(data) <= 0) =>
            (\A s, s' : Write(data) /\ [s -> s'] => s'.fileLength = s.fileLength)
        \/ (Len(data) > 0) =>
            (\A s, s' : Write(data) /\ [s -> s'] => \E endPos \in Int : s'.fileLength = Max(s.fileLength, endPos))

RefinementFlush ==
    \A s, s' : Flush /\ [s -> s'] => 
        \A i \in bufStart..bufStart + Len(buffer)-1 : s'.diskContents[i] = s.buffer[i - s.bufStart]

RefinementSetLength ==
    \/ \E newLen \in Int :
        (newLen < 0) =>
            (\A s, s' : SetLength(newLen) /\ [s -> s'] => s'.fileLength = s.fileLength)
        \/ (newLen >= 0) =>
            (\A s, s' : SetLength(newLen) /\ [s -> s'] => s'.fileLength = newLen)

Refinement ==
    \A s, s' : [s -> s'] => 
        \/ \E newPos \in Int : Seek(newPos)
        \/ \E len \in Int : Read(len)
        \/ \E data \in Seq(Nat) : Write(data)
        \/ Flush()
        \/ \E newLen \in Int : SetLength(newLen)

=============================================================================