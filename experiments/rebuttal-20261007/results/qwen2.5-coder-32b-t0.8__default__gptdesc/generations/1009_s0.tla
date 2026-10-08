------------------------------- MODULE BufferedRandomAccessFile -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    BufferSize, 
    ArbitrarySymbol

VARIABLES 
    buffer,         \* The in-memory buffer
    bufStart,       \* Position in the file where the buffer starts
    bufValidLen,    \* Number of valid bytes in the buffer
    logicalLength,  \* Logical length of the file
    diskContents    \* On-disk contents of the file

Init == 
    /\ buffer = << >> 
    /\ bufStart = 0 
    /\ bufValidLen = 0 
    /\ logicalLength = 0 
    /\ diskContents = << >>

Seek(newPos) ==
    /\ bufStart' = newPos
    /\ bufValidLen' = 0

Read(n) ==
    \* Ensure n is non-negative and does not exceed buffer capacity
    \/ /\ n <= 0 
       \/ /\ n <= BufferSize - bufValidLen
          /\ LET readFromBuf = Min(bufValidLen, n)
             unreadFromDisk = n - readFromBuf
             newDiskRead = SubSeq(diskContents, bufStart + bufValidLen + 1, unreadFromDisk) 
             newBuffer = Append(buffer, newDiskRead) 
          IN
          /\ bufValidLen' = bufValidLen + n
          /\ buffer' = Take(newBuffer, BufferSize)
    \/ /\ n > BufferSize - bufValidLen
       /\ LET readFromBuf = Min(bufValidLen, n)
          unreadFromDisk = n - readFromBuf
          newDiskRead = SubSeq(diskContents, bufStart + bufValidLen + 1, unreadFromDisk) 
          newBuffer = Append(buffer, newDiskRead) 
       IN
       /\ bufValidLen' = BufferSize
       /\ buffer' = Take(newBuffer, BufferSize)
       /\ bufStart' = bufStart + unreadFromDisk

Write(dataSeq) ==
    \* Ensure dataSeq fits within remaining buffer space
    \/ /\ Len(dataSeq) <= BufferSize - bufValidLen
       /\ LET newBuffer = Append(buffer, dataSeq) 
          newLogicalLength = Max(logicalLength, bufStart + bufValidLen + Len(dataSeq)) 
       IN
       /\ bufValidLen' = bufValidLen + Len(dataSeq)
       /\ buffer' = Take(newBuffer, BufferSize)
       /\ logicalLength' = newLogicalLength
    \/ /\ Len(dataSeq) > BufferSize - bufValidLen
       /\ LET partialWrite = SubSeq(dataSeq, 1, BufferSize - bufValidLen)
          remainingData = Tail(SubSeq(dataSeq, BufferSize - bufValidLen + 1))
          newBuffer = Append(buffer, partialWrite)
          newDiskContents = [diskContents EXCEPT ![bufStart+1..bufStart+BufferSize] 
                                                  <- Take(newBuffer, BufferSize)]
       IN
       /\ bufValidLen' = BufferSize
       /\ buffer' = newBuffer
       /\ diskContents' = [newDiskContents EXCEPT ![bufStart+BufferSize+1..bufStart+BufferSize+Len(remainingData)] 
                                                      <- remainingData]
       /\ logicalLength' = Max(logicalLength, bufStart + BufferSize + Len(remainingData))

Flush ==
    /\ diskContents' = [diskContents EXCEPT ![bufStart+1..bufStart+bufValidLen] 
                                                  <- Take(buffer, bufValidLen)]
    /\ bufValidLen' = 0

SetLength(newLogicalLength) ==
    /\ logicalLength' = newLogicalLength
    /\ diskContents' = Append(SubSeq(diskContents, 1, newLogicalLength), <<ArbitrarySymbol>>)

Next ==
    \/ \E newPos \in Integers : Seek(newPos)
    \/ \E n \in Integers : Read(n)
    \/ \E dataSeq \in Seq(ArbitrarySymbol) : Write(dataSeq)
    \/ Flush
    \/ \E newLogicalLength \in Integers : SetLength(newLogicalLength)

Spec ==
    /\ Init
    /\ [][Next]_<<buffer, bufStart, bufValidLen, logicalLength, diskContents>>
    /\ WF_[Next]_<<buffer, bufStart, bufValidLen, logicalLength, diskContents>>

Invariants ==
    /\ 0 <= bufStart
    /\ 0 <= bufValidLen /\ bufValidLen <= BufferSize
    /\ 0 <= logicalLength
    /\ Len(diskContents) >= logicalLength

\* Refinement to abstract RandomAccessFile spec would be defined here if provided

=============================================================================