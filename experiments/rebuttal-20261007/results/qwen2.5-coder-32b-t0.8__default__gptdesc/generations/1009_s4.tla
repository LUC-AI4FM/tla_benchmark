---------------------------- MODULE BufferedRandomAccessFileSpec ----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    \* Constants representing the size of the buffer and the maximum file length
    BUFFER_SIZE, MAX_FILE_LENGTH,
    \* ArbitrarySymbol to represent unknown or uninitialized content
    ArbitrarySymbol

VARIABLES 
    \* The current position in the file (cursor)
    pos,
    \* The on-disk contents of the file as a sequence
    diskContents,
    \* The in-memory buffer as a sequence
    buffer,
    \* The offset of the data currently in the buffer from the start of the file
    bufferOffset,
    \* Indicates if the buffer needs to be flushed to the disk
    dirty

CONSTRAINTS 
    /\ pos \in 0..MAX_FILE_LENGTH
    /\ Len(diskContents) \leq MAX_FILE_LENGTH
    /\ Len(buffer) = BUFFER_SIZE
    /\ bufferOffset \in 0..(MAX_FILE_LENGTH - BUFFER_SIZE)
    /\ dirty \in BOOLEAN

Init == 
    /\ pos = 0
    /\ diskContents = << >>
    /\ buffer = << ArbitrarySymbol >> ^ BUFFER_SIZE
    /\ bufferOffset = 0
    /\ dirty = FALSE

Seek(newPos) ==
    /\ newPos \in 0..MAX_FILE_LENGTH
    /\ pos' = newPos
    /\ UNCHANGED <<diskContents, buffer, bufferOffset, dirty>>

Read(n) ==
    /\ n \in 1..BUFFER_SIZE
    /\ LET offsetInBuffer = pos - bufferOffset
       IN
       /\ offsetInBuffer \in 0..(BUFFER_SIZE - n)
       /\ /\ IF (pos + n) > (bufferOffset + BUFFER_SIZE)
            THEN \/ /\ dirty
                 /\ diskContents' = SubSeqReplace(diskContents, bufferOffset+1, buffer)
                 /\ bufferOffset' = pos
                 /\ buffer' = <<ArbitrarySymbol>> ^ BUFFER_SIZE
              ELSE /\ UNCHANGED diskContents
                   /\ UNCHANGED bufferOffset
            FI
       /\ LET readData = SubSeq(buffer, offsetInBuffer + 1, n) 
          IN \/ /\ pos' = pos + n
               /\ UNCHANGED <<diskContents, buffer, bufferOffset, dirty>>
    \* Reading does not change the contents of the file or the state of the buffer

Write(data) ==
    /\ Len(data) \in 1..BUFFER_SIZE
    /\ LET offsetInBuffer = pos - bufferOffset
       IN
       /\ offsetInBuffer \in 0..(BUFFER_SIZE - Len(data))
       /\ /\ IF (pos + Len(data)) > (bufferOffset + BUFFER_SIZE)
            THEN \/ /\ dirty
                 /\ diskContents' = SubSeqReplace(diskContents, bufferOffset+1, buffer)
                 /\ bufferOffset' = pos
                 /\ buffer' = <<ArbitrarySymbol>> ^ BUFFER_SIZE
              ELSE /\ UNCHANGED diskContents
                   /\ UNCHANGED bufferOffset
            FI
       /\ LET newDataBuffer = SubSeqReplace(buffer, offsetInBuffer + 1, data) 
          IN \/ /\ dirty'
               /\ buffer' = newDataBuffer
               /\ pos' = pos + Len(data)

Flush ==
    /\ dirty
    /\ diskContents' = SubSeqReplace(diskContents, bufferOffset+1, buffer)
    /\ dirty' = FALSE
    /\ UNCHANGED <<pos, buffer, bufferOffset>>

SetLength(newLength) ==
    /\ newLength \in 0..MAX_FILE_LENGTH
    /\ \/ /\ (newLength < Len(diskContents))
         THEN diskContents' = SubSeq(diskContents, 1, newLength)
              /\ IF newLength < pos
                 THEN pos' = newLength
              ELSE UNCHANGED pos
              FI
          /\ LET offsetInBuffer = pos - bufferOffset
             IN
             /\ \/ IF (newLength <= bufferOffset) 
                  THEN /\ bufferOffset' = 0
                       /\ buffer' = <<ArbitrarySymbol>> ^ BUFFER_SIZE
                  ELSE /\ buffer' = SubSeqReplace(buffer, 1, newLength - bufferOffset)
                       /\ UNCHANGED bufferOffset
                  FI
              /\ dirty'
         ELSE /\ diskContents' = Append(diskContents, <<ArbitrarySymbol>> ^ (newLength - Len(diskContents)))
              /\ IF pos > newLength 
                 THEN pos' = newLength
              ELSE UNCHANGED pos
              FI
              /\ UNCHANGED bufferOffset
              /\ dirty'
    /\ UNCHANGED <<pos, buffer>>

Next ==
    \/ \E newPos \in 0..MAX_FILE_LENGTH: Seek(newPos)
    \/ \E n \in 1..BUFFER_SIZE: Read(n)
    \/ \E data \in SEQ(ArbitrarySymbol): Len(data) \in 1..BUFFER_SIZE /\ Write(data)
    \/ Flush
    \/ \E newLength \in 0..MAX_FILE_LENGTH: SetLength(newLength)

Spec ==
    Init /\ [][Next]_<<pos, diskContents, buffer, bufferOffset, dirty>>

\* Invariants

InvPosInBounds == pos \in 0..Len(diskContents)
InvBufferOffsetValid == bufferOffset \in 0..(MAX_FILE_LENGTH - BUFFER_SIZE)
InvBufferConsistency ==
    /\ \A i \in 1..BUFFER_SIZE: 
         \/ (bufferOffset + i) > Len(diskContents)
         \/ buffer[i] = diskContents[bufferOffset + i]

\* Refinement Properties

RefinesSeek(newPos) ==
    Seek(newPos) => /\ pos' = newPos
                    /\ UNCHANGED <<diskContents, buffer, bufferOffset, dirty>>

RefinesRead(n) ==
    Read(n) => \/ /\ pos' = pos + n
                 /\ UNCHANGED diskContents
                 /\ /\ IF (pos + n) > (bufferOffset + BUFFER_SIZE)
                      THEN \/ /\ dirty'
                           /\ diskContents' = SubSeqReplace(diskContents, bufferOffset+1, buffer)
                           /\ bufferOffset' = pos
                           /\ buffer' = <<ArbitrarySymbol>> ^ BUFFER_SIZE
                       ELSE /\ UNCHANGED diskContents
                            /\ UNCHANGED bufferOffset
                      FI

RefinesWrite(data) ==
    Write(data) => \/ /\ pos' = pos + Len(data)
                     /\ /\ IF (pos + Len(data)) > (bufferOffset + BUFFER_SIZE)
                          THEN \/ /\ dirty'
                               /\ diskContents' = SubSeqReplace(diskContents, bufferOffset+1, buffer)
                               /\ bufferOffset' = pos
                               /\ buffer' = <<ArbitrarySymbol>> ^ BUFFER_SIZE
                          ELSE /\ UNCHANGED diskContents
                               /\ UNCHANGED bufferOffset
                          FI
                     /\ LET newDataBuffer = SubSeqReplace(buffer, (pos - bufferOffset) + 1, data)
                        IN \/ /\ dirty'
                             /\ buffer' = newDataBuffer

RefinesFlush ==
    Flush => /\ diskContents' = SubSeqReplace(diskContents, bufferOffset+1, buffer)
             /\ dirty' = FALSE
             /\ UNCHANGED <<pos, buffer, bufferOffset>>

RefinesSetLength(newLength) ==
    SetLength(newLength) => \/ /\ (newLength < Len(diskContents))
                             THEN diskContents' = SubSeq(diskContents, 1, newLength)
                                  /\ IF newLength < pos
                                     THEN pos' = newLength
                                  ELSE UNCHANGED pos
                                  FI
                                  /\ LET offsetInBuffer = pos - bufferOffset
                                     IN
                                     /\ \/ IF (newLength <= bufferOffset) 
                                          THEN /\ bufferOffset' = 0
                                               /\ buffer' = <<ArbitrarySymbol>> ^ BUFFER_SIZE
                                          ELSE /\ buffer' = SubSeqReplace(buffer, 1, newLength - bufferOffset)
                                               /\ UNCHANGED bufferOffset
                                          FI
                                  /\ dirty'
                             ELSE /\ diskContents' = Append(diskContents, <<ArbitrarySymbol>> ^ (newLength - Len(diskContents)))
                                  /\ IF pos > newLength 
                                     THEN pos' = newLength
                                  ELSE UNCHANGED pos
                                  FI
                                  /\ UNCHANGED bufferOffset
                                  /\ dirty'

RefinementSpec ==
    Spec /\
    []\<RefinesSeek(newPos) \Wedge RefinesRead(n) \Wedge RefinesWrite(data) \Wedge RefinesFlush \Wedge RefinesSetLength(newLength)\>_<<pos, diskContents, buffer, bufferOffset, dirty>>

=============================================================================