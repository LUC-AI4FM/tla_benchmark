```tla
MODULE BufferedRandomAccessFile

EXTENDS Integers, Sequences, RandomAccessFile

CONSTANTS
  ArbitrarySymbol,
  MaxBufferSize,
  FileSize

VARIABLES
  buffer,
  diskContents,
  fileLength,
  bufferStart,
  bufferEnd,
  writePointer,
  readPointer

Init ==
  /\ buffer = <<>>
  /\ diskContents = <<ArbitrarySymbol>>
  /\ fileLength = 0
  /\ bufferStart = 0
  /\ bufferEnd = 0
  /\ writePointer = 0
  /\ readPointer = 0

Seek(position) ==
  /\ position >= 0
  /\ position <= fileLength
  /\ bufferStart' = position
  /\ bufferEnd' = IF position < fileLength THEN position + MaxBufferSize ELSE fileLength
  /\ writePointer' = position
  /\ readPointer' = position
  /\ UNCHANGED <<buffer, diskContents, fileLength>>

Read ==
  /\ readPointer < fileLength
  /\ readPointer' = readPointer + 1
  /\ buffer' = IF readPointer >= bufferStart
                THEN Append(buffer, diskContents[readPointer])
                ELSE diskContents[readPointer]
  /\ UNCHANGED <<diskContents, fileLength, bufferStart, bufferEnd, writePointer>>

Write(data) ==
  /\ writePointer <= fileLength
  /\ writePointer' = writePointer + 1
  /\ fileLength' = IF writePointer > fileLength THEN writePointer ELSE fileLength
  /\ buffer' = Append(buffer, data)
  /\ diskContents' = IF writePointer >= bufferStart
                    THEN Replace(diskContents, writePointer, data)
                    ELSE diskContents
  /\ UNCHANGED <<bufferStart, bufferEnd, readPointer>>

Flush ==
  /\ buffer' = <<>>
  /\ diskContents' = Append(diskContents, buffer)
  /\ fileLength' = IF bufferEnd > fileLength THEN bufferEnd ELSE fileLength
  /\ bufferStart' = 0
  /\ bufferEnd' = 0
  /\ writePointer' = fileLength
  /\ readPointer' = fileLength
  /\ UNCHANGED <<readPointer, writePointer>>

SetLength(newLength) ==
  /\ newLength >= 0
  /\ newLength <= MaxBufferSize + FileSize
  /\ fileLength' = newLength
  /\ IF newLength < fileLength THEN
    /\ buffer' = Take(buffer, newLength - bufferStart)
    /\ diskContents' = Take(diskContents, newLength)
  ELSE
    /\ buffer' = Append(buffer, ArbitrarySymbol)
    /\ diskContents' = Append(diskContents, ArbitrarySymbol)
  /\ writePointer' = newLength
  /\ readPointer' = newLength
  /\ UNCHANGED <<bufferStart, bufferEnd>>

Next ==
  \/ Seek(0)
  \/ Read
  \/ Write(ArbitrarySymbol)
  \/ Flush
  \/ SetLength(FileSize)

Spec == Init /\ [][Next]_<<buffer, diskContents, fileLength, bufferStart, bufferEnd, writePointer, readPointer>>
  
THEOREM Spec => []FileInvariant
FileInvariant ==
  /\ bufferStart <= bufferEnd
  /\ bufferEnd <= fileLength
  /\ Len(buffer) = bufferEnd - bufferStart

THEOREM Spec => []RefinementProperty
RefinementProperty ==
  <>(Seek(0) /\ Write(ArbitrarySymbol) /\ Read)

Fairness == SF_VARIABLES(<<buffer, diskContents, fileLength, bufferStart, bufferEnd, writePointer, readPointer>>)
====================================================================================================
TLC Configuration
====================================================================================================
CONSTANT ArbitrarySymbol = "Arbitrary"
CONSTANT MaxBufferSize = 10
CONSTANT FileSize = 100

INVARIANT FileInvariant
PROPERTY RefinementProperty
FAIRNESS_CONDITION Fairness
```