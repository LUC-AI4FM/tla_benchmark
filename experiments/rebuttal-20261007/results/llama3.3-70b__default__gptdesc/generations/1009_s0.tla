```tla
MODULE BufferedRandomAccessFile

EXTENDS Integers, Sequences, TLC

CONSTANTS
  MaxBufferSize,
  ArbitrarySymbol,
  FileSize

VARIABLES
  buffer,
  bufferStart,
  bufferEnd,
  fileContents,
  fileLength

Init ==
  /\ buffer = <<>>
  /\ bufferStart = 0
  /\ bufferEnd = 0
  /\ fileContents = <<>>
  /\ fileLength = 0

Seek(offset) ==
  /\ bufferStart' = offset
  /\ bufferEnd' = IF offset < fileLength THEN offset + MaxBufferSize ELSE fileLength
  /\ buffer' = IF offset < fileLength THEN SubSeq(fileContents, offset, bufferEnd') ELSE <<>>
  /\ fileContents' = fileContents
  /\ fileLength' = fileLength

Read ==
  /\ bufferStart' = bufferStart
  /\ bufferEnd' = bufferEnd
  /\ fileContents' = fileContents
  /\ fileLength' = fileLength
  /\ buffer' = IF bufferStart < bufferEnd THEN Append(buffer, ArbitrarySymbol) ELSE buffer

Write(data) ==
  /\ bufferStart' = bufferStart
  /\ bufferEnd' = bufferEnd + Len(data)
  /\ fileContents' = Append(fileContents, data)
  /\ fileLength' = fileLength + Len(data)
  /\ buffer' = Append(buffer, data)

Flush ==
  /\ bufferStart' = bufferStart
  /\ bufferEnd' = bufferEnd
  /\ fileContents' = Append(fileContents, SubSeq(buffer, bufferStart, bufferEnd))
  /\ fileLength' = fileLength + (bufferEnd - bufferStart)
  /\ buffer' = <<>>

SetLength(length) ==
  /\ bufferStart' = bufferStart
  /\ bufferEnd' = bufferEnd
  /\ fileContents' = IF length < fileLength THEN SubSeq(fileContents, 1, length) ELSE Append(fileContents, Repeat(ArbitrarySymbol, length - fileLength))
  /\ fileLength' = length
  /\ buffer' = IF length < fileLength THEN <<>> ELSE buffer

Next ==
  \/ \E offset \in 0..FileSize : Seek(offset)
  \/ Read
  \/ \E data \in Seq(ArbitrarySymbol) : Write(data)
  \/ Flush
  \/ \E length \in 0..FileSize : SetLength(length)

Spec == Init /\ [][Next]_<<buffer, bufferStart, bufferEnd, fileContents, fileLength>>

THEOREM Spec => []Inv

Inv ==
  /\ bufferStart <= bufferEnd
  /\ bufferEnd <= fileLength
  /\ Len(buffer) = bufferEnd - bufferStart
  /\ SubSeq(fileContents, bufferStart, bufferEnd) = SubSeq(buffer, 1, Len(buffer))

Fairness == SF_VARIABLES(<<buffer, bufferStart, bufferEnd, fileContents, fileLength>>)

=============================================================================
TLC Configuration
=============================================================================

CONSTANT
  MaxBufferSize = 10,
  ArbitrarySymbol = "arb",
  FileSize = 100

INVARIANT Inv

PROPERTIES Spec => []Inv

SYMMETRY BufferSymmetry

ALIASING ON buffer, bufferStart, bufferEnd, fileContents, fileLength
```