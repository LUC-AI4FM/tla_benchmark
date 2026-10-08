```
MODULE BufferedRandomAccessFile
EXTENDS Integers, Sequences, TLC

CONSTANTS
  MaxBufferSize,
  ArbitrarySymbol,
  FileName

VARIABLES
  buffer,
  bufferSize,
  fileLength,
  seekPosition,
  diskContents,
  inMemoryContents

Init ==
  /\ buffer = <<>>
  /\ bufferSize = 0
  /\ fileLength = 0
  /\ seekPosition = 0
  /\ diskContents = <<>>
  /\ inMemoryContents = <<>>

Next ==
  \/ SeekStep
  \/ ReadStep
  \/ WriteStep
  \/ FlushStep
  \/ SetLengthStep

SeekStep ==
  /\ seekPosition' = [seekPosition + 1..fileLength]
  /\ buffer' = <<>>
  /\ bufferSize' = 0
  /\ fileLength' = fileLength
  /\ diskContents' = diskContents
  /\ inMemoryContents' = inMemoryContents

ReadStep ==
  /\ seekPosition < fileLength
  /\ buffer' = Append(buffer, diskContents[seekPosition])
  /\ bufferSize' = bufferSize + 1
  /\ fileLength' = fileLength
  /\ seekPosition' = seekPosition + 1
  /\ diskContents' = diskContents
  /\ inMemoryContents' = inMemoryContents

WriteStep ==
  /\ seekPosition <= fileLength
  /\ buffer' = Append(buffer, ArbitrarySymbol)
  /\ bufferSize' = bufferSize + 1
  /\ fileLength' = IF seekPosition = fileLength THEN fileLength + 1 ELSE fileLength
  /\ seekPosition' = seekPosition + 1
  /\ diskContents' = diskContents
  /\ inMemoryContents' = Append(inMemoryContents, ArbitrarySymbol)

FlushStep ==
  /\ buffer' = <<>>
  /\ bufferSize' = 0
  /\ fileLength' = fileLength
  /\ seekPosition' = seekPosition
  /\ diskContents' = Concat(diskContents, Take(buffer, bufferSize))
  /\ inMemoryContents' = inMemoryContents

SetLengthStep ==
  /\ fileLength' = [0..MaxBufferSize]
  /\ buffer' = <<>>
  /\ bufferSize' = 0
  /\ seekPosition' = 0
  /\ diskContents' = Take(diskContents, fileLength')
  /\ inMemoryContents' = <<>>

Spec ==
  /\ Init
  /\ [][Next]_buffer
  /\ WF_Vars(SeekStep)
  /\ WF_Vars(ReadStep)
  /\ WF_Vars(WriteStep)
  /\ SF_Vars(FlushStep)

THEOREM Spec => [](TypeInvariant /\ BufferInvariant /\ FileLengthInvariant)
TypeInvariant ==
  /\ buffer \in Seq(ArbitrarySymbol)
  /\ bufferSize \in Nat
  /\ fileLength \in Nat
  /\ seekPosition \in Nat

BufferInvariant ==
  /\ Len(buffer) = bufferSize
  /\ buffer = Take(inMemoryContents, bufferSize)

FileLengthInvariant ==
  /\ fileLength <= MaxBufferSize
  /\ diskContents = Take(inMemoryContents, fileLength)
```