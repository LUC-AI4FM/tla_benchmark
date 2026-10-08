```tla
MODULE BufferedRandomAccessFile

EXTENDS Integers, Sequences, TLC

CONSTANTS
  MaxBufferSize,
  ArbitrarySymbol,
  FileDescriptorSet

VARIABLES
  fileDescriptor,
  buffer,
  bufferSize,
  bufferOffset,
  onDiskFile,
  logicalFileSize

Init ==
  /\ fileDescriptor \in FileDescriptorSet
  /\ buffer = <<>>
  /\ bufferSize = 0
  /\ bufferOffset = 0
  /\ onDiskFile = <<>>
  /\ logicalFileSize = 0

Seek(op) ==
  /\ op \in [1..MaxBufferSize]
  /\ bufferOffset' = op
  /\ UNCHANGED <<buffer, bufferSize, fileDescriptor, onDiskFile, logicalFileSize>>

Read(len) ==
  /\ len >= 0
  /\ IF (bufferOffset + len <= bufferSize)
    THEN
      /\ buffer' = buffer
      /\ bufferSize' = bufferSize
      /\ bufferOffset' = bufferOffset + len
      /\ UNCHANGED <<fileDescriptor, onDiskFile, logicalFileSize>>
    ELSE
      /\ onDiskFile' = onDiskFile
      /\ IF (bufferOffset + len <= logicalFileSize)
        THEN
          /\ buffer' = Append(onDiskFile, bufferOffset, len)
          /\ bufferSize' = Len(buffer')
          /\ bufferOffset' = 0
          /\ UNCHANGED <<fileDescriptor, logicalFileSize>>
        ELSE
          /\ buffer' = Append(onDiskFile, bufferOffset, logicalFileSize - bufferOffset)
          /\ bufferSize' = Len(buffer')
          /\ bufferOffset' = 0
          /\ logicalFileSize' = logicalFileSize
          /\ UNCHANGED <<fileDescriptor>>

Write(data) ==
  /\ data # ArbitrarySymbol
  /\ IF (bufferSize + Len(data) <= MaxBufferSize)
    THEN
      /\ buffer' = Append(buffer, data)
      /\ bufferSize' = bufferSize + Len(data)
      /\ bufferOffset' = bufferOffset
      /\ UNCHANGED <<fileDescriptor, onDiskFile, logicalFileSize>>
    ELSE
      /\ onDiskFile' = Append(onDiskFile, buffer)
      /\ buffer' = <<data>>
      /\ bufferSize' = Len(data)
      /\ bufferOffset' = 0
      /\ logicalFileSize' = IF (Len(onDiskFile) + Len(buffer) > logicalFileSize)
                              THEN Len(onDiskFile) + Len(buffer)
                              ELSE logicalFileSize
      /\ UNCHANGED fileDescriptor

Flush ==
  /\ onDiskFile' = Append(onDiskFile, buffer)
  /\ buffer' = <<>>
  /\ bufferSize' = 0
  /\ bufferOffset' = 0
  /\ logicalFileSize' = IF (Len(onDiskFile) + Len(buffer) > logicalFileSize)
                        THEN Len(onDiskFile) + Len(buffer)
                        ELSE logicalFileSize
  /\ UNCHANGED fileDescriptor

SetLength(len) ==
  /\ len >= 0
  /\ onDiskFile' = IF (len < Len(onDiskFile))
                    THEN Take(onDiskFile, len)
                    ELSE Append(onDiskFile, ArbitrarySymbol, len - Len(onDiskFile))
  /\ logicalFileSize' = len
  /\ buffer' = <<>>
  /\ bufferSize' = 0
  /\ bufferOffset' = 0
  /\ UNCHANGED fileDescriptor

Next ==
  \/ \E op \in [1..MaxBufferSize] : Seek(op)
  \/ \E len \in Nat : Read(len)
  \/ \E data \in Seq(ArbitrarySymbol) : Write(data)
  \/ Flush
  \/ \E len \in Nat : SetLength(len)

Spec ==
  /\ Init
  /\ [][Next]_<<fileDescriptor, buffer, bufferSize, bufferOffset, onDiskFile, logicalFileSize>>
  /\ WF_Vars(Seek)
  /\ WF_Vars(Read)
  /\ WF_Vars(Write)
  /\ WF_Vars(Flush)
  /\ SF_Vars(SetLength)

THEOREM Spec => []Inv

Inv ==
  /\ fileDescriptor \in FileDescriptorSet
  /\ bufferSize >= 0
  /\ bufferOffset >= 0
  /\ Len(onDiskFile) >= 0
  /\ logicalFileSize >= 0
  /\ (bufferSize = 0) => (buffer = <<>>)
  /\ (Len(buffer) > 0) => (buffer[1..bufferSize] = Take(onDiskFile, bufferSize))
  /\ bufferOffset <= Len(buffer)

TLCCONFIG ==
  SPECIFICATION Spec
  INVARIANT Inv
  CONSTANT
    MaxBufferSize = 10,
    ArbitrarySymbol = <<1>>,
    FileDescriptorSet = {1, 2}
  SYMMETRY fileDescriptor
  ALIASING fileDescriptor
```
Please note that this is an attempt to model the described system and might need further refinement based on specific requirements or details not covered in the description.