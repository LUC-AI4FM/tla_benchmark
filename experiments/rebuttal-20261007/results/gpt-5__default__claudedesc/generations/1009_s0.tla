---- MODULE RandomAccessFile ----
EXTENDS Naturals, Sequences

CONSTANT MaxOffset

(*
  Abstract unbuffered random-access file.
  - file_content: function from disk offsets 0..MaxOffset to byte values (modeled as 0..MaxOffset)
  - file_pointer: current position (0..MaxOffset+1, where MaxOffset+1 denotes one past the last addressable byte)
*)
VARIABLES file_content, file_pointer

AbsTypeOK ==
  /\ file_pointer \in 0..(MaxOffset+1)
  /\ file_content \in [0..MaxOffset -> 0..MaxOffset]

AbsInit ==
  /\ AbsTypeOK
  /\ file_pointer = 0

AbsSeek ==
  \E p \in 0..(MaxOffset+1):
    /\ file_pointer' = p
    /\ UNCHANGED file_content

AbsRead1 ==
  /\ file_pointer < MaxOffset+1
  /\ file_pointer' = file_pointer + 1
  /\ UNCHANGED file_content

AbsWrite1 ==
  \E v \in 0..MaxOffset:
    /\ file_pointer \in 0..MaxOffset
    /\ file_content' = [file_content EXCEPT ![file_pointer] = v]
    /\ file_pointer' = file_pointer + 1

AbsSetLength ==
  \E newLen \in 0..(MaxOffset+1):
    /\ file_pointer' = IF file_pointer <= newLen THEN file_pointer ELSE newLen
    /\ UNCHANGED file_content

AbsRead ==
  \E n \in Nat:
    LET k == IF n <= MaxOffset+1 THEN n ELSE MaxOffset+1 IN
    /\ file_pointer' = [IF file_pointer + k <= MaxOffset+1 THEN file_pointer + k ELSE MaxOffset+1]
    /\ UNCHANGED file_content

AbsWriteAtMost ==
  \E s \in Seq(0..MaxOffset):
    \E k \in 0..Len(s):
      /\ file_pointer \in 0..MaxOffset
      /\ file_pointer + k <= MaxOffset+1
      /\ file_content' =
           [ i \in 0..MaxOffset |->
             IF i \in file_pointer..(file_pointer + k - 1)
               THEN s[(i - file_pointer) + 1]
               ELSE file_content[i] ]
      /\ file_pointer' = file_pointer + k

AbsStutter == UNCHANGED <<file_content, file_pointer>>

AbsNext ==
  AbsSeek
  \/ AbsRead1
  \/ AbsWrite1
  \/ AbsSetLength
  \/ AbsRead
  \/ AbsWriteAtMost
  \/ AbsStutter

AbsSpec ==
  AbsInit /\ [][AbsNext]_<<file_content, file_pointer>>


====