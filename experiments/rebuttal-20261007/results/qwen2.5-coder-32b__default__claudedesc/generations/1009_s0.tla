------------------------------- MODULE BufferedRandomAccessFile -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS BuffSz, MaxOffset

VARIABLES dirty, length, curr, lo, buff, diskPos, file_content, file_pointer

Init == /\ dirty = FALSE
        /\ length = 0
        /\ curr = 0
        /\ lo = 0
        /\ buff = << >>
        /\ diskPos = 0
        /\ file_content = << >>
        /\ file_pointer = 0

LogicalFileContent ==
    LET extended_file == Append(file_content, Take(<<0>>, MaxOffset - Len(file_content)))
        buffer_start == IF lo <= length THEN lo ELSE length
        buffer_end == IF lo + BuffSz <= length THEN lo + BuffSz ELSE length
    IN  [i \in 0..MaxOffset -> 
            IF i < buffer_start \/ i >= buffer_end THEN extended_file[i]
            ELSE buff[i - lo]]

FlushBuffer ==
    /\ dirty
    /\ diskPos = lo
    /\ file_content' = Append(SubSeq(file_content, 1, lo), Append(buff, SubSeq(file_content, lo + BuffSz + 1)))
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr, lo, buff, diskPos, file_pointer>>

Seek ==
    /\ curr' \in 0..MaxOffset
    /\ IF curr' < lo \/ curr' >= lo + BuffSz THEN
            /\ diskPos' = (IF curr' < length THEN curr' ELSE length)
            /\ buff' = Take(file_content', lo', BuffSz)
            /\ lo' = (IF curr' < length THEN curr' - (curr' MOD BuffSz) ELSE length - (length MOD BuffSz))
       ELSE
            /\ UNCHANGED <<diskPos, buff, lo>>
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, file_content, file_pointer>>

SetLength ==
    /\ length' \in 0..MaxOffset
    /\ IF length' < length THEN
            /\ file_content' = Take(file_content, 1, length')
       ELSE
            /\ file_content' = Append(file_content, Take(<<0>>, length' - length))
    /\ dirty' = FALSE
    /\ UNCHANGED <<curr, lo, buff, diskPos, file_pointer>>

Read1 ==
    /\ curr < length
    /\ diskPos = (IF curr < lo \/ curr >= lo + BuffSz THEN lo ELSE curr)
    /\ buff' = Take(file_content', lo', BuffSz)
    /\ lo' = (IF curr < length THEN curr - (curr MOD BuffSz) ELSE length - (length MOD BuffSz))
    /\ file_pointer' = curr
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr>>

Write1 ==
    /\ curr <= length
    /\ diskPos = (IF curr < lo \/ curr >= lo + BuffSz THEN lo ELSE curr)
    /\ buff' = Append(SubSeq(buff, 1, curr - lo), <<file_content'[curr]>> \o SubSeq(buff, curr - lo + 2))
    /\ file_content'' = [file_content EXCEPT ![curr] = file_content'[curr]]
    /\ dirty' = TRUE
    /\ UNCHANGED <<length, lo, diskPos, file_pointer>>

Read ==
    /\ curr < length
    /\ diskPos = (IF curr < lo \/ curr >= lo + BuffSz THEN lo ELSE curr)
    /\ buff' = Take(file_content', lo', BuffSz)
    /\ lo' = (IF curr < length THEN curr - (curr MOD BuffSz) ELSE length - (length MOD BuffSz))
    /\ file_pointer' = curr
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr>>

WriteAtMost ==
    /\ curr <= length
    /\ diskPos = (IF curr < lo \/ curr >= lo + BuffSz THEN lo ELSE curr)
    /\ buff' = Append(SubSeq(buff, 1, curr - lo), file_content'[curr..Min(curr + Len(file_content') - 1, length)])
    /\ file_content'' = [file_content EXCEPT ![i \in curr..Min(curr + Len(file_content') - 1, length)] = file_content'[i]]
    /\ dirty' = TRUE
    /\ UNCHANGED <<length, lo, diskPos, file_pointer>>

Next ==
    \/ FlushBuffer
    \/ Seek
    \/ SetLength
    \/ Read1
    \/ Write1
    \/ Read
    \/ WriteAtMost

Spec == Init /\ [][Next]_<<dirty, length, curr, lo, buff, diskPos, file_content, file_pointer>>

Inv1 == length <= MaxOffset
Inv2 == /\ lo <= length
        /\ lo + BuffSz >= Min(curr, length)
Inv3 == Len(buff) = BuffSz \/ lo >= length
Inv4 == diskPos \in 0..MaxOffset
Inv5 == file_pointer \in 0..length

TypeOK ==
    /\ dirty \in BOOLEAN
    /\ length \in 0..MaxOffset
    /\ curr \in 0..MaxOffset
    /\ lo \in 0..MaxOffset
    /\ buff \in [1..BuffSz -> Nat]
    /\ diskPos \in 0..MaxOffset
    /\ file_content \in [0..MaxOffset -> Nat]
    /\ file_pointer \in 0..length

Invariants == Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv5 /\ TypeOK

Refinement ==
    LET AbstractFileContent == LogicalFileContent
        AbstractFilePointer == curr
    IN  Spec /\ [](AbstractFileContent' = [file_content EXCEPT ![file_pointer] = file_content'[file_pointer]])

Liveness ==
    \/ <>(\E seq \in Seq(Nat) : WF_seq(seq, FlushBuffer))
    \/ <>(\E seq \in Seq(Nat) : WF_seq(seq, Seek))

WF_seq(seq, act) == <<seq>> \in [0..Len(seq) -> {act}]

=============================================================================