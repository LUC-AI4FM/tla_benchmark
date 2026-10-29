```tla
 node eventually completes a checkpoint.
EventuallyCheckpointCompletes == <>(\E n \in Node : LastCheckpoint[n] > 0)

=========================================================================================
```