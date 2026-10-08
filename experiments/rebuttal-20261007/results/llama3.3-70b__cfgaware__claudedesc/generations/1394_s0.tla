---------------------------- MODULE Github702 ----------------------------
EXTENDS Integers, x_unchanged

VARIABLES y, z

fizzbuzz == 1

Instance == INSTANCE x_unchanged WITH x <- fizzbuzz

Spec == Instance!Spec

===================================