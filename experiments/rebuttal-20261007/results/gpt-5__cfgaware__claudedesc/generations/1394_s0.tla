---- MODULE Github702 ----
VARIABLES y, z

fizzbuzz == 1

X == INSTANCE x_unchanged WITH
  x <- fizzbuzz,
  y <- y,
  z <- z

Spec == X!Spec
====