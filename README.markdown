representable-tries
===================

[![Build Status](https://secure.travis-ci.org/ekmett/representable-functors.png?branch=master)](http://travis-ci.org/ekmett/representable-functors)

This package provides a simple function memoization scheme based on the notion of representable functors.

In category theory a representable functor (more pedantically a corepresentable functor) is one such that `f a` is isomorphic to `x -> a`. We choose the name `Representable` here because we are talking about haskell `Functor` instances, and they are all covariant, so this is the more natural notion of representability for Haskell.

Given the existence of representable functors, we can choose a `Traversable` representable functor that has our data type as a representation, and use it to memoize functions by building
a data structure that has one place to hold each answer for each possible argument.

Contact Information
-------------------

Contributions and bug reports are welcome!

Please feel free to contact me through github or on the #haskell IRC channel on irc.freenode.net.

-Edward Kmett
