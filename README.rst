indexed-set
===========

A simple wrapper around Sets from the containers package to keep track of
cardinality on the type level.

The design (especially for operations currently returning ``Bounds``) may be
subject to change. If you have any ideas as to how to make this nicer, feel free
to start a discussion on the issue tracker.

As it is, the library is largely untested, but since almost everything just
passes data through to containers, it should be somewhat usable in its current
form.
