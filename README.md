# Verifying a Lazy Concurrent List-Based Set Algorithm in Iris

We implemented the data structure presented in
"A Lazy Concurrent List-Based Set Algorithm" by Heller et al., in HeapLang,
defined logically atomic specifications for `add`, `remove`, and `contains`,
and proved the implementation of `add` and `remove` correct with regard to
those specifications in Iris. We also briefly discuss the difficulty of
verifying `contains` and an alternative way of setting up the invariant.

## Introduction

In "A Lazy Concurrent List-Based Set Algorithm", Heller et al.,
present a concurrent, list-based set algorithm in which insertion and
removal operations are optimistic, removal operations are lazy
(the target is first marked as removed, then physically unlinked) and
membership test operations are wait-free (every call finishes in a finite
number of steps) and never interfere with any concurrent operations.

The optimistic operations traverse the list without locking, locking only
the target entry and its predecessor, followed by a check for
synchronization conflicts. If no conflict has been detected, the operation
is executed. Otherwise, the operation is restarted.

While the algorithm has been studied in the context of formal verification
before, it has (to our knowledge) yet to be verified using separation logic.
This work implements the data structure and its methods in HeapLang, defines
the specification for the data structure and its method, and proves the
specifications for creating a new set, adding a key to the set, and removing
a key from the set using Iris. We do not prove the correctness of the
contains method, as it is out of scope for this project.

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for
installing the dependencies.  This requires the following two repositories:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
```

Once you have opam set up, run `make builddep` to install the right versions of
the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update, do `git pull`.  After an update, the development may fail to compile
because of outdated dependencies.  To fix that, please run `opam update`
followed by `make builddep`.