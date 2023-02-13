# Testing

There are mainly three kinds of tests used in Granule:
  - doc string specfications (using `Test.DocTest`)
  - Units tests (which live in `frontend/tests/hspec`)
  - Integration tests via negative and positive test cases

Running tests

All tests can be run via

    stack test

Individual parts of the integration test suite can be run via inclusion or exclusion.

# Integration tests

Integration tests are handled by `.gr` files with `.gr.output` expected outputs.
Positive tests (which should succeed), live in `frontend/tests/cases/positive`.
Negative tests (which should fail), live in `frontend/tests/cases/negative`.

## Testing only certain subsets of tests

Test subsets are defined by the directory they are in, within `frontend/tests/cases`.

      stack test --ta "-p name"

will run only those tests in directory with `name`` as a directory in the path.

These can be stacked, e.g., 

      stack test --ta "-p simple -p indexed"

Alternatively, you can exlude subsets via a different mechanism, by adding
those directories to a file `.excludes` in the top-level directory (one
per line). For example if `.excludes` contains

      indexed

then running tests will exclude those in directories called `indexed`.