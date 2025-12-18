# Testing

There are mainly three kinds of tests used in Granule:
  - doc string specfications (using `Test.DocTest`)
  - Units tests (which live in `frontend/tests/hspec`)
  - Integration tests via negative and positive test cases

Running tests

All tests can be run via

```console
> stack test
```

Individual parts of the suite can be run by package. For example, the following just runs all the unit tests
for the frontend:

```console
> stack test granule-frontend
```

Or individual unit tests files, e.g., the following runs the unit tests in just `TypeSpec`:

```console
> stack test granule-frontend --ta "--match \"Types\""
```

# Integration tests

Integration tests are handled by `.gr` files with `.gr.output` expected outputs.
Positive tests (which should succeed), live in `frontend/tests/cases/positive`.
Negative tests (which should fail), live in `frontend/tests/cases/negative`.

## Testing only certain subsets of tests

Test subsets are defined by the directory they are in, within `frontend/tests/cases`.

```console
> stack test --ta "-p name"
```

will run only those tests in directory with `name` as a directory in the path.

Alternatively, you can exlude subsets via a different mechanism, by adding
those directories to a file `.excludes` in the top-level directory (one
per line). For example if `.excludes` contains

```
indexed
```

then running tests will exclude those in directories called `indexed`.

## Updating golden tests

Golden files which end in `*.gr.output` can be automatically updated by passing the `--accept` option to the testsuite runner.

```console
> stack test --ta "--accept"
```

This can also be combined with the option to only run and update a single test:

```console
> stack test --ta "--accept -p name"
```
