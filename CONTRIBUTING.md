# Developer and Contributer Information

This document contains information about the developer workflow and how to contribute to the project.
Contributions are always very welcome, and we try our best to help you add your bugfixes and improvements to granule.
We want to make granule a welcoming community and a joyful place to collaborate, see our [CODE_OF_CONDUCT.md](./CODE_OF_CONDUCT.md) for the guidelines we ask all contributers to adhere to.

## Contents

  - [Issues and Pull Requests](#issues-and-pull-requests)
  - [Building with Stack](#building-with-stack)
  - [Testing](#testing)

## Issues and Pull Requests

For small fixes it is sufficient to just open a pull request.
Bigger features and bugs should first be reported on the issue tracker.

## Building with Stack

You can build individual executables like this

```console
stack build granule:exe:gr
stack build granule:exe:grc
stack build granule:exe:grepl
stack build granule:exe:grls
stack build granule:exe:grenchmark
```

and the same also works for the testsuites.

```console
stack build granule:test:frontend-spec
stack build granule:test:gr-golden
```

## Testing

Granule has an extensive testsuite, and new features and bugfixes should come ideally always come with tests.
[TESTING.md](./TESTING.md) contains information about how to run the testsuite, how to fix failing tests and how to add new tests.