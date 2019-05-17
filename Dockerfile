# Stack build environment
FROM fpco/stack-build:lts-13.21 AS build
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip \
  && unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip \
  && mv z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04/bin/z3 /usr/bin/z3 \
  && rm -rf z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04*
WORKDIR /granule
COPY LICENSE \
  README.md \
  StdLib \
  examples \
  frontend \
  interpreter \
  repl \
  stack.yaml \
  /granule/
RUN stack install --local-bin-path /granule

# Get a stripped down ubuntu 16.04 for a lean distribution image
FROM ubuntu:xenial-20190515
RUN apt-get update && apt-get install -y libgmp10
COPY --from=build /granule/gr /granule/grin /usr/bin/z3 /usr/bin/
CMD ["bash"]