# Stack build environment
FROM fpco/stack-build:lts-13.21 AS build
WORKDIR /granule
COPY . /granule/
RUN stack install --local-bin-path /usr/bin && stack clean --full
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip \
  && unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip \
  && mv z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04/bin/z3 /usr/bin/z3 \
  && rm -rf z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04*

# Get a stripped down ubuntu 16.04 for a lean distribution image
FROM ubuntu:xenial-20190515
WORKDIR /granule
COPY --from=build /usr/bin/gr /usr/bin/grin /usr/bin/z3 /usr/bin/
COPY --from=build /granule /granule
RUN apt-get update
# for GHC
RUN apt-get install -y libgmp10
# for Z3
RUN apt-get install -y libgomp1
# UTF8 support
RUN apt-get install -y locales \
  && sed -i -e 's/# en_US.UTF-8 UTF-8/en_US.UTF-8 UTF-8/' /etc/locale.gen \
  && dpkg-reconfigure --frontend=noninteractive locales \
  && update-locale LANG=en_US.UTF-8
ENV LANG en_US.UTF-8
# add .granule config file
RUN echo "--include-path /granule/StdLib --alternative-colors" > ~/.granule
CMD ["bash"]