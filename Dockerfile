FROM fpco/stack-build:lts-13.21
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
RUN unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
RUN mv z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04/bin/z3 /usr/bin/z3
WORKDIR /granule
COPY . /granule
RUN stack install
CMD ["bash"]