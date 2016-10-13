FROM haskell:7.10.3
WORKDIR /opt/server

# Install the libraries
RUN sed -i "s/httpredir.debian.org/mirrors.tuna.tsinghua.edu.cn/" /etc/apt/sources.list
RUN apt-get update && \
    apt-get install -y libglpk36 glpk-utils libglpk-dev

# Add the local files to the image
COPY AmorJiSe_project /opt/server

RUN echo "stack ghci" > run.sh

#build the whole thing
RUN stack build

#make edit possible
RUN apt-get install -y emacs

ENV PATH /root/.cabal/bin:/root/.local/bin:/opt/cabal/1.24/bin:/opt/ghc/8.0.1/bin:/opt/happy/1.19.5/bin:/opt/alex/3.1.7/bin:$PATH

CMD ["/bin/bash -c 'stack ghci'"]