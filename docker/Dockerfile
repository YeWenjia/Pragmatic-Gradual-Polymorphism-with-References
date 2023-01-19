FROM coqorg/coq:8.10.2

WORKDIR /app

RUN git clone https://github.com/plclub/metalib && cd metalib/Metalib && git checkout 597fd7d && make install

RUN git clone https://github.com/YeWenjia/Pragmatic-Gradual-Polymorphism.git 