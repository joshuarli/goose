FROM ubuntu:24.04@sha256:534baea6a22c03a63003dbc8dbe78fe34bc0d7e595d9a9dc9834884ff530eb55

ENV DEBIAN_FRONTEND=noninteractive \
    GIT_OPTIONAL_LOCKS=0 \
    PYTHONDONTWRITEBYTECODE=1

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        clang \
        cmake \
        git \
        libclang-rt-dev \
        ninja-build \
        python3 \
    && rm -rf /var/lib/apt/lists/*

COPY . /src/goose
WORKDIR /src/goose

RUN cmake -S . -B build/fuzz-clang-glibc -G Ninja \
        -DCMAKE_BUILD_TYPE=Debug \
        -DCMAKE_C_COMPILER=clang \
        -DCMAKE_CXX_COMPILER=clang++ \
        -DGOOSE_FUZZ=ON \
        -DGOOSE_LIBTCC=OFF \
        -DGOOSE_GFX=OFF \
        -DGOOSE_AUDIO=OFF \
        -DGOOSE_PHYSICS=OFF \
        -DGOOSE_UI=OFF \
    && cmake --build build/fuzz-clang-glibc \
        --target goose goose_fuzz_parser goose_fuzz_pipeline -j2

VOLUME ["/work"]

CMD ["python3", "fuzz/driver.py", "smoke", "--exe", "build/fuzz-clang-glibc/goose", "--cc", "clang", "--output", "/work/fuzz"]
