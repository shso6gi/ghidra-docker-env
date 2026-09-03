FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# software-properties-common をインストールして PPA を追加
RUN apt-get update && apt-get install -y \
    software-properties-common \
    && add-apt-repository ppa:ubuntu-toolchain-r/test -y \
    && apt-get update && apt-get install -y \
    wget \
    unzip \
    curl \
    git \
    python3 \
    python3-pip \
    python3-venv \
    python3-dev \
    z3 \
    gcc-13 \
    g++-13 \
    make \
    time \
    ca-certificates \
    gnupg \
    clang \
    # ========================================
    # ARM64 クロスコンパイラ
    # ========================================
    gcc-aarch64-linux-gnu \
    g++-aarch64-linux-gnu \
    libc6-dev-arm64-cross \
    # ========================================
    # MIPS64 クロスコンパイラ
    # ========================================
    gcc-mips64-linux-gnuabi64 \
    g++-mips64-linux-gnuabi64 \
    libc6-dev-mips64-cross \
    # ========================================
    # Clang クロスコンパイル用追加パッケージ
    # ========================================
    binutils-aarch64-linux-gnu \
    binutils-mips64-linux-gnuabi64 \
    && rm -rf /var/lib/apt/lists/*

# GCC 13 をデフォルトに設定
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-13 100 && \
    update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-13 100 && \
    update-alternatives --install /usr/bin/cc cc /usr/bin/gcc-13 100 && \
    update-alternatives --install /usr/bin/c++ c++ /usr/bin/g++-13 100

# Eclipse Temurin JDK 21 のインストール
RUN mkdir -p /etc/apt/keyrings && \
    wget -O - https://packages.adoptium.net/artifactory/api/gpg/key/public | gpg --dearmor -o /etc/apt/keyrings/adoptium.gpg && \
    echo "deb [signed-by=/etc/apt/keyrings/adoptium.gpg] https://packages.adoptium.net/artifactory/deb jammy main" | tee /etc/apt/sources.list.d/adoptium.list && \
    apt-get update && \
    apt-get install -y temurin-21-jdk && \
    rm -rf /var/lib/apt/lists/*

# JAVA_HOME の設定
ENV JAVA_HOME=/usr/lib/jvm/temurin-21-jdk-amd64
ENV PATH="${JAVA_HOME}/bin:${PATH}"

# Ghidra 12.0.1 のダウンロードとインストール
ARG GHIDRA_URL=https://github.com/NationalSecurityAgency/ghidra/releases/download/Ghidra_12.0.1_build/ghidra_12.0.1_PUBLIC_20260114.zip
ARG GHIDRA_SHA256=85bd2990945f3a78df4d1e09f1bb1f40ab77be3bac62c6e7678900788c7f0f41
ENV GHIDRA_INSTALL_DIR=/opt/ghidra

RUN wget -q "${GHIDRA_URL}" -O /tmp/ghidra.zip && \
    if [ -n "${GHIDRA_SHA256}" ]; then echo "${GHIDRA_SHA256}  /tmp/ghidra.zip" | sha256sum -c -; fi && \
    unzip -q /tmp/ghidra.zip -d /opt && \
    mv /opt/ghidra_12.0.1_PUBLIC ${GHIDRA_INSTALL_DIR} && \
    rm /tmp/ghidra.zip

# Ghidra 環境変数の設定
ENV GHIDRA_HOME=${GHIDRA_INSTALL_DIR}
ENV PATH="${GHIDRA_HOME}:${GHIDRA_HOME}/support:${PATH}"

# Python dependencies are pinned in the repository so git pull plus image
# rebuild keeps the Python side of the validation environment stable.
COPY requirements-test.txt /tmp/requirements-test.txt
RUN python3 -m pip install --upgrade pip && \
    pip3 install --no-cache-dir -r /tmp/requirements-test.txt && \
    rm /tmp/requirements-test.txt

WORKDIR /workspace

CMD ["/bin/bash"]

ENV JAVA_TOOL_OPTIONS="-Djava.awt.headless=true"
