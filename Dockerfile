# Analysis image for the Ghidra/PyGhidra equivalence checker.
# Build and run through docker-compose.yml (see README).
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive \
    TZ=UTC

# Toolchain: clang drives the arm64/mips64 EqBench builds together with the
# GNU cross compilers; native gcc only serves pip builds and ad-hoc fixtures.
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    wget \
    unzip \
    git \
    gnupg \
    time \
    python3 \
    python3-pip \
    python3-dev \
    z3 \
    gcc \
    libc6-dev \
    clang \
    gcc-aarch64-linux-gnu \
    libc6-dev-arm64-cross \
    binutils-aarch64-linux-gnu \
    gcc-mips64-linux-gnuabi64 \
    libc6-dev-mips64-cross \
    binutils-mips64-linux-gnuabi64 \
    && rm -rf /var/lib/apt/lists/*

# Eclipse Temurin JDK 21 (Ghidra 12 requires Java 21)
RUN mkdir -p /etc/apt/keyrings && \
    wget -qO- https://packages.adoptium.net/artifactory/api/gpg/key/public | gpg --dearmor -o /etc/apt/keyrings/adoptium.gpg && \
    echo "deb [signed-by=/etc/apt/keyrings/adoptium.gpg] https://packages.adoptium.net/artifactory/deb jammy main" > /etc/apt/sources.list.d/adoptium.list && \
    apt-get update && apt-get install -y --no-install-recommends temurin-21-jdk && \
    rm -rf /var/lib/apt/lists/*

ENV JAVA_HOME=/usr/lib/jvm/temurin-21-jdk-amd64 \
    JAVA_TOOL_OPTIONS="-Djava.awt.headless=true"

# Ghidra 12.0.1, verified by SHA-256
ARG GHIDRA_URL=https://github.com/NationalSecurityAgency/ghidra/releases/download/Ghidra_12.0.1_build/ghidra_12.0.1_PUBLIC_20260114.zip
ARG GHIDRA_SHA256=85bd2990945f3a78df4d1e09f1bb1f40ab77be3bac62c6e7678900788c7f0f41
ENV GHIDRA_INSTALL_DIR=/opt/ghidra
ENV GHIDRA_HOME=${GHIDRA_INSTALL_DIR}
ENV PATH="${JAVA_HOME}/bin:${GHIDRA_HOME}/support:${PATH}"

RUN wget -q "${GHIDRA_URL}" -O /tmp/ghidra.zip && \
    echo "${GHIDRA_SHA256}  /tmp/ghidra.zip" | sha256sum -c - && \
    unzip -q /tmp/ghidra.zip -d /opt && \
    mv /opt/ghidra_12.0.1_PUBLIC "${GHIDRA_INSTALL_DIR}" && \
    rm /tmp/ghidra.zip

# Python dependencies are pinned in the repository so that git pull plus an
# image rebuild keeps the Python side of the environment stable.
COPY requirements-test.txt /tmp/requirements-test.txt
RUN pip3 install --no-cache-dir --upgrade pip && \
    pip3 install --no-cache-dir -r /tmp/requirements-test.txt && \
    rm /tmp/requirements-test.txt

# The container runs as the host user (docker-compose.yml passes the uid/gid)
# so that files written into the bind mount stay owned by that user; HOME is
# a writable scratch location for Ghidra's per-user config and caches.
ENV HOME=/tmp/home \
    PYTHONDONTWRITEBYTECODE=1
RUN mkdir -p /tmp/home && chmod 1777 /tmp/home

WORKDIR /workspace
CMD ["/bin/bash"]
