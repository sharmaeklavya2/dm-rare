FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive

# Change system encoding from latin1 to UTF-8 (matters for vim)
ENV LANG=C.utf8

RUN apt-get update && apt-get install -y \
    curl git build-essential vim-tiny \
    nodejs npm python3 \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
# --default-toolchain none: don't download a toolchain at build time;
# the lean-toolchain file in the project will pin the exact version.
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- --default-toolchain none -y
ENV PATH="/root/.elan/bin:$PATH"

# Claude Code is not installed here: the devcontainer feature
# (ghcr.io/anthropics/devcontainer-features/claude-code) installs it.

# Disable git credential helper to prevent credential leakage into the container
RUN git config --global credential.helper ""

COPY vimrc /root/.vimrc

WORKDIR /workspace
