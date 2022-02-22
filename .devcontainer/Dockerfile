ARG VARIANT="buster"
FROM mcr.microsoft.com/vscode/devcontainers/rust:0-${VARIANT}

# Add backports
RUN echo 'deb http://deb.debian.org/debian bullseye-backports main contrib non-free' >> /etc/apt/sources.list \
    && echo 'deb-src http://deb.debian.org/debian bullseye-backports main contrib non-free' >> /etc/apt/sources.list

# Install perf for 5.15 
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends \
    linux-perf-5.15 \
    # Link perf to a known location
    && ln -s /usr/bin/perf_5.15 /usr/bin/perf
