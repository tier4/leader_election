FROM ubuntu:22.04

# tzdataが対話モードになるのを防ぐ
ENV DEBIAN_FRONTEND=noninteractive

# 基本パッケージのインストール
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        procps \
        htop \
        stress-ng \
        iproute2 \
        iputils-ping \
        net-tools \
        git \
        build-essential \
        bash && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# デフォルトのコマンド
CMD ["bash"]
