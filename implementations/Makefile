CC = gcc
CFLAGS = -pthread -Wall -Wextra
TARGET = leader_election
SRCS = coordination.c

.PHONY: all, clean

all: $(TARGET)

$(TARGET): $(SRCS)
	$(CC) $(CFLAGS) $(SRCS) -o $(TARGET)

clean:
	rm -f $(TARGET)