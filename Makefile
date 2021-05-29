CC=g++
CFLAGS=-std=c11 -g -fno-common
SRCS=$(wildcard *.cpp)
OBJS=$(SRCS:.cpp=.o)

syscc: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

$(OBJS): syscc.hpp

test: syscc
	./test.sh

clean:
	rm -f syscc *.o *~ tmp*

.PHONY: test clean

