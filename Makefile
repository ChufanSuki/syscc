CXX=g++
CC=gcc
CFLAGS=-std=c11 -g -fno-common
# CXXFLAGS=-std=c++1y -g -Wextra -Werror -pedantic -fno-common
SRCS=$(wildcard *.cpp)
DEFS=$(wildcard *.hpp)
OBJS=$(SRCS:.cpp=.o)

syscc: $(OBJS)
	$(CXX) $(CFLAGS) -o $@ $^ $(LDFLAGS)

$(OBJS): syscc.hpp

format:
	@$(foreach var, $(SRCS), clang-format -i $(var);)
	@$(foreach var, $(DEFS), clang-format -i $(var);) 

test: syscc
	./test.sh

clean:
	rm -f syscc *.o *~ tmp*

.PHONY: test clean

