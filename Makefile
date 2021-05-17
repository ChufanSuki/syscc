CFLAGS=-std=c11 -g -static

chibicc: main.o
	$(CC) -o $@ $? $(LDFLAGS)

test: syscc
	./test.sh

clean:
	rm -f syscc *.o *~ tmp*

.PHONY: test clean

