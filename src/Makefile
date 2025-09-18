CPP = g++
CPPFLAGS = -O3 -std=c++20 -fopenmp

itercnc: itercnc.o
	${CPP} ${CPPFLAGS} itercnc.o -o itercnc

itercnc.o: itercnc.cpp
	${CPP} ${CPPFLAGS} itercnc.cpp -c

clean:
	rm -rf *.o
	rm itercnc
	clear
