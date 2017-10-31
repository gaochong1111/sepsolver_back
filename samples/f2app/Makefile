# Makefile in f2app
include ../../Make.properties
TARGET=runf2
SRC=./src/runf2.cpp

all:
	$(CC) -o $(TARGET) $(SRC) $(CPPFLAGS) -L$(DISTDIR) -ltest
	mv $(TARGET) ./bin

clean:
	rm -f ./src/*.o ./bin/$(TARGET)
