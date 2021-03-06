.POSIX:
SRC = preamble.lp
OBJ = $(SRC:.lp=.lpo)
.SUFFIXES:

all: $(OBJ)

install: clean all lambdapi.pkg
	lambdapi install lambdapi.pkg $(OBJ) $(SRC)

uninstall:
	lambdapi uninstall lambdapi.pkg

clean:
	rm -f $(OBJ)

.SUFFIXES: .lp .lpo

.lp.lpo:
	lambdapi check --gen-obj $<

.PHONY: all install uninstall clean
