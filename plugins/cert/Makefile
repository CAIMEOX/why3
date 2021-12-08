all:
	make -C ../..

test:
	ls tests | grep .*mlw | cut -d. -f1 | xargs -I @ bash -c "echo; echo | awk '{ print toupper(\"@\") }'; ../../bin/why3 replay tests/@; echo; echo"

