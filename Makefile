JAVAC ?= javac
JAR ?= jar

PREFIX ?= $(shell brew --prefix 2>/dev/null || echo /usr/local)
BINDIR ?= $(DESTDIR)$(PREFIX)/bin

TARGET = magma
SRC = Magma.java

.PHONY: all test bench install uninstall clean

all: $(TARGET)

$(TARGET): $(SRC)
	@mkdir -p .build_tmp
	$(JAVAC) -d .build_tmp $(SRC)
	$(JAR) --create --file .build_tmp/magma.jar --main-class Magma -C .build_tmp .
	printf '#!/bin/sh\nexec java -jar "$$0" "$$@"\n' > $(TARGET)
	cat .build_tmp/magma.jar >> $(TARGET)
	chmod 755 $(TARGET)
	@rm -rf .build_tmp

test: $(TARGET)
	./$(TARGET) --test

bench: $(TARGET)
	./$(TARGET) --bench

install: $(TARGET)
	install -d "$(BINDIR)"
	install -m 755 $(TARGET) "$(BINDIR)/$(TARGET)"

uninstall:
	rm -f "$(BINDIR)/$(TARGET)"

clean:
	rm -rf $(TARGET) .build_tmp *.class *.jar
