SOURCES = $(shell find src -type f -name "*.java")
CLASSES = $(patsubst src/%.java,out/%.class,$(SOURCES))

all: $(CLASSES)

run:
	java -Xms256m -Xmx512m -cp out Main

out/%.class: src/%.java
	javac -cp src $< -d out
