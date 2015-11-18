all:
	javac -cp antlr-4.5.1-complete.jar:libs/commons-cli-1.3.1.jar */*.java

test:
	~/.local/bin/lit tests
