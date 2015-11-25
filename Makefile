all:
	javac -cp antlr-4.5.1-complete.jar:libs/commons-cli-1.3.1.jar */*.java

test:	all
	-~/.local/bin/lit tests

test-output: all
	-~/.local/bin/lit --max-time=1800 tests/__acceptancetests/part1 1> part1_lit_report.txt 2> part1_lit_error.txt
	-~/.local/bin/lit --max-time=1800 tests/__acceptancetests/part2 1> part2_lit_report.txt 2> part2_lit_error.txt
	python process_lit_results.py part1_lit_report.txt part2_lit_report.txt test_results_info.json
