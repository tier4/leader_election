make_coordination: src/coordination.c
	mkdir -p install
	gcc src/coordination.c include/coordination.h -o install/coordination -I include -W -Wall -Werror -g
	cp node_info.txt install/node_info.txt