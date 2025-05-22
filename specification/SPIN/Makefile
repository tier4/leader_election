pan.c: leader_election.pml
	spin -a $<

pan: pan.c
	gcc -O3 -DCOLLAPSE -o $@ $<

run: pan
	rm -f *.trail
	./pan -a -n

trail:
	spin -plgrc -t leader_election.pml

clean:
	rm -f pan.* *.trail pan *.tmp