#!/bin/bash

TIMEOUT_AMOUNT=10s
TIMEOUT=$(if which timeout >& /dev/null; then echo "timeout"; else echo "gtimeout"; fi)
PROVER=FO-prover

correct=0
timeout=0
total_A=0
total_B=0
total_C=0
score=0

for test in ./tests/C/t*.txt; do
	[ -e "$test" ] || continue
	
	if [[ "$test" =~ ^./tests/C/t(.*).txt ]]
	then
		n="${BASH_REMATCH[1]}"
	else
		printf "no match\n"
	fi
	
	echo -n "Running test C $n..."

	# run the solver with a timeout
	result=$(cat "$test" | $TIMEOUT -sHUP $TIMEOUT_AMOUNT ./"$PROVER")

	if (( $? == 0 )) ; then

		if (( $result == "1" )) ; then
			score=$((score - 2))
			echo "FAIL"
		elif (( $result == "0" )) ; then
			score=$((score + 0))
			echo "OK"
		else 
			# abort on unexpected output
			echo "unexpected output"
			return -1
		fi

	else
		score=$((score - 1))
		echo "TIMEOUT"
	fi

	total_C=$((total_C+1))
done

total=$((total_A + total_B + total_C))
echo "Score: $score/$total"
echo "$score" > "score.txt"
