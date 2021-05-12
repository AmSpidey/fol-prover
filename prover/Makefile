.PHONY: all

all: FO-prover

FO-prover:
	stack build
	cp "`stack path --local-install-root`/bin/prover-exe" FO-prover

clean:
	rm FO-prover