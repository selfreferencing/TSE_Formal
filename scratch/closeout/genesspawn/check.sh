#!/bin/zsh
export PATH="$HOME/.elan/bin:$PATH"
cd ~/Desktop/TSE_Formal_chile
lake env lean SEKernel/CloseoutGenesSpawn.lean > scratch/closeout/genesspawn/build.log 2>&1
echo "EXIT $?"
grep -n ": error" scratch/closeout/genesspawn/build.log | head -20
echo "warnings: $(grep -c ': warning' scratch/closeout/genesspawn/build.log)"
