#! /bin/bash
set -uo pipefail

total_mem=$(free --kilo | sed '2q;d' | sed 's/  */S/g' | cut -dS -f2)
eighty_perc=$(( $total_mem * 80 / 100 ))

echo "Setting usable memory to 80% of the machine mem ($eighty_perc kbyte)"
ulimit -m $eighty_perc

echo "Available example files are:"
ls -1 Processed/ | awk '{ print NR " : " $0 }'
read -p "Which one would you like to compile? " ans

file=Processed/$(sed "${ans}q;d" <(ls -1 Processed/))

ghcopts="\
 -Wno-overlapping-patterns \
 -Wno-inaccessible-code \
 -Wno-incomplete-patterns \
 -Wno-incomplete-uni-patterns \
 -Wno-incomplete-record-updates \
"

echo -e "\nCompiling ${file} with:\n"
echo $ghcopts | sed 's/ /\n/g' | sed 's/^/  /'
echo ""

time ghc --make $ghcopts $file
