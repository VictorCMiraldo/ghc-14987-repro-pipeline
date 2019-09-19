#! /bin/bash
set -uo pipefail

total_mem=$(free --kilo | sed '2q;d' | sed 's/  */S/g' | cut -dS -f4)
allowed=$(( $total_mem * 95 / 100 ))

echo "Setting usable memory to 95% of the machine free mem ($allowed kbyte)"
ulimit -m $allowed

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

echo "Removing object files"
rm -f Processed/*.hi
rm -f Processed/*.o
