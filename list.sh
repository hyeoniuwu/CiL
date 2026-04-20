#!/usr/bin/env bash

ROOT="Computability"
LIST="fine.txt"

if [[ ! -f "$LIST" ]]; then
  echo "Error: $LIST not found"
  exit 1
fi

TMP=$(mktemp)
sed 's|^\./||' "$LIST" > "$TMP"

total=0
fine=0

find "$ROOT" -type f | while read -r file; do
  rel="${file#./}"

  ((total++))

  if grep -Fxq "$rel" "$TMP"; then
    echo -e "\e[32m✓\e[0m $rel"
    ((fine++))
  else
    echo -e "\e[31m✗\e[0m $rel"
  fi
done

# The loop runs in a subshell, so we need a workaround to keep counts:
# rerun counting outside the pipe

total=$(find "$ROOT" -type f | wc -l)
fine=$(grep -Fx -f "$TMP" <(find "$ROOT" -type f | sed 's|^\./||') | wc -l)

echo "[$fine/$total]"

rm "$TMP"