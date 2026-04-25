#!/bin/bash
set -e

# 1. Rename directories and root files
mv papers/AccuracyDiversity papers/PRPKG24AccuracyDiversity
mv papers/AccuracyDiversity.lean papers/PRPKG24AccuracyDiversity.lean

mv papers/ProducerFairness papers/MBJG25ProducerFairness
mv papers/ProducerFairness.lean papers/MBJG25ProducerFairness.lean

mv papers/UserItemFairness papers/GCG24UserItemFairness
mv papers/UserItemFairness.lean papers/GCG24UserItemFairness.lean

mv papers/DiscretizationBias papers/DSWG24DiscretizationBias
mv papers/DiscretizationBias.lean papers/DSWG24DiscretizationBias.lean

mv papers/Monoculture papers/KR21Monoculture
mv papers/Monoculture.lean papers/KR21Monoculture.lean

# 2. Rewrite imports, namespaces, and internal file references
# We do this carefully with word boundaries (\b) in sed if possible, or exact strings
find papers/ -type f \( -name "*.lean" -o -name "*.tex" -o -name "*.md" \) -exec sed -i \
  -e 's/AccuracyDiversity/PRPKG24AccuracyDiversity/g' \
  -e 's/ProducerFairness/MBJG25ProducerFairness/g' \
  -e 's/UserItemFairness/GCG24UserItemFairness/g' \
  -e 's/DiscretizationBias/DSWG24DiscretizationBias/g' \
  -e 's/Monoculture/KR21Monoculture/g' \
  {} +

