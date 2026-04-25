#!/bin/bash
set -e

# 1. Rename files and directories
mv EconCSLean EconCSLib
mv EconCSLean.lean EconCSLib.lean

# 2. Universal find-and-replace for EconCSLean -> EconCSLib
# We target specific extensions to avoid corrupting binaries or the .git folder
find . -type f \( -name "*.lean" -o -name "*.md" -o -name "*.toml" -o -name "*.tex" \) -exec sed -i 's/EconCSLean/EconCSLib/g' {} +

