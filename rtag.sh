#!/bin/bash -e
HASH=$(git log -n 1 --pretty=format:%H)
VER=4.${HASH:0:10}
echo "Tagging ${VER}"
git tag ${VER}
git push origin ${VER}