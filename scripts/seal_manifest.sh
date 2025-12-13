#!/bin/sh
M="registry/manifests/temporal_paradox_manifest.txt"
TS=$(date -Iseconds)
SHA=$(sha256sum "$M"|awk '{print $1}')
echo "TS:$TS SHA256:$SHA" >> registry/digest.index
git add "$M" registry/digest.index registry/ledger.log
git commit -m "Canonized manifest TS:$TS SHA256:$SHA"
git push origin main
