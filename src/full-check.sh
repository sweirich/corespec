#!/bin/sh

# exit when any command fails
set -e

echo "____Corespec: full proof check____"
echo

echo "Coq version: `coqc -print-version`"
echo

echo "__Cleanup__"
(cd FcEtt && make clean)
echo

echo "__Build__"
(cd FcEtt && make)
echo


echo "Success"
