#!/bin/bash

set -euo "pipefail"

cat src/convert.lisp | ../acl2/saved_acl2
