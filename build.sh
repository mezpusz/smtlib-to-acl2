#!/bin/bash

set -euo "pipefail"

cat convert.lisp | ../acl2/saved_acl2
