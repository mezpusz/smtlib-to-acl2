#!/bin/bash

set -euo "pipefail"

echo "(exit)" | ./smtlib-to-acl2 $@
echo
