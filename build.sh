#!/bin/bash

set -eo "pipefail"

if [ -z ${ACL2} ];
then
    ACL2=../acl2/saved_acl2;
fi

cat src/convert.lisp | ${ACL2}
