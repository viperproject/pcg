#!/bin/bash
set -e

docker build --target dev-profile -t pcg-dev .

docker run -p 4444:4444 --rm -it pcg-dev
