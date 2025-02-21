#!/bin/bash
set -e
docker build -t pcg_server -f Dockerfile .
docker run -p 4000:4000
