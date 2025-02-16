#!/bin/bash
set -e

docker build -t pcg_bin -f Dockerfile .

# The -p flag exposes the memory profiling port
# --entrypoint overrides the default command to run pcs_bin instead of the server
# -v mounts the current directory into the container at /app
docker run -p 4444:4444 -v "$(pwd):/app" --workdir /app --entrypoint /usr/src/app/pcs_bin pcs_bin "$@"
