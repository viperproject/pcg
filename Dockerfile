# Build stage for Rust projects
FROM rust:1.75 as rust-builder

# Install required dependencies
RUN apt-get update && apt-get install -y \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /usr/src/app

# Copy Rust project files
COPY . .

# Build PCS
RUN cargo build --release

# Build pcg-server
WORKDIR /usr/src/app/pcg-server
RUN cargo build --release

# Build stage for Node.js visualization
FROM node:20 as node-builder

WORKDIR /usr/src/app/visualization

# Copy visualization project files
COPY visualization/package*.json ./
RUN npm install

COPY visualization/ ./
RUN npm run build

# Final stage
FROM debian:bookworm-slim

# Install required runtime dependencies
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libgcc-12-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /usr/src/app

# Create tmp directory with proper permissions
RUN mkdir tmp && chmod 777 tmp

# Copy built artifacts from previous stages
COPY --from=rust-builder /usr/src/app/target/release/pcs_bin ./
COPY --from=rust-builder /usr/src/app/pcg-server/target/release/pcg-server ./
COPY --from=rust-builder /usr/src/app/pcg-server/templates ./templates
# Copy Rust runtime libraries
COPY --from=rust-builder /usr/local/rustup /usr/local/rustup
COPY --from=rust-builder /usr/local/cargo /usr/local/cargo
ENV PATH="/usr/local/cargo/bin:${PATH}"
ENV RUSTUP_HOME="/usr/local/rustup"
ENV CARGO_HOME="/usr/local/cargo"

# Set up visualization directory structure
RUN mkdir -p visualization/dist
COPY --from=node-builder /usr/src/app/visualization/dist ./visualization/dist/
COPY --from=node-builder /usr/src/app/visualization/index.html ./visualization/

# Enable full backtraces
ENV RUST_BACKTRACE=1

# Expose port for pcg-server
EXPOSE 3000

CMD ["./pcg-server"]
