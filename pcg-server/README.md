# PCG Viewer Server

A web server for visualizing PCG (Program Control Graph) outputs. This server allows users to upload Rust files and view their PCG visualizations through a web interface.

## Prerequisites

- Rust and Cargo installed
- Access to the parent PCS project with `pcs_bin` and visualization files

## Setup

1. Make sure this project is in the same parent directory as the main PCS project
2. Build the project:
   ```bash
   cargo build
   ```

## Running the Server

1. Start the server:
   ```bash
   cargo run
   ```
2. Open your web browser and navigate to `http://localhost:4000`
3. Upload a Rust file through the web interface
4. After successful processing, you'll be automatically redirected to view the PCG visualization

The visualization remains available at its unique URL until the server is restarted
