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
2. Open your web browser and navigate to `http://localhost:3000`
3. Upload a Rust file through the web interface
4. After successful processing, you'll be automatically redirected to view the PCG visualization

## How it Works

1. The server provides a simple web interface for file uploads
2. When a Rust file is uploaded, it:
   - Creates a temporary directory
   - Runs the PCS analysis with visualization enabled
   - Copies the visualization files to the temporary directory
   - Redirects you to view the results
3. The visualization remains available at its unique URL until the server is restarted

## Notes

- Only `.rs` files are accepted
- Each upload gets its own unique URL
- Temporary directories are not automatically cleaned up (they persist until server restart)
- The server runs on port 3000 by default
