use axum::{
    #[allow(unused_imports)]
    body::Body,
    extract::Multipart,
    response::{Html, IntoResponse, Redirect, Response},
    routing::{get, post},
    Router,
};
use hyper::StatusCode;
use std::{
    backtrace::Backtrace,
    #[allow(unused_imports)]
    error::Error,
    fs,
    net::SocketAddr,
    #[allow(unused_imports)]
    path::{Path, PathBuf},
    process::Command,
};
#[allow(unused_imports)]
use tempfile::TempDir;
use tokio::net::TcpListener;
use tower_http::services::ServeDir;
use tracing::{debug, info, Level};
use tracing_subscriber::FmtSubscriber;
use uuid::Uuid;

#[tokio::main]
async fn main() {
    // Initialize tracing with debug level
    FmtSubscriber::builder().with_max_level(Level::DEBUG).init();

    // Ensure tmp directory exists
    fs::create_dir_all("tmp").expect("Failed to create tmp directory");

    let app = Router::new()
        .route("/", get(serve_upload_form))
        .route("/upload", post(handle_upload))
        .fallback_service(ServeDir::new("./").append_index_html_on_directories(false));

    info!("Starting server on 0.0.0.0:4000");
    let addr = SocketAddr::from(([0, 0, 0, 0], 4000));
    let listener = TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn serve_upload_form() -> impl IntoResponse {
    let html_content =
        fs::read_to_string("templates/index.html").expect("Failed to read upload form template");
    Html(html_content)
}

async fn handle_upload(multipart: Multipart) -> Response {
    match handle_upload_inner(multipart).await {
        Ok(response) => response,
        Err(e) => {
            let backtrace = Backtrace::capture();
            let error_with_trace = format!("Error: {}\n\nBacktrace:\n{}", e, backtrace);
            (StatusCode::INTERNAL_SERVER_ERROR, error_with_trace).into_response()
        }
    }
}

fn find_pcg_bin() -> Result<PathBuf, String> {
    let to_try = vec![
        PathBuf::from("pcg_bin"),
        PathBuf::from("../target/debug/pcg_bin"),
    ];

    for path in to_try {
        if path.exists() {
            tracing::info!("Found pcg_bin at {:?}", path);
            return Ok(path);
        }
    }

    Err("pcg_bin not found".to_string())
}

fn find_pcg_visualization_dir() -> Result<PathBuf, String> {
    let to_try = vec![
        PathBuf::from("visualization"),
        PathBuf::from("../visualization"),
    ];

    for path in to_try {
        if path.exists() {
            tracing::info!("Found visualization directory at {:?}", path);
            return Ok(path);
        }
    }

    Err("visualization directory not found".to_string())
}

async fn handle_upload_inner(mut multipart: Multipart) -> Result<Response, String> {
    // Create a new directory in ./tmp with a unique name
    let tmp_dir = PathBuf::from("tmp");
    let unique_dir = tmp_dir.join(Uuid::new_v4().to_string());
    fs::create_dir_all(&unique_dir).map_err(|e| e.to_string())?;
    debug!("Created temporary directory: {:?}", unique_dir);

    // Create data directory
    let data_dir = unique_dir.join("data");
    fs::create_dir(&data_dir).map_err(|e| e.to_string())?;

    // Debug all fields
    let mut code = String::new();
    let mut input_method = String::new();

    while let Some(field) = multipart.next_field().await.map_err(|e| e.to_string())? {
        let name = field.name().ok_or("Field missing name")?.to_string();
        debug!("Processing multipart field: {}", name);

        match name.as_str() {
            "input_method" => {
                input_method = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got input method: {}", input_method);
            }
            "code" => {
                code = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got code field content length: {}", code.len());
            }
            "file" => {
                if input_method == "file" {
                    let file_name = field.file_name().ok_or("No file name")?.to_string();

                    if !file_name.ends_with(".rs") {
                        return Ok((
                            StatusCode::BAD_REQUEST,
                            "Only Rust files (.rs) are accepted",
                        )
                            .into_response());
                    }

                    let contents = field.bytes().await.map_err(|e| e.to_string())?;
                    code = String::from_utf8(contents.to_vec()).map_err(|e| e.to_string())?;
                }
            }
            _ => {
                debug!("Unexpected field name: {}", name);
            }
        }
    }

    if code.is_empty() {
        return Ok((StatusCode::BAD_REQUEST, "No code content provided").into_response());
    }

    let file_path = unique_dir.join("input.rs");

    // Debug: Print the submitted code
    debug!("Submitted Rust code:\n{}", code);

    // Write the code to file
    fs::write(&file_path, &code).map_err(|e| e.to_string())?;

    // Debug: Verify file contents
    let saved_contents = fs::read_to_string(&file_path).map_err(|e| e.to_string())?;
    debug!("Saved file contents:\n{}", saved_contents);

    // Get absolute paths for both input file and data directory
    let abs_file_path = file_path.canonicalize().map_err(|e| e.to_string())?;
    let abs_data_dir = data_dir.canonicalize().map_err(|e| e.to_string())?;
    debug!("Using absolute file path: {:?}", abs_file_path);
    debug!("Using absolute data dir: {:?}", abs_data_dir);

    // Run pcg_bin with visualization flags
    let pcg_bin = find_pcg_bin()?;
    let output = Command::new(pcg_bin)
        .env("PCG_VISUALIZATION", "true")
        .env("PCG_VISUALIZATION_DATA_DIR", abs_data_dir.to_str().unwrap())
        .arg(abs_file_path)
        .output()
        .map_err(|e| e.to_string())?;

    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let error_message = format!(
            "PCG analysis failed:\n\nStdout:\n{}\n\nStderr:\n{}",
            stdout, stderr
        );
        return Ok((StatusCode::INTERNAL_SERVER_ERROR, error_message).into_response());
    }

    let visualization_dir = find_pcg_visualization_dir()?;

    // Copy visualization files
    copy_dir(visualization_dir.join("dist"), unique_dir.join("dist")).map_err(|e| e.to_string())?;

    fs::copy(
        visualization_dir.join("index.html"),
        unique_dir.join("index.html"),
    )
    .map_err(|e| e.to_string())?;

    // Redirect to the visualization
    let redirect_path = format!(
        "/tmp/{}/index.html",
        unique_dir.file_name().unwrap().to_str().unwrap()
    );
    Ok(Redirect::to(&redirect_path).into_response())
}

fn copy_dir(src: PathBuf, dst: PathBuf) -> std::io::Result<()> {
    if !dst.exists() {
        fs::create_dir(&dst)?;
    }

    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        let dst_path = dst.join(entry.file_name());

        if ty.is_dir() {
            copy_dir(entry.path(), dst_path)?;
        } else {
            fs::copy(entry.path(), dst_path)?;
        }
    }

    Ok(())
}
