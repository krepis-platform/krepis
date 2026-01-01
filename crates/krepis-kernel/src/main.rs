use anyhow::Result;
use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper::{Request, Response, body::Incoming};
use hyper_util::rt::TokioIo; // 핵심 어댑터
use std::net::SocketAddr;
use tokio::net::TcpListener;
use tracing::{info, error};

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    let listener = TcpListener::bind(addr).await?;
    
    info!("🚀 Krepis Sovereign Kernel starting on {}", addr);
    info!("⚡ Hyper-Pingora Engine: ACTIVE");

    loop {
        let (stream, remote_addr) = listener.accept().await?;
        
        // TcpStream을 Hyper가 이해할 수 있는 TokioIo로 래핑합니다.
        let io = TokioIo::new(stream);

        tokio::spawn(async move {
            if let Err(err) = http1::Builder::new()
                .serve_connection(io, service_fn(handle_request))
                .await
            {
                error!("Connection error from {}: {}", remote_addr, err);
            }
        });
    }
}

async fn handle_request(
    _req: Request<Incoming>,
) -> Result<Response<String>, hyper::Error> {
    Ok(Response::new(
        "Krepis Sovereign Kernel v1.5.0 - Ready".to_string()
    ))
}