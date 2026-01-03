use std::io::Result;

fn main() -> Result<()> {
    // 📌 proto 파일들이 있는 디렉토리 경로를 정확히 지정합니다.
    let proto_dir = "proto";
    
    prost_build::compile_protos(
        &[
            format!("{}/context.proto", proto_dir),
            format!("{}/error.proto", proto_dir),
        ],
        &[proto_dir], // proto include 경로
    )?;
    Ok(())
}