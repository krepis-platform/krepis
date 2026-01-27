# Krepis Sovereign Development Environment for Firebase Studio (IDX)
# Reference: https://firebase.google.com/docs/studio/customize-workspace
{ pkgs, ... }: {
  # 안정적인 24.05 채널 사용
  channel = "stable-24.05";

  # 필요한 패키지들을 여기에 정의합니다.
  packages = [
    # Rust 관련 툴체인
    pkgs.rustup
    pkgs.gcc        # Rust 컴파일 시 필요한 링커
    
    # Deno 및 런타임
    pkgs.deno
    
    # Java (TLA+ 실행용)
    pkgs.jdk17
    
    # 유틸리티 (기존 wget 대체 및 환경 구성용)
    pkgs.wget
    pkgs.curl
    pkgs.gnumake
  ];

  # 환경 변수 설정 (Deno 및 Rust 경로)
  env = {
    RUST_BACKTRACE = "1";
  };

  idx = {
    # VS Code 익스텐션 이식
    extensions = [
      "rust-lang.rust-analyzer"
      "denoland.vscode-deno"
      "tamasfe.even-better-toml"
      "serayuzgur.2108" # TLA+ 익스텐션 (추가 추천)
    ];

    # 워크스페이스 생명주기 훅
    workspace = {
      # 워크스페이스가 처음 생성될 때 실행 (기존 postCreateCommand 역할)
      onCreate = {
        # Rust 툴체인 설치 및 TLA+ 도구 다운로드
        setup-rust = "rustup default stable && rustup component add rust-analyzer";
        setup-tla = "mkdir -p $HOME/bin && wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -P $HOME/bin";
      };
      
      # 워크스페이스가 시작될 때마다 실행
      onStart = {
        # 필요 시 서버 자동 실행 등의 명령어를 넣을 수 있습니다.
      };
    };

    # 미리보기 기능 (백엔드/웹 API 테스트용)
    previews = {
      enable = true;
      previews = {
        # 예: KNUL 프로토콜 테스트용 로컬 서버 미리보기
        # server = {
        #   command = ["cargo" "run"];
        #   manager = "web";
        # };
      };
    };
  };
}