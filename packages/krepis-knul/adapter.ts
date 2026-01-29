/**
 * Krepis KNUL - Network Adapter Layer
 *
 * Protocol-agnostic adapters for bridging external requests to the Krepis kernel.
 * Implements explicit context propagation and binary-first payload handling.
 *
 * Supports multiple protocols (HTTP, gRPC, QUIC) through pluggable adapter pattern.
 */

import type {
    FfiResponse,
    IKrepisContext,
  } from "../krepis-core/mod.ts";
  
  // ============================================================================
  // 1. ADAPTER CONFIGURATION TYPES
  // ============================================================================
  
  /**
   * Protocol enumeration for adapter selection
   */
  export enum AdapterProtocol {
    HTTP = "http",
    HTTPS = "https",
    QUIC = "quic",
    GRPC = "grpc",
  }
  
  /**
   * Base adapter configuration interface
   * Common settings for all adapter types
   */
  export interface IAdapterConfig {
    /** Protocol type */
    protocol: AdapterProtocol;
  
    /** Server host/address to bind to */
    host: string;
  
    /** Server port to listen on */
    port: number;
  
    /** Maximum concurrent connections allowed */
    maxConnections: number;
  
    /** Request timeout in milliseconds */
    requestTimeoutMs: number;
  
    /** Maximum payload size in bytes */
    maxPayloadBytes: number;
  
    /** Enable compression for payloads */
    enableCompression?: boolean;
  
    /** Custom headers or protocol-specific options */
    extra?: Record<string, unknown>;
  }
  
  /**
   * QUIC-specific configuration
   * Extends base config with TLS/crypto requirements
   */
  export interface QuicConfig extends IAdapterConfig {
    protocol: AdapterProtocol.QUIC;
  
    /** Path to TLS certificate file */
    certPath: string;
  
    /** Path to TLS private key file */
    keyPath: string;
  
    /** Optional: Path to root CA certificate for client verification */
    caPath?: string;
  
    /** Enable client certificate verification */
    requireClientAuth?: boolean;
  
    /** QUIC protocol version */
    quicVersion?: string;
  
    /** Connection idle timeout in milliseconds */
    idleTimeoutMs?: number;
  
    /** Maximum stream concurrency */
    maxStreamsConcurrent?: number;
  }
  
  /**
   * HTTP/HTTPS-specific configuration
   */
  export interface HttpConfig extends IAdapterConfig {
    protocol: AdapterProtocol.HTTP | AdapterProtocol.HTTPS;
  
    /** Path to TLS certificate (HTTPS only) */
    certPath?: string;
  
    /** Path to TLS private key (HTTPS only) */
    keyPath?: string;
  
    /** Keep-alive timeout in milliseconds */
    keepAliveTimeoutMs?: number;
  
    /** HTTP version (1.1, 2.0, 3.0) */
    httpVersion?: string;
  }
  
  /**
   * gRPC-specific configuration
   */
  export interface GrpcConfig extends IAdapterConfig {
    protocol: AdapterProtocol.GRPC;
  
    /** Path to TLS certificate */
    certPath?: string;
  
    /** Path to TLS private key */
    keyPath?: string;
  
    /** Enable gRPC reflection service */
    enableReflection?: boolean;
  
    /** Maximum message size in bytes */
    maxMessageSize?: number;
  }
  
  /**
   * Union type for all adapter configurations
   */
  export type AdapterConfig = QuicConfig | HttpConfig | GrpcConfig;
  
  // ============================================================================
  // 2. ADAPTER INTERFACE & TYPES
  // ============================================================================
  
  /**
   * Statistics snapshot for adapter monitoring
   */
  export interface AdapterStats {
    /** Total requests processed since startup */
    totalRequests: number;
  
    /** Currently active connections */
    activeConnections: number;
  
    /** Total bytes received */
    totalBytesIn: number;
  
    /** Total bytes sent */
    totalBytesOut: number;
  
    /** Average request latency in milliseconds */
    avgLatencyMs: number;
  
    /** Error count since startup */
    errorCount: number;
  
    /** Uptime in milliseconds */
    uptimeMs: number;
  }
  
  /**
   * Core adapter interface
   *
   * All protocol adapters must implement this contract.
   * Provides unified request handling with explicit context propagation.
   */
  export interface IAdapter extends Disposable {
    /**
     * Start the adapter
     *
     * Initializes network listeners, allocates resources, and begins
     * accepting external connections.
     *
     * @returns Promise that resolves when adapter is ready
     * @throws AdapterError if startup fails
     */
    start(): Promise<void>;
  
    /**
     * Stop the adapter gracefully
     *
     * Closes all active connections, releases network resources,
     * and prepares for shutdown. Should complete within reasonable timeout.
     *
     * @returns Promise that resolves when all resources are freed
     * @throws AdapterError if stop fails
     */
    stop(): Promise<void>;
  
    /**
     * Handle incoming request
     *
     * Processes raw binary payload within given context and returns
     * FFI response from kernel. Must preserve binary data without copying
     * where possible.
     *
     * All async operations within this method must propagate the context
     * explicitly to maintain traceability and determinism.
     *
     * @param ctx - Request context (request_id, tenant_id, trace_id, etc.)
     * @param payload - Raw binary request payload (no copying if possible)
     * @returns FFI response from kernel (error code + result buffer)
     * @throws AdapterError if handling fails
     */
    handle(ctx: IKrepisContext, payload: Uint8Array): Promise<FfiResponse>;
  
    /**
     * Get current adapter statistics
     *
     * @returns Snapshot of current performance and state metrics
     */
    getStats(): AdapterStats;
  
    /**
     * Check if adapter is currently running
     *
     * @returns true if adapter has been started and not stopped
     */
    isRunning(): boolean;
  
    /**
     * Get adapter configuration
     *
     * @returns Active configuration (may include runtime overrides)
     */
    getConfig(): AdapterConfig;
  }
  
  // ============================================================================
  // 3. QUIC ADAPTER IMPLEMENTATION (SKELETON)
  // ============================================================================
  
  /**
   * QUIC Protocol Adapter
   *
   * High-performance UDP-based transport for Krepis kernel communication.
   * Implements multiplexing, congestion control, and connection migration.
   *
   * Implements:
   * - IAdapter: Request handling contract
   * - Disposable: Resource cleanup on disposal
   */
  export class QuicAdapter implements IAdapter {
    /** Configuration object */
    private config: QuicConfig;
  
    /** Running state */
    private running = false;
  
    /** Statistics accumulator */
    private stats: AdapterStats = {
      totalRequests: 0,
      activeConnections: 0,
      totalBytesIn: 0,
      totalBytesOut: 0,
      avgLatencyMs: 0,
      errorCount: 0,
      uptimeMs: 0,
    };
  
    /** Startup timestamp */
    private startTime: number = 0;
  
    /** Disposed state */
    private disposed = false;
  
    /**
     * Create QUIC adapter with configuration
     *
     * @param config QUIC-specific configuration
     * @throws TypeError if config is invalid
     */
    constructor(config: QuicConfig) {
      if (!config) throw new TypeError("Config is required");
      if (!config.certPath) throw new TypeError("certPath is required");
      if (!config.keyPath) throw new TypeError("keyPath is required");
      if (config.port < 1 || config.port > 65535) {
        throw new TypeError("Invalid port number");
      }
      if (config.maxConnections < 1) {
        throw new TypeError("maxConnections must be >= 1");
      }
  
      this.config = config;
    }
  
    /**
     * Start QUIC server
     *
     * Initializes TLS context, creates socket listener,
     * and begins accepting QUIC connections.
     *
     * @throws AdapterError if startup fails
     */
    async start(): Promise<void> {
      this.assertNotDisposed();
      if (this.running) {
        throw new Error("Adapter is already running");
      }
  
      try {
        // TODO: Initialize QUIC listener
        // - Load TLS certificate and key
        // - Create QUIC socket
        // - Bind to configured host:port
        // - Set up connection acceptance loop
  
        this.running = true;
        this.startTime = Date.now();
        console.log(
          `[QUIC] Adapter started on ${this.config.host}:${this.config.port}`,
        );
      } catch (error) {
        throw new Error(`Failed to start QUIC adapter: ${error}`);
      }
    }
  
    /**
     * Stop QUIC server gracefully
     *
     * Closes all active connections and releases network resources.
     * Waits for in-flight requests to complete before returning.
     *
     * @throws AdapterError if graceful shutdown times out
     */
    async stop(): Promise<void> {
      this.assertNotDisposed();
      if (!this.running) return;
  
      try {
        // TODO: Graceful shutdown
        // - Signal all active connections to drain
        // - Wait for pending requests with timeout
        // - Close QUIC socket
        // - Release TLS context
  
        this.running = false;
        console.log("[QUIC] Adapter stopped");
      } catch (error) {
        throw new Error(`Failed to stop QUIC adapter: ${error}`);
      }
    }
  
    /**
     * Handle incoming QUIC request
     *
     * Processes binary payload with explicit context propagation.
     * Returns FFI response from kernel.
     *
     * Context fields (request_id, tenant_id, trace_id) are
     * threaded through all async operations for traceability.
     *
     * @param ctx - Canonical request context
     * @param payload - Raw binary request (typically 0-copy)
     * @returns FFI response with error code and result buffer
     * @throws AdapterError if handling fails
     */
    async handle(ctx: IKrepisContext, payload: Uint8Array): Promise<FfiResponse> {
      this.assertNotDisposed();
      if (!this.running) {
        throw new Error("Adapter is not running");
      }
  
      const startMs = Date.now();
  
      try {
        // TODO: Implementation
        // 1. Validate payload size
        // 2. Deserialize payload to request structure
        // 3. Call kernel FFI with context and request
        // 4. Serialize kernel response
        // 5. Update statistics (bytes in/out, latency)
        // 6. Return FFI response
  
        // Placeholder: must return FfiResponse
        throw new Error("QuicAdapter.handle() not yet implemented");
      } catch (error) {
        this.stats.errorCount++;
        const msg = error instanceof Error ? error.message : String(error);
        console.error(`[QUIC] Request failed: ${msg}`);
        throw error;
      } finally {
        const latencyMs = Date.now() - startMs;
        this.stats.totalRequests++;
        this.stats.avgLatencyMs = (
          this.stats.avgLatencyMs * (this.stats.totalRequests - 1) +
          latencyMs
        ) / this.stats.totalRequests;
      }
    }
  
    /**
     * Get current adapter statistics
     *
     * @returns Snapshot of metrics (requests, connections, bytes, latency)
     */
    getStats(): AdapterStats {
      this.assertNotDisposed();
      return {
        ...this.stats,
        uptimeMs: this.running ? Date.now() - this.startTime : 0,
      };
    }
  
    /**
     * Check if adapter is currently running
     *
     * @returns true if started and not stopped
     */
    isRunning(): boolean {
      this.assertNotDisposed();
      return this.running;
    }
  
    /**
     * Get current configuration
     *
     * @returns Active QUIC configuration
     */
    getConfig(): QuicConfig {
      this.assertNotDisposed();
      return this.config;
    }
  
    /**
     * Check if adapter is disposed
     */
    private assertNotDisposed(): void {
      if (this.disposed) {
        throw new ReferenceError("QuicAdapter has been disposed");
      }
    }
  
    /**
     * Dispose adapter and release all resources
     *
     * Implements Disposable protocol for use with `using` statement.
     * Calls stop() if still running.
     */
    async [Symbol.asyncDispose](): Promise<void> {
      if (this.disposed) return;
      this.disposed = true;
  
      try {
        if (this.running) {
          await this.stop();
        }
      } catch (error) {
        console.error(`Failed to dispose QuicAdapter: ${error}`);
      }
    }
  
    /**
     * Synchronous dispose (fallback for environments without async dispose)
     */
    [Symbol.dispose](): void {
      if (this.disposed) return;
      this.disposed = true;
  
      if (this.running) {
        // Synchronous stop - not ideal but allows graceful degradation
        console.warn("[QUIC] Synchronous disposal of running adapter");
        // TODO: Implement synchronous stop (non-blocking, signal shutdown)
      }
    }
  }
  
  // ============================================================================
  // 4. ADAPTER FACTORY & BUILDER
  // ============================================================================
  
  /**
   * Adapter factory for creating instances from configuration
   */
  export function createAdapter(config: AdapterConfig): IAdapter {
    switch (config.protocol) {
      case AdapterProtocol.QUIC:
        return new QuicAdapter(config as QuicConfig);
      // Additional protocol implementations would go here
      // case AdapterProtocol.HTTP:
      //   return new HttpAdapter(config as HttpConfig);
      // case AdapterProtocol.GRPC:
      //   return new GrpcAdapter(config as GrpcConfig);
      default:
        throw new Error(`Unsupported protocol: ${config.protocol}`);
    }
  }
  
  /**
   * Adapter builder for fluent configuration
   *
   * Example usage:
   * ```ts
   * const adapter = new AdapterBuilder()
   *   .protocol(AdapterProtocol.QUIC)
   *   .host("127.0.0.1")
   *   .port(4433)
   *   .certPath("./cert.pem")
   *   .keyPath("./key.pem")
   *   .build();
   * ```
   */
  export class AdapterBuilder {
    private config: Partial<AdapterConfig> = {
      protocol: AdapterProtocol.QUIC,
      host: "127.0.0.1",
      port: 4433,
      maxConnections: 10000,
      requestTimeoutMs: 30000,
      maxPayloadBytes: 10 * 1024 * 1024, // 10MB
    };
  
    protocol(p: AdapterProtocol): this {
      this.config.protocol = p;
      return this;
    }
  
    host(h: string): this {
      this.config.host = h;
      return this;
    }
  
    port(p: number): this {
      this.config.port = p;
      return this;
    }
  
    certPath(path: string): this {
      if (this.config.protocol === AdapterProtocol.QUIC) {
        (this.config as QuicConfig).certPath = path;
      } else if (this.config.protocol === AdapterProtocol.HTTPS) {
        (this.config as HttpConfig).certPath = path;
      }
      return this;
    }
  
    keyPath(path: string): this {
      if (this.config.protocol === AdapterProtocol.QUIC) {
        (this.config as QuicConfig).keyPath = path;
      } else if (this.config.protocol === AdapterProtocol.HTTPS) {
        (this.config as HttpConfig).keyPath = path;
      }
      return this;
    }
  
    maxConnections(max: number): this {
      this.config.maxConnections = max;
      return this;
    }
  
    requestTimeoutMs(ms: number): this {
      this.config.requestTimeoutMs = ms;
      return this;
    }
  
    maxPayloadBytes(bytes: number): this {
      this.config.maxPayloadBytes = bytes;
      return this;
    }
  
    extra(options: Record<string, unknown>): this {
      this.config.extra = options;
      return this;
    }
  
    build(): IAdapter {
      if (!this.config.protocol) {
        throw new Error("Protocol must be set");
      }
      if (!this.config.host || !this.config.port) {
        throw new Error("Host and port must be set");
      }
  
      return createAdapter(this.config as AdapterConfig);
    }
  }
  
  // ============================================================================
  // 5. ERROR TYPES
  // ============================================================================
  
  /**
   * Adapter-specific error class
   */
  export class AdapterError extends Error {
    constructor(
      message: string,
      readonly code: number = 5000, // Default to network error code
      readonly retryable: boolean = false,
    ) {
      super(message);
      this.name = "AdapterError";
    }
  }
  
  // ============================================================================
  // 6. EXPORT SUMMARY
  // ============================================================================
  
  export const VERSION = "0.1.0";
  export const ADAPTER_PROTOCOL_NAMES = Object.values(AdapterProtocol);