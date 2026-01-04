/**
 * @file di/mod.ts
 * @version 1.0.0
 * 
 * Krepis Dependency Injection 모듈 진입점.
 */

export {
  InjectionToken,
  type ServiceIdentifier,
  type Constructor,
  type ServiceDescriptor,
  ServiceLifetime,
  type IScopedContainer,
  type IServiceProvider,
  type IServiceCollection,
  type ILogger,
  type ITelemetry,
  KREPIS_CONTEXT,
  LOGGER,
  TELEMETRY,
} from "./identifiers.ts";

export {
  ServiceCollection,
  createServiceCollection,
} from "./SovereignContainer.ts";