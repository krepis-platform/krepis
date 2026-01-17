# Network Chaos Injection: Testing Under Real-World Conditions

## Why Perfect Networks Are Unrealistic

When you develop software on your laptop, you are working in an almost perfect environment. Your computer talks to your local server over the loopback interface. Network latency is measured in microseconds. Packets never get lost because they never actually leave your computer. Bandwidth is essentially unlimited because you are just moving data from one part of memory to another. This perfect environment is wonderful for development, but it creates a dangerous illusion.

The illusion is that networks are reliable and fast. In reality, production networks are neither. When your application runs in production, requests travel through multiple network hops between your users and your servers. Packets cross routers, switches, and firewalls. They might traverse undersea cables or satellite links. They compete with other traffic for limited bandwidth. Along this journey, things go wrong in countless ways.

Packets get lost. Router buffers overflow during traffic spikes, and some packets get dropped. Wireless connections lose packets when signal strength degrades. Congested links cannot handle all the traffic and drop packets randomly. Your application needs to handle these losses gracefully.

Latency varies unpredictably. Sometimes a request completes in ten milliseconds. Other times the same request takes two hundred milliseconds because it got queued behind other traffic. Occasionally latency spikes to several seconds when a routing change causes packets to take a longer path. Your application needs to handle this variability without breaking.

Bandwidth fluctuates. During peak hours, available bandwidth decreases as more users share the same connection. Mobile users experience bandwidth that varies with signal strength. Users on congested networks might have plenty of bandwidth for small requests but struggle with large responses. Your application needs to work well across this range of bandwidth conditions.

This is where chaos injection comes in. Chaos injection deliberately introduces these real-world network imperfections into your testing environment. Instead of testing your framework in a perfect network that will never exist in production, you test it in realistic network conditions that simulate what users will actually experience.

## Understanding Different Types of Network Chaos

Let me walk you through the different types of network chaos and explain what each one simulates and why it matters. Think of each type of chaos as simulating a different real-world scenario that your application will encounter.

Packet loss chaos simulates the situation where some percentage of your network packets simply disappear. They never reach their destination. The sender waits for a response that never comes. In a perfect network, packet loss is zero. But real networks lose packets for many reasons. Wireless connections lose packets when radio interference occurs. Congested routers drop packets when their buffers fill up. Faulty network equipment occasionally corrupts packets, making them undeliverable. A typical wired internet connection might lose zero point one percent of packets. A mobile connection might lose one to five percent. A degraded connection experiencing problems might lose ten percent or more.

When you inject packet loss into your tests, you are verifying that your framework handles these losses correctly. Does your HTTP client retry failed requests? Do your timeouts handle the case where a request never receives a response? Does your connection pool recover when connections fail? These questions only have meaningful answers when you test with realistic packet loss.

Latency injection chaos simulates the delay between sending a request and receiving a response. In a perfect local network, this delay is microseconds. But real networks introduce milliseconds or even seconds of delay. The delay has multiple components. There is propagation delay, which is the time for signals to physically travel through cables or wireless links. The speed of light imposes a minimum delay of about forty milliseconds for a round trip across the United States. There is queuing delay, which is the time packets spend waiting in router buffers when the network is busy. There is processing delay, which is the time routers spend examining packet headers and making forwarding decisions.

The total delay varies depending on many factors. Geographic distance matters enormously. A request from a user in Singapore to a server in Virginia will always have high latency because of the physical distance. Network congestion matters. During peak hours, queuing delays increase. The quality of the network path matters. Premium networks with well-connected routers have lower latency than networks that take circuitous routes.

When you inject latency into your tests, you verify that your framework remains responsive even when the network is slow. Do your timeouts give enough time for requests to complete over high-latency connections? Does your application show appropriate loading indicators rather than appearing frozen? Do you have retry logic that does not make the latency problem worse by retrying too aggressively?

Jitter chaos simulates the variability in latency. Real network latency is not constant. Sometimes a request completes in fifty milliseconds. The next identical request might take one hundred milliseconds. This variability is called jitter, and it comes from the same sources as base latency but changes moment to moment as network conditions fluctuate. Jitter is particularly problematic for applications that assume consistent timing. If your application uses timeouts that are barely longer than the average latency, jitter will cause timeouts to fire incorrectly when latency temporarily increases.

Latency spike chaos simulates the occasional extreme delays that happen in real networks. Most of the time, latency might be reasonable. But occasionally, something goes wrong. A routing change causes packets to take a much longer path. A brief network congestion event creates a spike in queuing delay. A failing network component causes retransmissions that multiply the effective delay. These spikes can be ten or more times the normal latency. Your application needs to handle these spikes without cascading failures.

Bandwidth throttling chaos simulates limited network capacity. While most modern networks have high bandwidth, not all users enjoy these conditions. Mobile users on 3G or 4G networks have limited bandwidth that varies with signal strength. Users in some geographic regions have limited bandwidth because infrastructure is less developed. Users sharing connections with many others experience reduced bandwidth during peak usage. When your application sends large responses over limited bandwidth, the transfer takes longer. Your timeouts need to account for this. Your application design might need to reduce response sizes or use compression.

## Configuring Chaos Injection: Starting Simple

Let me show you how to configure chaos injection, starting with simple examples and building up to more sophisticated scenarios. The key is to understand what each configuration parameter does and how it affects your tests.

The simplest form of chaos injection is adding a constant delay to all requests. This simulates a high-latency network connection without any other complications. Here is how you would configure this:

```rust
// Simulate a high-latency connection (like overseas users)
let chaos = NetworkChaosInjector::new(ChaosConfig {
    // Add 200ms of latency to every request
    base_latency_ms: 200,
    
    // No jitter, no packet loss, no spikes
    jitter_ms: 0,
    packet_loss_rate: 0.0,
    spike_probability: 0.0,
    spike_multiplier: 1.0,
});
```

This configuration is useful for testing whether your application works acceptably for users who are far away from your servers. Two hundred milliseconds is a realistic latency for transoceanic connections. If your application assumes fast responses and breaks when latency increases, this test will reveal the problem.

Next, let us add some variability to make the simulation more realistic. Real network latency is not constant. It varies from request to request as network conditions change. We model this variability with jitter:

```rust
// Simulate a high-latency connection with realistic variability
let chaos = NetworkChaosInjector::new(ChaosConfig {
    // Base latency of 200ms
    base_latency_ms: 200,
    
    // Add random jitter up to ±50ms
    // This means actual latency will be between 150ms and 250ms
    jitter_ms: 50,
    
    // Still no packet loss or spikes
    packet_loss_rate: 0.0,
    spike_probability: 0.0,
    spike_multiplier: 1.0,
});
```

Now each request will experience slightly different latency. This variability tests whether your application handles inconsistent response times gracefully. Applications that assume consistent timing might show confusing behavior when some requests complete quickly and others slowly.

Now let us add packet loss to simulate an unreliable network:

```rust
// Simulate a mobile network connection
let chaos = NetworkChaosInjector::new(ChaosConfig {
    // Mobile networks typically have higher latency than wired
    base_latency_ms: 80,
    jitter_ms: 40,
    
    // Mobile networks lose about 2% of packets
    packet_loss_rate: 0.02,
    
    // No latency spikes yet
    spike_probability: 0.0,
    spike_multiplier: 1.0,
});
```

This configuration simulates what users on mobile networks experience. The two percent packet loss rate means that about one in fifty requests will be lost. Your application must handle these losses by retrying the requests. If your retry logic is broken or missing, this test will expose the problem by showing many failed requests.

Finally, let us add latency spikes to simulate occasional extreme delays:

```rust
// Simulate a degraded network experiencing problems
let chaos = NetworkChaosInjector::new(ChaosConfig {
    base_latency_ms: 150,
    jitter_ms: 100,
    packet_loss_rate: 0.05, // 5% packet loss
    
    // 5% of requests will experience a latency spike
    spike_probability: 0.05,
    
    // When a spike occurs, latency increases 10x
    spike_multiplier: 10.0,
});
```

This configuration is aggressive. It simulates a network that is having significant problems. Five percent of requests are lost entirely. Five percent experience latency spikes that make them ten times slower than normal. If your application can handle these conditions gracefully, you can be confident it will handle most real-world network problems.

## How Chaos Injection Works Internally

Let me explain what happens inside the chaos injector when it processes a request. Understanding the internal mechanism will help you configure chaos more effectively and interpret the results correctly.

When a Virtual User is ready to send a request, it first consults the chaos injector. The chaos injector makes several decisions based on its configuration. First, it decides whether this request should be dropped entirely to simulate packet loss. The chaos injector generates a random number between zero and one. If this random number is less than the configured packet loss rate, the request is dropped. The Virtual User never sends the request at all. It waits for a timeout and then marks the request as failed. This accurately simulates what happens when a packet is lost on a real network.

If the request is not dropped, the chaos injector next calculates how much latency to add. It starts with the base latency. Then it adds a random amount of jitter. If jitter is configured as fifty milliseconds, the injector picks a random number between zero and fifty and adds it to the base latency. Then it decides whether to apply a latency spike. It generates another random number. If this number is less than the spike probability, a spike occurs. The calculated latency is multiplied by the spike multiplier. The final total latency is the base latency plus the random jitter, possibly multiplied by the spike factor.

Once the latency is calculated, the chaos injector tells the Virtual User to wait for this duration before sending the request. This simulates the network delay that would occur on a real network. After waiting, the Virtual User sends the request normally. The server receives it and processes it as usual. But from the Virtual User's perspective, the request took longer because of the injected delay.

Here is a simplified version of how this works in code:

```rust
impl NetworkChaosInjector {
    // Decide if we should drop this packet
    fn should_drop_packet(&mut self) -> bool {
        // Generate a random number between 0.0 and 1.0
        let random_value = self.rng.gen::<f64>();
        
        // If the random value is less than our packet loss rate,
        // we drop the packet
        random_value < self.config.packet_loss_rate
    }
    
    // Calculate the total latency for this request
    fn compute_latency(&mut self) -> Duration {
        // Start with the configured base latency
        let base = self.config.base_latency_ms;
        
        // Add random jitter
        let jitter = self.rng.gen_range(0..self.config.jitter_ms);
        
        // Decide if we should apply a latency spike
        let spike = if self.should_apply_spike() {
            // Multiply the base latency by the spike multiplier
            (base as f64 * self.config.spike_multiplier) as u64
        } else {
            0
        };
        
        // Total latency is base + jitter + spike
        Duration::from_millis(base + jitter + spike)
    }
    
    fn should_apply_spike(&mut self) -> bool {
        let random_value = self.rng.gen::<f64>();
        random_value < self.config.spike_probability
    }
}
```

This internal mechanism is deterministic when you use a seed. If you run the same test with the same seed, you get exactly the same sequence of packet drops, latency values, and spikes. This determinism is crucial for debugging. If you find a performance problem during a chaos test, you can reproduce it exactly by running the test again with the same seed.

## Predefined Chaos Profiles for Common Scenarios

Rather than configuring chaos parameters from scratch every time, it is helpful to have predefined profiles that represent common real-world scenarios. Let me describe several standard profiles and explain when to use each one.

The Baseline profile represents an ideal network with minimal imperfections. Use this profile when you want to establish a performance baseline without chaos. This tells you how your framework performs under the best possible conditions. You can then compare other chaos tests against this baseline to see how much impact network imperfections have.

```rust
// Baseline: Nearly perfect network
let baseline = ChaosConfig {
    base_latency_ms: 10,    // Just 10ms latency
    jitter_ms: 2,           // Minimal jitter
    packet_loss_rate: 0.0,  // No packet loss
    spike_probability: 0.0, // No spikes
    spike_multiplier: 1.0,
};
```

The Mobile Network profile simulates what users on 4G or 5G mobile connections experience. Mobile networks have higher latency than wired connections because signals travel through radio towers. They also have variable latency because signal strength changes. They lose more packets because wireless connections are inherently less reliable than wired connections.

```rust
// Mobile Network: Typical 4G/5G experience
let mobile = ChaosConfig {
    base_latency_ms: 80,    // Higher latency than wired
    jitter_ms: 40,          // Significant variability
    packet_loss_rate: 0.02, // 2% packet loss
    spike_probability: 0.05, // Occasional spikes
    spike_multiplier: 5.0,   // 5x latency when spikes occur
};
```

The Overseas User profile simulates what happens when users are geographically distant from your servers. The speed of light imposes a minimum latency for long distances. A round trip from North America to Asia takes at least one hundred fifty milliseconds just for the signal to travel. Add network processing delays and you get two hundred milliseconds or more.

```rust
// Overseas User: Transoceanic connection
let overseas = ChaosConfig {
    base_latency_ms: 200,   // Physical distance latency
    jitter_ms: 50,          // Network routing variability
    packet_loss_rate: 0.01, // Low packet loss on good infrastructure
    spike_probability: 0.02, // Occasional routing changes
    spike_multiplier: 3.0,   // Temporary routing inefficiencies
};
```

The Degraded Network profile simulates a network that is experiencing significant problems. This might represent a congested network during peak hours, a network with failing equipment, or a user on a very poor connection. This profile is intentionally aggressive to stress test your framework.

```rust
// Degraded Network: Significant problems
let degraded = ChaosConfig {
    base_latency_ms: 150,    // High latency
    jitter_ms: 100,          // Huge variability
    packet_loss_rate: 0.10,  // 10% packet loss
    spike_probability: 0.10, // Frequent spikes
    spike_multiplier: 10.0,  // Extreme delays when spikes occur
};
```

The 3G Mobile profile simulates older mobile networks that some users still rely on, particularly in areas with limited infrastructure. 3G networks are much slower than 4G or 5G and less reliable.

```rust
// 3G Mobile: Older mobile technology
let mobile_3g = ChaosConfig {
    base_latency_ms: 200,    // Much higher latency
    jitter_ms: 100,          // Very variable
    packet_loss_rate: 0.05,  // 5% packet loss
    spike_probability: 0.08, // Common spikes
    spike_multiplier: 8.0,   // Severe delays
};
```

## Running Chaos Tests and Interpreting Results

Now let me show you how to actually run chaos tests and what to look for in the results. The process is similar to running normal Virtual User tests, but you add chaos injection and pay special attention to metrics that reveal resilience problems.

Here is a complete example of running a chaos test:

```rust
// Step 1: Create your Virtual User scenario
let scenario = create_ecommerce_scenario();

// Step 2: Create a chaos injector with the profile you want to test
let chaos = NetworkChaosInjector::new(ChaosConfig::mobile_network());

// Step 3: Configure your Virtual User pool
let pool = VirtualUserPool::new(VuPoolConfig {
    total_vus: 1000,
    spawn_rate: 50,
    scenarios: vec![(scenario, 1.0)],
    seed: 42,
});

// Step 4: Attach the chaos injector to the pool
pool.with_chaos_injector(chaos);

// Step 5: Run the simulation
let handle = pool.start_simulation();
tokio::time::sleep(Duration::from_secs(130)).await; // Ramp up
tokio::time::sleep(Duration::from_secs(300)).await; // Run

// Step 6: Get the metrics
let metrics = pool.get_metrics();

// Step 7: Analyze the results
println!("=== Chaos Test Results (Mobile Network) ===");
println!("Total requests: {}", metrics.total_requests);
println!("Success rate: {:.2}%", metrics.success_rate * 100.0);
println!("Retry rate: {:.2}%", metrics.retry_rate * 100.0);
println!("Timeout rate: {:.2}%", metrics.timeout_rate * 100.0);
println!("p50 latency: {}ms", metrics.latency_p50_ms);
println!("p95 latency: {}ms", metrics.latency_p95_ms);
println!("p99 latency: {}ms", metrics.latency_p99_ms);
println!("Max latency: {}ms", metrics.max_latency_ms);
```

When you examine these results, you want to look for several key indicators. The success rate tells you what percentage of requests completed successfully despite the network chaos. A good framework should maintain a very high success rate even under chaos. If you configured two percent packet loss but your success rate is below ninety percent, something is wrong. Your retry logic might not be working correctly.

The retry rate tells you what percentage of requests needed to be retried. This should be roughly equal to your packet loss rate if your retry logic is working correctly. If you lose two percent of packets, you should retry about two percent of requests. If the retry rate is much higher than the packet loss rate, you might be retrying too aggressively, possibly because your timeouts are too short.

The timeout rate tells you what percentage of requests exceeded their timeout limit. Under chaos conditions, some requests will timeout because they encountered multiple failures or extreme latency spikes. A small timeout rate is acceptable. But if many requests are timing out, you might need to increase your timeout values or improve your retry strategy.

The latency percentiles tell you how chaos affected response times. Under chaos, latency will be higher than in perfect conditions. This is expected. What you want to verify is that the latency increase is reasonable and that your framework still meets its performance targets. If your service level objective says ninety-nine percent of requests should complete in under one hundred milliseconds, check whether your p99 latency is still below one hundred milliseconds even under chaos.

## What Good Chaos Test Results Look Like

Let me give you concrete examples of what good results look like versus bad results. This will help you understand whether your framework is handling chaos well.

Good results under mobile network chaos might look like this:

```
Total requests: 150,000
Success rate: 98.5%
Retry rate: 2.1%
Timeout rate: 0.3%
p50 latency: 95ms
p95 latency: 180ms
p99 latency: 320ms
```

These results show that despite two percent packet loss, the framework maintained a ninety-eight point five percent success rate. The retry rate is slightly higher than the packet loss rate, which is normal because some retries might also fail. The timeout rate is low, showing that most requests complete even when they need to be retried. The latency percentiles are higher than they would be without chaos, but they are reasonable for a mobile network scenario.

Bad results might look like this:

```
Total requests: 150,000
Success rate: 85.3%
Retry rate: 12.7%
Timeout rate: 8.2%
p50 latency: 450ms
p95 latency: 2,100ms
p99 latency: 5,800ms
```

These results reveal serious problems. The success rate is only eighty-five percent despite just two percent packet loss. The retry rate is much higher than the packet loss rate, suggesting the framework is retrying too aggressively or retrying requests that should not be retried. The timeout rate is high, indicating that many requests are taking too long. The latency percentiles are far too high, particularly the p99 latency of nearly six seconds. These results suggest problems with timeout configuration, retry logic, or both.

## Using Chaos Profiles to Test Different User Segments

An effective testing strategy is to run your Virtual User tests with multiple chaos profiles to simulate different user segments. Real users experience different network conditions depending on their location, device, and connection type. By testing with multiple profiles, you verify that your framework works well for all user segments, not just users with perfect connections.

Here is how you might structure this multi-profile testing:

```rust
// Define the chaos profiles you want to test
let profiles = vec![
    ("baseline", ChaosConfig::baseline()),
    ("mobile", ChaosConfig::mobile_network()),
    ("overseas", ChaosConfig::overseas_user()),
    ("degraded", ChaosConfig::degraded_network()),
];

// Run the same test with each profile
for (name, config) in profiles {
    println!("Running test with {} profile", name);
    
    let chaos = NetworkChaosInjector::new(config);
    let pool = create_test_pool();
    pool.with_chaos_injector(chaos);
    
    let metrics = run_simulation(pool).await;
    
    println!("Results for {}:", name);
    println!("  Success rate: {:.2}%", metrics.success_rate * 100.0);
    println!("  p99 latency: {}ms", metrics.latency_p99_ms);
    println!();
}
```

This approach gives you a comprehensive view of how your framework performs across different network conditions. You might discover that your framework works perfectly for users with good connections but struggles for users on mobile networks. Or you might find that overseas users experience acceptable latency but users on degraded networks experience too many failures. These insights help you prioritize improvements.

## Integrating Chaos Tests Into Continuous Integration

Just as you can integrate normal Virtual User tests into continuous integration, you can also integrate chaos tests. This ensures that your framework maintains its resilience as you make changes. Here is an example GitHub Actions workflow that runs chaos tests:

```yaml
name: Chaos Testing

on:
  pull_request:
    branches: [main]

jobs:
  chaos_test:
    strategy:
      matrix:
        chaos: [mobile, overseas, degraded]
    
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v3
      
      - name: Build framework
        run: cargo build --release
      
      - name: Start test server
        run: |
          ./target/release/krepis-server &
          sleep 5
      
      - name: Run chaos test
        run: |
          cargo run --bin kraken -- \
            --vus 1000 \
            --chaos-profile ${{ matrix.chaos }} \
            --duration 300 \
            --seed 42 \
            --report-format json > chaos_${{ matrix.chaos }}.json
      
      - name: Check resilience thresholds
        run: |
          success_rate=$(jq '.success_rate' chaos_${{ matrix.chaos }}.json)
          
          # Different thresholds for different chaos levels
          if [ "${{ matrix.chaos }}" == "mobile" ]; then
            threshold=0.98
          elif [ "${{ matrix.chaos }}" == "overseas" ]; then
            threshold=0.97
          else
            threshold=0.95
          fi
          
          if (( $(echo "$success_rate < $threshold" | bc -l) )); then
            echo "❌ Success rate ($success_rate) below threshold ($threshold)"
            exit 1
          fi
          
          echo "✅ Chaos test passed"
```

This workflow runs three different chaos tests on every pull request, each with a different chaos profile. Each profile has different success rate thresholds that are appropriate for that level of chaos. Mobile network chaos requires ninety-eight percent success. Overseas user chaos requires ninety-seven percent. Degraded network chaos requires ninety-five percent. If any test falls below its threshold, the pull request is rejected.

## The Philosophy of Chaos Testing

Let me close with some thoughts about why chaos testing matters and how it fits into the larger goal of building a reliable framework. Traditional testing assumes perfect conditions. You test your code with valid inputs, reliable dependencies, and perfect infrastructure. This testing is valuable, but it only tells you how your code behaves when everything works correctly.

Chaos testing takes the opposite approach. It assumes things will go wrong and tests how your code behaves when they do. Networks will be unreliable. Packets will be lost. Latency will spike. Bandwidth will be limited. These are not edge cases. These are normal operating conditions on the internet.

By testing under chaos, you build resilience into your framework from the beginning rather than discovering problems after deployment. You verify that your retry logic actually works. You confirm that your timeouts are set appropriately. You ensure that network problems do not cascade into application failures. This proactive approach to resilience is what separates production-ready frameworks from frameworks that only work in perfect conditions.

The ultimate goal is to reach a state where you can confidently tell users that your framework will work reliably for them regardless of their network conditions. Users on fast fiber connections will get excellent performance. Users on mobile networks will get acceptable performance. Even users on degraded networks will get a working application, albeit with reduced performance. This universal reliability is only achievable through rigorous chaos testing.