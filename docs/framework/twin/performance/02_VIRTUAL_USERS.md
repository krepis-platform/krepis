# Virtual Users: Simulating Real Human Behavior

## What Makes a User "Virtual"?

When we talk about Virtual Users, we are describing something that sounds simple but is actually quite sophisticated. A Virtual User is a piece of software that pretends to be a real person using your application. But the key word here is "pretends." A Virtual User does not just send random requests to your server. It behaves the way a real human being would behave, with all the quirks and patterns that make human behavior distinctly different from machine behavior.

To understand why this distinction matters, imagine two different ways of testing a coffee shop. In the first approach, you send people into the coffee shop as fast as possible, one after another, each person walking straight to the counter and ordering a coffee without pause. You measure how many coffees the shop can make per hour. This tells you something about the shop's maximum capacity, but it does not tell you how the shop handles real customers.

In the second approach, you send people in at realistic intervals. Each person walks in, looks at the menu for thirty seconds, decides what they want, waits in line, orders their coffee, waits for the coffee to be made, picks it up, and leaves. Some people order simple drinks. Others order complicated customized drinks. Some people pay with cash. Others use credit cards. This second approach gives you a much better picture of how the coffee shop actually performs under real conditions.

Virtual Users are the second approach applied to software testing. They do not just hammer your API endpoints. They follow realistic scenarios that mirror how real users interact with your application.

## The Anatomy of a Virtual User

Let me break down what makes up a Virtual User by looking at its components one at a time. Think of a Virtual User as having four essential parts, each serving a specific purpose.

First, every Virtual User has an identity. This is not just a number or an ID. A Virtual User has an email address, a password, maybe a user profile with preferences and history. This identity persists throughout the Virtual User's session. When the Virtual User logs in at the beginning of its scenario, it receives an authentication token. It carries this token with every subsequent request, just like a real user's web browser carries session cookies. This statefulness is crucial because it means the Virtual User can execute multi-step workflows that depend on previous actions.

Second, every Virtual User follows a scenario. A scenario is a detailed script that describes exactly what the Virtual User will do and in what order. The scenario might say the Virtual User logs in, then browses the product catalog for two seconds, then searches for a specific product, then adds it to their shopping cart, waits one second while reviewing the cart, and finally proceeds to checkout. Each step in this scenario is precisely defined, including what API endpoint to call, what data to send, and how long to wait before the next step.

Third, every Virtual User maintains context between steps. When a Virtual User completes one step of its scenario, it does not forget what happened. If the login step returned an authentication token, the Virtual User remembers that token and includes it in all subsequent requests. If the product search returned a list of product IDs, the Virtual User can randomly select one of those IDs to add to its cart. This context maintenance is what allows scenarios to be realistic rather than just sequences of independent requests.

Fourth, every Virtual User includes natural timing. Real people do not instantly click from one page to the next. They pause to read, to think, to decide what to do. These pauses are called "think time," and they are essential for realistic simulation. When a Virtual User's scenario says to wait two seconds after viewing the product list, that two-second pause represents the time a real user would spend scrolling through the list and choosing which product looks interesting. Without think time, Virtual Users would create unrealistic traffic spikes that bear no resemblance to production patterns.

## Building Your First Scenario: A Simple Example

Let me show you how to build a Virtual User scenario from the ground up. We will start with something very simple and gradually make it more realistic. This will help you understand the thinking process behind scenario design.

Suppose you are building an API for a blog platform. Users can read blog posts and leave comments. The simplest possible scenario would be a Virtual User that reads a single blog post. Here is how we might define that scenario.

```rust
// The simplest possible scenario: just read one blog post
let simple_read = UserScenario::SimpleRequest {
    // The API endpoint to call
    endpoint: "/api/posts/123".to_string(),
    
    // HTTP method
    method: HttpMethod::GET,
};
```

This scenario works, but it is not very realistic. A real user does not just read blog post number one hundred twenty-three specifically. A real user browses to find interesting posts. So let us make the scenario slightly more realistic by adding a browsing step first.

```rust
// More realistic: browse posts, then read one
let browse_and_read = UserScenario::MultiStep {
    steps: vec![
        // Step 1: Get the list of recent posts
        ScenarioStep {
            name: "browse_posts".to_string(),
            endpoint: "/api/posts".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: false,
            think_time_ms: 0,
        },
        
        // Step 2: Read a specific post
        // In a real scenario, we would randomly select from the browse results
        ScenarioStep {
            name: "read_post".to_string(),
            endpoint: "/api/posts/123".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: false,
            think_time_ms: 2000, // 2 seconds to scan the post list
        },
    ],
};
```

This is better. Now our Virtual User browses the post list before reading a specific post. Notice that we added two seconds of think time before the read step. This represents the time a real user would spend looking at the post titles and deciding which one to read.

But we can make this even more realistic. A real user does not always read post number one hundred twenty-three. They might read different posts depending on what catches their eye. Let us use template variables to make the scenario more dynamic.

```rust
// Even more realistic: randomly select which post to read
let dynamic_browse_and_read = UserScenario::MultiStep {
    steps: vec![
        ScenarioStep {
            name: "browse_posts".to_string(),
            endpoint: "/api/posts".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: false,
            think_time_ms: 0,
        },
        
        ScenarioStep {
            name: "read_post".to_string(),
            // This template variable will be replaced with a random post ID
            // from the previous browse response
            endpoint: "/api/posts/{{random_post_id}}".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: true, // Extract post IDs from browse response
            think_time_ms: 2000,
        },
    ],
};
```

Now our Virtual User behaves much more like a real user. It browses the post list, waits a couple of seconds while "reading" the titles, and then reads whichever post caught its attention. The specific post varies from one Virtual User to another, creating realistic diversity in the traffic pattern.

## Making Scenarios Stateful: The Login Example

Now that you understand basic scenarios, let me show you how to handle authentication and state. Many applications require users to log in before they can do anything interesting. Let us build a scenario where a Virtual User logs in and then performs some authenticated actions.

The key insight here is that the login step produces a result that subsequent steps need to use. When you log in, the server returns an authentication token. All your subsequent requests must include this token to prove you are logged in. This is exactly the kind of state that Virtual Users need to maintain.

```rust
let authenticated_scenario = UserScenario::MultiStep {
    steps: vec![
        // Step 1: Log in to get an authentication token
        ScenarioStep {
            name: "login".to_string(),
            endpoint: "/api/auth/login".to_string(),
            method: HttpMethod::POST,
            
            // The login request body includes email and password
            // We use template variables so each Virtual User has a unique identity
            body_template: Some(r#"{
                "email": "user-{{vu_id}}@example.com",
                "password": "test123"
            }"#.to_string()),
            
            uses_prev_response: false,
            think_time_ms: 0,
        },
        
        // Step 2: Browse posts (now authenticated)
        ScenarioStep {
            name: "browse_posts".to_string(),
            endpoint: "/api/posts".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            
            // This tells the Virtual User to include the auth token
            // from the login response in this request
            uses_prev_response: true,
            
            think_time_ms: 1000, // 1 second after logging in
        },
        
        // Step 3: Read a specific post (still authenticated)
        ScenarioStep {
            name: "read_post".to_string(),
            endpoint: "/api/posts/{{random_post_id}}".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: true, // Still using the auth token
            think_time_ms: 2000,
        },
    ],
};
```

Notice how the first step produces an authentication token, and then every subsequent step uses that token. The Virtual User maintains this token throughout its entire session. This is exactly how a real user's browser works with cookies or tokens. Once you log in, your browser includes your session token with every request until you log out.

## Complex Scenarios: E-Commerce Workflows

Now let me show you a more complex scenario that demonstrates many realistic patterns. Imagine you are building an e-commerce platform. A typical user journey might involve logging in, browsing products, adding items to a cart, and checking out. This workflow involves multiple types of state and several decision points.

```rust
let ecommerce_scenario = UserScenario::MultiStep {
    steps: vec![
        // Step 1: User logs in
        ScenarioStep {
            name: "login".to_string(),
            endpoint: "/api/auth/login".to_string(),
            method: HttpMethod::POST,
            body_template: Some(r#"{
                "email": "shopper-{{vu_id}}@example.com",
                "password": "shop123"
            }"#.to_string()),
            uses_prev_response: false,
            think_time_ms: 0,
        },
        
        // Step 2: Browse the product catalog
        // Real users often browse before buying anything
        ScenarioStep {
            name: "browse_catalog".to_string(),
            endpoint: "/api/products?category=electronics".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: true, // Include auth token
            think_time_ms: 3000, // 3 seconds browsing the catalog
        },
        
        // Step 3: View details of a specific product
        // Real users click on interesting products to learn more
        ScenarioStep {
            name: "view_product".to_string(),
            endpoint: "/api/products/{{random_product_id}}".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: true,
            think_time_ms: 5000, // 5 seconds reading product details
        },
        
        // Step 4: Add the product to cart
        // After reading details, user decides to buy
        ScenarioStep {
            name: "add_to_cart".to_string(),
            endpoint: "/api/cart/add".to_string(),
            method: HttpMethod::POST,
            body_template: Some(r#"{
                "product_id": "{{current_product_id}}",
                "quantity": 1
            }"#.to_string()),
            uses_prev_response: true,
            think_time_ms: 1000, // 1 second to click "add to cart"
        },
        
        // Step 5: View the cart
        // User wants to review what they are buying
        ScenarioStep {
            name: "view_cart".to_string(),
            endpoint: "/api/cart".to_string(),
            method: HttpMethod::GET,
            body_template: None,
            uses_prev_response: true,
            think_time_ms: 4000, // 4 seconds reviewing the cart
        },
        
        // Step 6: Proceed to checkout
        // User is satisfied and ready to buy
        ScenarioStep {
            name: "checkout".to_string(),
            endpoint: "/api/orders/create".to_string(),
            method: HttpMethod::POST,
            body_template: Some(r#"{
                "payment_method": "card",
                "shipping_address": "123 Test St"
            }"#.to_string()),
            uses_prev_response: true,
            think_time_ms: 8000, // 8 seconds entering payment info
        },
    ],
};
```

This scenario demonstrates several important patterns. First, notice how the think times vary depending on what the user is doing. Browsing a catalog takes three seconds. Reading product details takes five seconds. Entering payment information takes eight seconds. These durations are based on observing how real users behave. The think times make the scenario realistic rather than artificial.

Second, notice how each step builds on the previous steps. The user must log in before they can browse. They must browse before they can view a specific product. They must add something to their cart before they can check out. This sequential dependency is characteristic of real user workflows.

Third, notice how we use template variables like the current product ID and the virtual user ID. These variables make each Virtual User slightly different from every other Virtual User, creating natural diversity in the traffic pattern. Some Virtual Users will look at different products. Some will take slightly different amounts of time on each step. This diversity is important because real traffic is never perfectly uniform.

## Understanding Template Variables

Let me explain template variables in more detail because they are crucial for making scenarios flexible and realistic. A template variable is a placeholder in your scenario that gets replaced with actual data when the Virtual User executes the scenario. The most common template variables are:

The virtual user ID template variable, written as `{{vu_id}}`, gets replaced with the unique identifier of the Virtual User executing the scenario. If you have one thousand Virtual Users, they will have IDs from zero to nine hundred ninety-nine. This lets you create unique email addresses like `user-0@example.com`, `user-1@example.com`, and so on. Each Virtual User has its own distinct identity.

The timestamp template variable, written as `{{timestamp}}`, gets replaced with the current Unix timestamp in seconds. This is useful when you need to include temporal data in requests, such as when creating records that should have different creation times.

The random string template variable, written as `{{random_string}}`, gets replaced with a randomly generated alphanumeric string. This is useful when you need unique identifiers that do not have to follow a predictable pattern.

The previous response template variables are the most sophisticated. When you write something like `{{prev_response.token}}`, the Virtual User extracts the token field from the previous API response and inserts it here. This is how you chain steps together, using the output of one step as the input to the next step. You could also write `{{prev_response.products[0].id}}` to extract the ID of the first product from a list of products returned by a previous step.

Here is an example that shows how these template variables work together:

```rust
ScenarioStep {
    name: "create_comment".to_string(),
    endpoint: "/api/posts/{{prev_response.post_id}}/comments".to_string(),
    method: HttpMethod::POST,
    body_template: Some(r#"{
        "author": "user-{{vu_id}}",
        "text": "Great post! {{random_string}}",
        "timestamp": {{timestamp}}
    }"#.to_string()),
    uses_prev_response: true,
    think_time_ms: 3000,
}
```

When this step executes, the Virtual User replaces `{{prev_response.post_id}}` with the post ID from the previous step's response, replaces `{{vu_id}}` with its own unique ID, replaces `{{random_string}}` with a random string so each comment is slightly different, and replaces `{{timestamp}}` with the current time. The result is a completely unique comment that looks realistic.

## Configuring Virtual User Pools

Now that you understand how to define scenarios, let me explain how to create pools of Virtual Users and control how they execute. A Virtual User Pool is a collection of Virtual Users that execute scenarios concurrently. The pool manages spawning Virtual Users, distributing scenarios among them, and collecting metrics from their execution.

The most important configuration decision is how many Virtual Users to create and how fast to spawn them. You do not want to spawn all ten thousand Virtual Users simultaneously because that would create an unrealistic traffic spike. Real users arrive gradually over time. The spawn rate controls how many new Virtual Users appear per second.

```rust
let pool = VirtualUserPool::new(VuPoolConfig {
    // Total number of Virtual Users to create
    total_vus: 10_000,
    
    // Spawn rate: create 100 new Virtual Users per second
    // This means it takes 100 seconds to spawn all 10,000 users
    spawn_rate: 100,
    
    // Scenario distribution: assign scenarios to Virtual Users probabilistically
    // 70% of users follow the browsing scenario
    // 20% follow the purchasing scenario
    // 10% follow the commenting scenario
    scenarios: vec![
        (browsing_scenario, 0.7),
        (purchasing_scenario, 0.2),
        (commenting_scenario, 0.1),
    ],
    
    // Seed for deterministic random behavior
    // Using the same seed produces identical results every time
    seed: 42,
});
```

This configuration creates a realistic simulation where Virtual Users arrive gradually and follow different scenarios based on realistic distributions. If your analytics show that seventy percent of real users browse without buying, you configure your Virtual User pool to match that distribution.

The seed parameter is particularly important for debugging and continuous integration. When you run the same scenario with the same seed, you get exactly the same sequence of random decisions. The same Virtual Users will choose the same products, experience the same think times, and create the same traffic pattern. This determinism is invaluable when you need to reproduce a performance issue or verify that an optimization actually improved performance.

## Running a Load Test

Let me walk you through the complete process of running a load test with Virtual Users. This will help you understand how all the pieces fit together.

First, you create your scenario definitions. These are the scripts that describe what your Virtual Users will do. You might have several different scenarios representing different types of users or different workflows.

Second, you configure your Virtual User pool, specifying how many Virtual Users to create, how fast to spawn them, and which scenarios they should follow. You also set a seed to ensure reproducibility.

Third, you start the simulation and let it run for some duration. The typical pattern is to start the simulation, wait for a ramp-up period while Virtual Users spawn and begin their scenarios, run the full load for some steady state duration, and then gracefully shut down.

Fourth, you collect and analyze the metrics. The Virtual User pool tracks detailed statistics about every request, including success rates, latency percentiles, and error patterns.

Here is what this looks like in code:

```rust
// Step 1: Define your scenarios
let browsing = create_browsing_scenario();
let purchasing = create_purchasing_scenario();

// Step 2: Configure the pool
let pool = VirtualUserPool::new(VuPoolConfig {
    total_vus: 10_000,
    spawn_rate: 100,
    scenarios: vec![
        (browsing, 0.7),
        (purchasing, 0.3),
    ],
    seed: 42,
});

// Step 3: Start the simulation
let handle = pool.start_simulation();

// Wait for ramp-up: 100 seconds to spawn all users
// Plus another 30 seconds for them to get into their workflows
tokio::time::sleep(Duration::from_secs(130)).await;

// Run at full load for 5 minutes
tokio::time::sleep(Duration::from_secs(300)).await;

// Step 4: Collect metrics
let metrics = pool.get_current_metrics();

// Print the results
println!("Total requests: {}", metrics.total_requests);
println!("Success rate: {:.2}%", metrics.success_rate * 100.0);
println!("Average latency: {}ms", metrics.avg_latency_ms);
println!("p50 latency: {}ms", metrics.latency_p50_ms);
println!("p95 latency: {}ms", metrics.latency_p95_ms);
println!("p99 latency: {}ms", metrics.latency_p99_ms);

// Graceful shutdown
pool.stop_simulation().await;
```

The metrics tell you how your framework performed under this specific workload. The success rate shows what percentage of requests completed without errors. The latency percentiles show how fast your framework responded. The p50 latency is the median response time. Half of all requests were faster than this. The p95 latency means ninety-five percent of requests were faster than this. The p99 latency means ninety-nine percent of requests were faster than this.

These percentiles are important because they reveal the user experience. If your p50 latency is ten milliseconds but your p99 latency is one second, that means most users get fast responses but one percent of users experience terrible slowness. This kind of long tail latency can ruin user experience even if most requests are fast.

## Best Practices for Scenario Design

Let me share some principles that will help you design effective scenarios based on experience building performance tests for production systems.

First, always base your scenarios on real user behavior. The best way to design scenarios is to analyze your application's analytics data. Look at what real users actually do. What percentage browse without buying? What percentage create accounts but never complete their profiles? What percentage perform searches? Design your scenarios to match these real patterns.

Second, include realistic think times. Do not set every think time to zero. Real users pause to read, to decide, to type. These pauses are important because they create realistic traffic patterns. A good rule of thumb is to time yourself performing the actions manually and use those durations as think times.

Third, maintain proper state across requests. If your scenario includes login, make sure subsequent requests include the authentication token. If your scenario involves selecting items from a list, make sure you actually use the items that were in the list response, not hardcoded item IDs that might not exist.

Fourth, add realistic error handling. Real users sometimes make mistakes. They might try to add the same item to their cart twice. They might submit forms with invalid data. Your scenarios should include some of these error cases to ensure your framework handles them gracefully.

Fifth, use scenario distributions that match production. If seventy percent of your real traffic is read operations and thirty percent is writes, configure your Virtual User pool to match that distribution. Do not test with fifty-fifty read-write ratios unless that matches your actual usage.

Sixth, always set a seed for reproducibility. This makes your tests deterministic so you can reproduce issues and verify fixes. The only time you should run without a seed is when you are explicitly trying to explore different random variations.

## Integrating Virtual Users Into Continuous Integration

The real power of Virtual Users comes from integrating them into your continuous integration pipeline. Every time someone submits a pull request that changes your framework, you can automatically run a performance test with Virtual Users and verify that the change does not degrade performance.

Here is a simple example of how you might configure this in a GitHub Actions workflow:

```yaml
name: Performance Test

on:
  pull_request:
    branches: [main]

jobs:
  virtual_user_test:
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v3
      
      - name: Build framework
        run: cargo build --release
      
      - name: Start test server
        run: |
          ./target/release/krepis-server &
          sleep 5  # Wait for server to start
      
      - name: Run Virtual User simulation
        run: |
          cargo run --bin kraken -- \
            --vus 1000 \
            --spawn-rate 50 \
            --duration 300 \
            --scenario ecommerce \
            --seed 42 \
            --report-format json > metrics.json
      
      - name: Check performance thresholds
        run: |
          success_rate=$(jq '.success_rate' metrics.json)
          p99_latency=$(jq '.latency_p99_ms' metrics.json)
          
          if (( $(echo "$success_rate < 0.99" | bc -l) )); then
            echo "❌ Success rate ($success_rate) below 99%"
            exit 1
          fi
          
          if (( $(echo "$p99_latency > 100" | bc -l) )); then
            echo "❌ p99 latency ($p99_latency ms) exceeds 100ms"
            exit 1
          fi
          
          echo "✅ Performance tests passed"
```

This workflow automatically runs on every pull request. It builds your framework, starts a test server, runs a Virtual User simulation with one thousand users, and checks that the success rate is above ninety-nine percent and the p99 latency is below one hundred milliseconds. If either threshold is violated, the pull request is automatically rejected.

This automated performance verification prevents regressions from ever reaching your main branch. It gives you confidence that every change maintains or improves performance. Over time, this ensures your framework only gets better, never worse.

## The Relationship Between Virtual Users and Real Users

I want to close with an important philosophical point about what Virtual Users can and cannot tell you. Virtual Users are extremely good at simulating the mechanical aspects of user behavior. They send the right requests in the right order with realistic timing. They maintain session state correctly. They create traffic patterns that closely resemble real traffic.

But Virtual Users cannot perfectly simulate every aspect of real user behavior because real users are unpredictable in ways that go beyond mechanical patterns. Real users might abandon a purchase flow halfway through for reasons that have nothing to do with your application. Real users might click the wrong button by accident. Real users might have slow internet connections that you did not anticipate. Real users might use your application in creative ways you never imagined.

This means Virtual Users give you confidence that your framework can handle the expected patterns you designed for, but they cannot guarantee it will handle every possible real-world scenario. This is why you still need real user testing in addition to Virtual User simulation. But Virtual Users get you ninety percent of the way there. They catch the vast majority of performance issues before real users ever encounter them.

Think of Virtual Users as a very thorough dress rehearsal before opening night. The dress rehearsal helps you find and fix most problems. But opening night might still reveal a few issues the dress rehearsal missed. That is okay. The dress rehearsal was still valuable because it caught most problems. Virtual Users serve the same purpose for your framework.