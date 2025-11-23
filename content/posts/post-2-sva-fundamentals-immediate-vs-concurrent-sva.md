+++
title = "Post 2: SVA Fundamentals: Immediate vs Concurrent SVA"
author = ["Enze Chi"]
date = 2025-11-23T12:08:00+11:00
tags = ["SVA", "FPGA", "Verification", "Verilator"]
categories = ["Verification", "SVA"]
draft = false
+++

## Introduction: The Two Pillars of SVA {#introduction-the-two-pillars-of-sva}

SystemVerilog Assertions (SVA) gives you two main ways to check your design's behavior, depending on the scope of time you need to cover:

1.  **Immediate Assertions:** For checks that must hold true _right now_, within a single simulation cycle.
2.  **Concurrent Assertions:** For checks that involve _time_, tracking a sequence of events over multiple clock cycles.

Understanding when and where to use each type is crucial for effective verification.


## 1. Immediate Assertions (The Procedural Check) {#immediate-assertions-the-procedural-check}

Immediate assertions behave much like a standard `if...else` statement in procedural SystemVerilog code (like inside an `always` block or `initial` block). They are evaluated **immediately** when the simulation control flow reaches them.


### 💡 Key Characteristics: {#key-characteristics}

Execution
: Procedural (evaluated based on execution flow).

Timing
: Zero-time delay. They check the condition based on the current values of signals in that time step.

Best Use Case
: Invariant checks in combinatorial logic, checking conditions at the start of a block, or ensuring that a function's arguments are valid.


### 📝 Example: Checking One-Hot Encoding {#example-checking-one-hot-encoding}

If a state machine's state register (`state_reg`) must always be in a one-hot configuration (only one bit high), an immediate assertion is perfect.

```verilog
always_comb begin
    // Standard procedural logic (combinatorial update)
    if (reset) next_state = IDLE;
    else next_state = calculate_next_state(state_reg, input_en);

    // Immediate Assertion: Check that state_reg is always one-hot.
    // If it fails, the simulator issues a fatal error.
    assert ($onehot(state_reg)) else $fatal(1, "State register is not one-hot! Value: %h", state_reg);
end
```

**Analogy:** An immediate assertion is like an alarm that goes off **the instant** a smoke detector detects smoke. It's an instant check of a static condition.

---


## 2. Concurrent Assertions (The Temporal Powerhouse) {#concurrent-assertions-the-temporal-powerhouse}

Concurrent assertions are the heart of SVA. They are designed to check **temporal properties** -- patterns and sequences that happen over multiple clock cycles.


### 💡 Key Characteristics: {#key-characteristics-1}

Execution
: Always active (concurrently) and implicitly sampled on a clock edge.

Timing
: Synchronous. They must be anchored to a clock event (e.g., `@(posedge clk)`).

Best Use Case
: Protocol checking (e.g., AXI, APB, custom handshakes), ensuring grants follow requests, or verifying timeout mechanisms.


### 📝 Example: Checking Request-Acknowledge Handshake {#example-checking-request-acknowledge-handshake}

We want to check that after a request signal (`req`) is asserted, an acknowledge signal (`ack`) must be asserted sometime between 1 and 3 clock cycles later.

```verilog
// Define the Property (The Rule)
property p_req_to_ack;
    // Anchor the check to the positive edge of the clock (clk)
    @(posedge clk) (req) |-> ##[1:3] (ack);
endproperty

// Instantiate the Assertion (Activate the Rule)
a_req_ack_check: assert property (p_req_to_ack)
    else $error("Request failed to receive acknowledge within 1 to 3 cycles.");
```

In the example above:

@(posedge clk)
: The **sampling event**. All signals are checked on the rising edge of `clk`.

(req)
: The **antecedent** (or starting condition). The assertion begins evaluation when `req` is true at the clock edge.

|-&gt;
: The **implication operator** (Non-Overlap, which we'll cover deeper next time). It means: _if_ the antecedent succeeds, _then_...

##[1:3] (ack)
: The **sequence/consequent**. `##` represents a clock cycle delay. This reads: **1 to 3** clock cycles later, the `ack` signal must be true.

**Analogy:** A concurrent assertion is like a security camera programmed to track a sequence: “If person A enters (cycle 1), then the safe must open (cycle 2) before the alarm goes off (cycle 5).” It tracks events over time.

---


## Comparison Summary Table {#comparison-summary-table}

| Feature        | Immediate Assertion                            | Concurrent Assertion                                |
|----------------|------------------------------------------------|-----------------------------------------------------|
| Execution      | Procedural (in `always`, `initial`, `task`)    | Concurrent (always active)                          |
| Timing         | Zero-time (evaluated immediately)              | **Synchronous** (sampled on a clock edge)           |
| Syntax         | `assert (condition) else action;`              | `assert property (@(clk) property_name);`           |
| Key Use        | Combinatorial checks, function argument checks | **Temporal protocol checks**, sequence verification |
| Requires Clock | No                                             | **Yes** (Must be clocked)                           |


## Conclusion and What's Next {#conclusion-and-whats-next}

Immediate assertions ensure instantaneous integrity, while concurrent assertions define complex temporal contracts. The vast majority of your SVA work will use the powerful **Concurrent** type.

In the next post, I will take a deep dive into the **Concurrent Assertion** syntax, focusing on **Sequences** and the crucial role of the **Implication Operators** (`|->` and `|=>`).
