+++
title = "Post 3: Temporal Logic Unlocked: Sequence Repetition and Implication Operators"
author = ["Enze Chi"]
date = 2025-11-27T09:31:00+11:00
tags = ["SVA", "FPGA", "Verification", "Verilator"]
categories = ["Verification", "SVA"]
draft = true
+++

## Introduction: Sequences Define Time {#introduction-sequences-define-time}

In SystemVerilog Assertions, a **sequence** is a pattern of Boolean expressions that unfolds over one or more clock cycles. Sequences are how you define the temporal relationship between signals. Once a sequence is defined, a **property** uses it, often along with an **implication operator**, to establish a clear cause-and-effect rule.

---


## 1. Defining Sequences: The Building Blocks {#defining-sequences-the-building-blocks}

The primary tool for defining sequences is the **cycle delay operator** (**##**).


### A. Basic Delays (**##**): {#a.-basic-delays}

The **##** operator specifies the number of clock cycles that must pass between two expressions.

| Operator    | Description                          | Example                             |
|-------------|--------------------------------------|-------------------------------------|
| **##1**     | One clock cycle later                | **a ##1 b**                         |
| **##[n:m]** | Any number of cycles from `n` to `m` | **a ##[1:3] b** (1, 2, or 3 cycles) |
| **##N**     | Exactly `N` clock cycles later       | **a ##4 b**                         |


### 📝 Example 1: Request and Acknowledge Timing {#example-1-request-and-acknowledge-timing}

Define a sequence where a request (**req**) is followed by an acknowledge (**ack**) exactly **four cycles** later.

```verilog
sequence req_followed_by_ack;
    (req) ##4 (ack);
endsequence
```


### B. Repetition ([\*]): {#b.-repetition}

Repetition operators allow a part of a sequence to repeat for a specified number of cycles. They are incredibly useful for defining bus idle periods or waiting states.

| Operator | Description                                                                           | Example    | Notes                                           |
|----------|---------------------------------------------------------------------------------------|------------|-------------------------------------------------|
| [\*N]    | Repeat `N` times                                                                      | en [\*8]   | Signal en must be high for 8 consecutive cycles |
| [\*0:N]  | Repeat 0 up to `N` times                                                              | en [\*0:2] | Signal en is high 0, 1, or 2 times              |
| [=N]     | Non-consecutive repetition (out of scope for this post, but useful for sparse events) | req [=4]   |                                                 |


### 📝 Example 2: Wait State Definition {#example-2-wait-state-definition}

Define a sequence where signal `b` must occur 0 to 2 times, followed by signal `c`. This models a scenario where a block might wait for up to two cycles before proceeding.

```systemverilog
sequence wait_for_c;
    (b [*0:2]) ##1 (c);
endsequence
```

**Interpretation:** This sequence succeeds if **`c`** is true:

1.  ...on the next cycle (`##1`) after `b` was false (i.e., `b [*0]`).
2.  ...two cycles later (`b` was true for 1 cycle).
3.  ...three cycles later (`b` was true for 2 cycles).

---


## 2. Properties and Implication Operators {#properties-and-implication-operators}

A **property** ties a sequence to a clock and defines the assertion's overall behavior. Most properties use an **implication operator** to define the cause-and-effect relationship.

| Operator    | Name                        | Timing                                                                             | Usage           | Notes                                                                |
|-------------|-----------------------------|------------------------------------------------------------------------------------|-----------------|----------------------------------------------------------------------|
| &vert;-&gt; | **Overlap Implication**     | Antecedent and Consequent start evaluation at the **same** clock cycle.            | a &vert;-&gt; b | If `a` is true at time `T`, `b` must be true starting at time `T`.   |
| &vert;=&gt; | **Non-Overlap Implication** | Consequent evaluation starts at the clock cycle **after** the antecedent succeeds. | a &vert;=&gt; b | If `a` is true at time `T`, `b` must be true starting at time `T+1`. |


### 📝 Example 3: Implication Timing {#example-3-implication-timing}

If we assert that a request (`req`) must be followed by an acknowledge (`ack`) within 1 to 5 cycles:

```verilog
property p_req_ack_nonoverlap;
    @(posedge clk) (req) |=> ##[1:5] (ack); // Use |=> for clean 1-cycle delay
endproperty

property p_req_ack_overlap;
    @(posedge clk) (req) |-> ##[1:5] (ack); // Sequence effectively starts at the same cycle as req
endproperty
```

Using |=&gt; (Non-Overlap)
: If `req` is true at cycle `T`, the check for `ack` begins at cycle `T+1`. The earliest `ack` can be checked is cycle `T+2` (`##1`).

Using |-&gt; (Overlap)
: If `req` is true at cycle `T`, the check for `ack` begins at cycle `T`. The earliest `ack` can be checked is cycle `T+1` (`##1`).

**When to Use Which:**

-   Use **`|=>`** when your consequent sequence includes a **delay** (`##1` or more). It's cleaner.
-   Use **`|->`** when the consequent condition or sequence needs to be evaluated in the **same clock cycle** as the antecedent (e.g., checking a write enable is always accompanied by valid data in the same cycle).


### 📝 Example 4: The `disable iff` Construct {#example-4-the-disable-iff-construct}

A very important modifier is `disable iff`. This allows you to _temporarily pause_ the assertion checking during specific conditions, such as an active reset.

```verilog
property p_req_granted_with_reset;
    @(posedge clk) disable iff (!rst_n) (req) |-> ##[1:5] (grant);
endproperty
```

**Interpretation:** The assertion is suspended, and any pending checks are abandoned, whenever the active-low reset signal (`rst_n`) is low. This prevents false failures due to reset conditions.

---


## Conclusion and What's Next {#conclusion-and-whats-next}

Sequences (`##`, `[*]`) are the vocabulary of SVA, and properties (**|-&gt;**, **|=&gt;**, **disable iff**) are the grammar. You now have the fundamental tools to write powerful temporal checks!

In the next post, I move to **Phase 2: Professional SVA Methodology**. I'll learn the essential **`checker`** and **`bind`** constructs---the keys to keeping the SVA decoupled from the golden RTL.
