+++
title = "Post 5: Beyond the Log File: Triggering C++ and Cocotb from SVA"
author = ["Enze Chi"]
date = 2025-12-30T12:18:00+11:00
tags = ["SVA", "FPGA", "Verification", "Verilator"]
categories = ["Verification", "SVA"]
draft = false
+++

## Introduction: Why Connect SVA to Software? {#introduction-why-connect-sva-to-software}

Seeing an error message in a terminal is fine for a human, but a self-checking testbench needs to know programmatically when an assertion fails. By using the Direct Programming Interface (DPI), we can call a C++ function directly from an SVA “Action Block.”


## The Action Block: The Trigger {#the-action-block-the-trigger}

Every assertion has two hidden slots called Action Blocks: the “pass” block and the “fail” block.

```verilog
a_protocol_check: assert property (p_my_rule)
  // Success Action Block
  begin
      $display(“Success!”);
  end
// Failure Action Block
else begin
    $error(“Failed!”);
end
```


## The DPI Bridge (Linking to C++/Python) {#the-dpi-bridge--linking-to-c-plus-plus-python}

Instead of just printing a message, we can call a C function. This function can then update a scoreboard in C++ or raise an exception in Cocotb.

Step A: Declare the C function in SystemVerilog
Inside your checker or a separate package, define the function you want to call.

```verilog
// Import the C function into SystemVerilog
import “DPI-C” function void notify_assertion_failure(string name, int cycle);
```

Step B: Call it from the SVA Action Block

```verilog
a_handshake: assert property (@(posedge clk) req |=> ack)
  else begin
      // Call the C function when the assertion fails
      notify_assertion_failure(“REQ_ACK_FAIL”, $time);
  end
```


## Handling the Event in C++ (Verilator) {#handling-the-event-in-c-plus-plus--verilator}

When Verilator compiles your code, it expects you to provide the implementation of notify_assertion_failure.

```C++
// In your C++ Testbench (sim_main.cpp)
extern “C” void notify_assertion_failure(const char* name, int cycle) {
  printf(“C++ Alert: Assertion %s failed at time %d!\n”, name, cycle);
  // You can also increment an error counter here
  my_testbench->error_count++;
}
```


## Integration with Cocotb (Python) {#integration-with-cocotb--python}

Cocotb works by wrapping the simulator. When using Cocotb, you usually have two choices for SVA:

Passive Monitoring
: Let SVA print to the console; Cocotb's log-scrubber will see the “Error” message and fail the test automatically.


Active Signaling
: Use a DPI function (as shown above) to toggle a “failure signal” in a helper module. Cocotb can “watch” this signal using await Edge(dut.assertion_fail_sig).


## Conclusion: Your Verification Superpowers {#conclusion-your-verification-superpowers}

You've now moved from writing simple code to building a cross-language verification framework.

SVA handles the complex timing logic.

DPI handles the communication.

C++/Python handles the test coordination and results.

This concludes the Foundations Series! You can find the example code [here](https://github.com/ezchi/sva-verilator-cocotb-starter).
