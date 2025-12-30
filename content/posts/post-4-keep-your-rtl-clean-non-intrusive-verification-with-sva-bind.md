+++
title = "Post 4: Keep Your RTL Clean: Non-Intrusive Verification with SVA Bind"
author = ["Enze Chi"]
date = 2025-12-29T21:04:00+11:00
tags = ["SVA", "FPGA", "Verification", "Verilator"]
categories = ["Verification", "SVA"]
draft = true
+++

## Introduction: Why Decouple? {#introduction-why-decouple}

If you embed assertions directly inside your module rtl_logic, you risk two things:

Code Bloat
: Your design files become harder to read.

Synthesis Issues
: While most synthesis tools ignore SVA, keeping them separate ensures there is zero chance of accidentally affecting the hardware gates.

Today, we learn the “Wrapper and Bolt” method using the checker and bind constructs.


## The `checker` Construct: The Verification Wrapper {#the-checker-construct-the-verification-wrapper}

Think of a checker as a specialized container. It looks like a module, but it is specifically designed to hold assertions, properties, and the modeling logic needed to support them.

📝 Example: The APB Protocol Checker
Instead of putting protocol checks in the bus controller, we define them in a standalone checker.

```verilog
checker apb_protocol_check (
                            input logic pclk,
                            input logic presetn,
                            input logic psel,
                            input logic penable,
                            input logic pready,
                            input logic pslverr
                            );
// Property: PENABLE must follow PSEL in the next cycle
property p_sel_then_enable;
    @(posedge pclk) disable iff (!presetn)
      psel && !penable |=> penable;
endproperty

// Assertion instance
a_sel_enable: assert property (p_sel_then_enable)
  else $error("APB Error: PENABLE did not follow PSEL!");

endchecker
```


## The `bind` Construct: The Magic Linker {#the-bind-construct-the-magic-linker}

The bind statement is the most powerful tool in the SVA arsenal. It allows you to instantiate your checker inside an existing module without touching the original RTL file.

How it works:
You have your golden RTL: rtl_top.sv.

You have your assertions: apb_check.sv.

You create a third “bind file”: binder.sv.

📝 Example: Binding the Checker
Assume your design module is named my_design_core. Here is how you “inject” the checker into it:

```verilog
bind my_design_core apb_protocol_check u_apb_assertion_ip (
                                                           .pclk (clk), // Link design signal ‘clk’ to checker ‘pclk’
                                                           .presetn (rst_n), // Link design signal ‘rst_n’ to checker ‘presetn’
                                                           .psel (bus_sel),
                                                           .penable (bus_en),
                                                           .pready (bus_ready),
                                                           .pslverr (bus_err)
                                                           );
```

What just happened? The simulator treats this as if you physically typed apb_protocol_check u_apb_assertion_ip (...) inside the my_design_core module. Your RTL remains “pure,” but it's now fully monitored.


## Conclusion and What's Next {#conclusion-and-what-s-next}

By using checker and bind, you've created a modular, reusable verification library. You can move this checker from project to project, binding it to different modules as needed.

In the final phase of this series, we go cross-language. We will learn how to trigger C++ or Python/Cocotb events whenever these assertions fail or succeed using the DPI (Direct Programming Interface).
