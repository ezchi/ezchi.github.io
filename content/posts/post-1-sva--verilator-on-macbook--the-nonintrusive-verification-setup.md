+++
title = "Post 1: SVA & Verilator on Macbook : The Non-Intrusive Verification Setup"
author = ["Enze Chi"]
date = 2025-11-23T11:34:00+11:00
tags = ["SVA", "FPGA", "Verification", "Verilator"]
categories = ["Verification"]
draft = false
+++

## Introduction: Why Assertions and Non-Intrusive Verification? {#introduction-why-assertions-and-non-intrusive-verification}

SystemVerilog Assertions (SVA) are not just another test language; they are a declarative, temporal powerhouse. Instead of writing hundreds of lines of procedural code to check a protocol's timing, you define the rule once. This significantly reduces verification effort.

In professional flows, it's crucial to keep verification separate from design. I want to check the golden RTL without modifying it. This post is the first step: setting up the environment using the open-source workhorse Verilator on MacOS system.


## 🛠️ Part 1: Prerequisites -- The Toolchain {#️-part-1-prerequisites-the-toolchain}

I need the right tools to compile the SystemVerilog into a simulation model.

Xcode Command Line Tools
: These are essential for the native C/C++ compiler suite (clang or gcc) that Verilator will rely on to build the final simulator executable.

Action: Open your Terminal and run:

```sh
xcode-select --install
```

Note: If you get a message saying the tools are already installed, you're good to go!

Homebrew (The macOS Package Manager)
: Homebrew makes installing open-source tools like Verilator incredibly simple.

Action: If you don't have it, install Homebrew by following the instructions on its official site, typically by running:

```sh
/bin/bash -c “$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)”
```


## 🚀 Part 2: Installing Verilator -- The SVA Compiler {#part-2-installing-verilator-the-sva-compiler}

Verilator is a unique tool. It doesn't just simulate; it compiles your SystemVerilog RTL and SVA code into a high-performance C++ model. This is the key that unlocks integration with C++ and, subsequently, Python/Cocotb.

Install Verilator
: Use Homebrew to fetch and install the latest stable version.

Action: Run the following in your Terminal:

```sh
brew install verilator
```

Verification: Check your installation to ensure Verilator is recognized globally.

Action: Run:

```sh
verilator --version
```

Expected Output: You should see the version number (e.g., Verilator 5.042 2025-11-02 rev...).

In the following posts, I will share my SVA learning journey.
