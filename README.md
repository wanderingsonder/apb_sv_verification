

## 🔍 Project Overview

This project implements a complete **layered class-based testbench** for verifying an APB-compliant slave peripheral. The testbench is structured following industry-standard verification methodology principles:

- **Layered architecture** separating stimulus, checking, and coverage
- **Constrained-random verification** through a `rand` transaction class
- **Self-checking** via a reference predictor model and scoreboard comparison
- **Protocol checking** via a built-in SVA assertion on `PREADY`
- **Functional coverage** with coverpoints and cross-coverage
- **Dual-mode simulation**: with random wait states OR zero wait states
- **Automated regression** with per-test and merged HTML coverage reports

**Simulation tool:** Synopsys VCS `T-2022.06_Full64`  
**Coverage tool:** `urg` (Unified Report Generator)  
**Debug tool:** Synopsys Verdi (KDB enabled)  
**Final merged coverage score: 100.00%** ✅

---

## 📚 AMBA APB3 Protocol Background

The **Advanced Peripheral Bus (APB)** is part of the ARM AMBA bus family. It is designed for low-power, low-complexity peripheral access (UARTs, GPIOs, Timers, etc.).

### APB3 State Machine

Every APB transfer goes through exactly two phases:

```
       IDLE
        │
        ▼  PSEL=1, PENABLE=0
      SETUP
        │
        ▼  PSEL=1, PENABLE=1
      ACCESS  ──► PREADY=0 ──► (wait states) ──► PREADY=1 ──► Transfer Done
```

| Phase      | PSEL | PENABLE | PREADY | Description                              |
|------------|------|---------|--------|------------------------------------------|
| IDLE       | 0    | 0       | —      | No transfer in progress                  |
| SETUP      | 1    | 0       | —      | Address, data, control driven by master  |
| ACCESS     | 1    | 1       | 0      | Slave inserting wait states              |
| ACCESS     | 1    | 1       | 1      | Transfer complete                        |

### Key APB3 Signals

| Signal    | Direction      | Width | Description                                 |
|-----------|----------------|-------|---------------------------------------------|
| `PCLK`    | Input to Slave | 1     | Peripheral clock                            |
| `PRESETn` | Input to Slave | 1     | Active-low synchronous reset                |
| `PSEL`    | Input to Slave | 1     | Slave select                                |
| `PENABLE` | Input to Slave | 1     | Transfer enable (high = ACCESS phase)       |
| `PADDR`   | Input to Slave | 32    | Address bus                                 |
| `PWRITE`  | Input to Slave | 1     | 1=Write, 0=Read                             |
| `PWDATA`  | Input to Slave | 32    | Write data                                  |
| `PRDATA`  | Output         | 32    | Read data                                   |
| `PREADY`  | Output         | 1     | Wait state control (0=extend, 1=complete)   |
| `PSLVERR` | Output         | 1     | Slave error response                        |

---

## 📁 Project Structure

```
apb_sv_project/
│
├── rtl/
│   └── apb_slave_design.sv          # DUT: APB3-compliant slave with FSM
│
├── env/
│   ├── apb_interface.sv             # APB interface, clocking blocks, SVA assertion
│   ├── apb_transaction.sv           # Randomized transaction class with constraints
│   ├── apb_generator.sv             # Base generator class (virtual task run)
│   ├── apb_driver.sv                # Bus functional model — drives transactions to DUT
│   ├── apb_monitor.sv               # Passive bus observer — captures all transfers
│   ├── apb_predictor.sv             # Reference model — predicts expected DUT output
│   ├── apb_scoreboard.sv            # Compares monitor vs predictor + functional coverage
│   └── apb_enviroment.sv            # Top-level TB env: instantiates all components
│
├── test/
│   ├── apb_pkg.sv                   # Package: includes all env + test files
│   ├── apb_test.sv                  # Base test: plusarg dispatch, build_and_run task
│   ├── apb_write_test.sv            # Write-only (20 write transactions)
│   ├── apb_read_test.sv             # Read-only (20 read transactions)
│   ├── apb_write_read_test.sv       # Mixed: 10 writes + 10 reads
│   ├── apb_slverr_test.sv           # PSLVERR: 2 transactions to err_addr=0xFFFFFFFF
│   ├── apb_reset_test.sv            # Reset: mixed txns + 4 mid-simulation resets
│   ├── apb_write_zerowait_test.sv   # Write-only (zero wait state mode)
│   ├── apb_read_zerowait_test.sv    # Read-only (zero wait state mode)
│   ├── apb_write_read_zerowait_test.sv  # Mixed (zero wait state mode)
│   ├── apb_slverr_zerowait_test.sv  # PSLVERR (zero wait state mode)
│   └── apb_reset_zerowait_test.sv   # Reset (zero wait state mode)
│
├── top/
│   └── apb_top.sv                   # Top module: clock gen, reset, DUT, test instantiation
│
└── sim/
    ├── Makefile                     # All compile/run/regression/coverage targets
    ├── regression.py                # Python automation script for regression
    ├── verdi_config_file            # Verdi waveform configuration
    ├── *.log                        # Per-test simulation log files (pre-run)
    ├── *_coverage.vdb/              # Per-test VCS coverage databases
    ├── *_report/                    # Per-test URG HTML coverage reports
    └── merged_report/               # Merged coverage across all 10 tests
```

---

## 🔧 DUT — APB Slave Design

**File:** `rtl/apb_slave_design.sv`

The DUT is a fully APB3-compliant slave peripheral with the following features:

### Memory Map

| Address  | Register   | Reset Value    | Description                  |
|----------|------------|----------------|------------------------------|
| `0x00`   | `ctl_reg`  | `0x00000000`   | 4-bit control register       |
| `0x04`   | `timer_0`  | `0xCAFE1234`   | 32-bit timer register 0      |
| `0x08`   | `timer_1`  | `0xFACE5678`   | 32-bit timer register 1      |
| `0x0C`   | `stat_reg` | `0x00000000`   | 2-bit status register        |
| `other`  | `mem[]`    | address value  | 256-deep 32-bit memory array |

### DUT State Machine

The DUT implements a 3-state FSM clocked on the **negative edge** of `PCLK`:

```
                     psel=0
                  ┌──────────┐
                  │          │
                  ▼          │
              ┌────────┐     │
     ─────▶   │  SETUP │─────┘
              └────┬───┘
                   │
       ┌───────────┴────────────┐
       │ psel=1                 │ psel=1
       │ penable=0              │ penable=0
       │ pwrite=1               │ pwrite=0
       ▼                        ▼
  ┌──────────┐            ┌──────────┐
  │ W_ENABLE │            │ R_ENABLE │
  └────┬─────┘            └────┬─────┘
       │ pready=0 ◀── loop      │ pready=0 ◀── loop
       │ pready=1               │ pready=1
       └───────────┐   ┌────────┘
                   ▼   ▼
                ┌────────┐
                │  SETUP │  (transfer complete)
                └────────┘
```

| State      | Encoding | Transition Condition                  |
|------------|----------|---------------------------------------|
| `SETUP`    | `2'b00`  | Always starts here; waits for PSEL    |
| `W_ENABLE` | `2'b01`  | PSEL=1, PENABLE=0, PWRITE=1           |
| `R_ENABLE` | `2'b10`  | PSEL=1, PENABLE=0, PWRITE=0           |

### Wait State Behavior

The DUT has built-in configurable wait state injection:

```systemverilog
reg busy_rand_enable = 1;   // Enable random busy cycles
integer busy_min     = 0;   // Minimum random wait cycles
integer busy_max     = 5;   // Maximum random wait cycles
integer busy_delay   = 1;   // Fixed delay value
```

- By default, `PREADY` is deasserted for a **random 0–5 cycles** after `PSEL` assertion
- Passing `+zerowaitstate` at runtime disables all wait states (`busy_rand_enable=0`, `busy_delay=0`)

### Slave Error Injection

```systemverilog
reg err_enable = 1;
reg [31:0] err_addr = {32{1'b1}};   // Default err addr: 0xFFFFFFFF
```

`PSLVERR` is asserted on the **negedge of PCLK** whenever `PADDR == err_addr`. This is used by the `apb_slverr_test` to verify error response handling.

### DUT Utility Tasks

| Task               | Parameters              | Description                        |
|--------------------|-------------------------|------------------------------------|
| `set_random_delay` | `delay_min, delay_max`  | Enable random wait states          |
| `set_fixed_delay`  | `delay`                 | Set fixed wait state count         |
| `set_slverr`       | `addr`                  | Set the address that triggers PSLVERR |

### Reset Behavior

On `rst_n = 0` (negedge-clocked):
- `ctl_reg`, `stat_reg`, `data_in` reset to `0`
- `timer_0` resets to `0xCAFE1234`
- `timer_1` resets to `0xFACE5678`
- `prdata` resets to `0`, `pready` resets to `1`
- `mem[i]` initialized to `i` (index value)

---

## 🏗 Testbench Architecture

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                              apb_top  (module)                               ║
║                                                                              ║
║  ╔════════════════════════════════════════════════════════╗                  ║
║  ║                    apb_environment                     ║                  ║
║  ║                                                        ║                  ║
║  ║   ┌─────────────┐  gdmbx  ┌─────────────┐             ║                  ║
║  ║   │  Generator  │────────▶│    Driver   │             ║                  ║
║  ║   └─────────────┘         └──────┬──────┘             ║                  ║
║  ║          ▲                       │                     ║                  ║
║  ║          │  event e1             │  drives signals     ║                  ║
║  ║          │                       ▼                     ║                  ║
║  ║   ┌─────────────┐        ┌───────────────┐            ║  ┌─────────────┐ ║
║  ║   │   Monitor   │◀───────│ apb_interface │◀──────────▶║  │  apb_slave  │ ║
║  ║   └──────┬──────┘        │   (dr_cb /    │            ║  │    (DUT)    │ ║
║  ║          │               │    mo_cb)     │            ║  └─────────────┘ ║
║  ║          │               └───────────────┘            ║                  ║
║  ║          │  mpmbx                                      ║                  ║
║  ║          ├──────────────▶┌─────────────┐  psmbx       ║                  ║
║  ║          │               │  Predictor  │─────────┐    ║                  ║
║  ║          │               └─────────────┘         │    ║                  ║
║  ║          │  msmbx                                 ▼    ║                  ║
║  ║          └──────────────────────────────▶┌─────────────┐                 ║
║  ║                                          │ Scoreboard  │                 ║
║  ║                                          │  +Coverage  │                 ║
║  ║                                          └─────────────┘                 ║
║  ╚════════════════════════════════════════════════════════╝                  ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

### Mailbox Communication

| Mailbox  | Type       | From → To              | Purpose                                  |
|----------|------------|------------------------|------------------------------------------|
| `gdmbx`  | Bounded(1) | Generator → Driver     | One transaction at a time (flow control) |
| `mpmbx`  | Unbounded  | Monitor → Predictor    | Captured bus transaction for prediction  |
| `msmbx`  | Unbounded  | Monitor → Scoreboard   | Captured bus transaction for comparison  |
| `psmbx`  | Unbounded  | Predictor → Scoreboard | Expected output for comparison           |

### Synchronization Event

```systemverilog
event e1;  // Declared in apb_pkg
```

The monitor triggers `->e1` after capturing each transaction. The generator waits `@(e1)` before sending the next transaction — this creates a **handshake** that prevents the generator from running ahead of the DUT.

---

## 🔬 Component Deep-Dive

### 1. APB Interface & Clocking Blocks

**File:** `env/apb_interface.sv`

```systemverilog
interface apb_interface;
  logic rst_n, pclk;
  logic psel, penable, pwrite;
  logic [31:0] paddr, pwdata, prdata;
  logic pready, pslverr;

  // Driver clocking block — outputs driven, inputs sampled
  clocking dr_cb @(posedge pclk);
    output psel, pwrite, pwdata, paddr, penable;
    input  pready, prdata, pslverr;
  endclocking

  // Monitor clocking block — all signals sampled (read-only)
  clocking mo_cb @(posedge pclk);
    input psel, pwrite, pwdata, paddr, penable, prdata, pready, pslverr;
  endclocking

  modport dr_mp (clocking dr_cb);
  modport mo_mp (clocking mo_cb);
endinterface
```

**Built-in SVA Protocol Assertion:**

```systemverilog
property pready_check;
  @(posedge pclk) $rose(psel) ##1 penable |-> ##[0:5] pready;
endproperty

assertion_check: assert property(pready_check);
```

This assertion fires if `PREADY` is not asserted within **5 clock cycles** after `PENABLE` goes high — catching any DUT hang or excessive wait-state violations automatically.

---

### 2. APB Transaction

**File:** `env/apb_transaction.sv`

The transaction object carries all APB signal values for one transfer:

```systemverilog
class apb_transaction;
  rand bit [31:0] paddr;    // Randomized address
  rand bit [31:0] pwdata;   // Randomized write data
  rand bit        pwrite;   // Randomized direction

  // Observed/captured fields (not randomized)
  bit        psel, penable;
  bit [31:0] prdata;
  bit        pready, pslverr;
```

**Constraints:**

| Constraint  | Description |
|-------------|-------------|
| `addr_c`    | Soft: address from boundary values (`0xFF`, `0x55`, `0xCC`, `0xAB`, `0xFC`, etc.) |
| `addr_a`    | Hard: **exclude** register addresses `{0, 4, 8, 12}` — forces tests to hit `mem[]` array |
| `data_c`    | Soft: write data from walking-bit and checkerboard patterns (`0xAAAA_AAAA`, `0x5555_5555`, `0xA5A5_A5A5`, etc.) |
| `pwrite_c`  | Soft: randomize read/write direction |

**Display function** prints a tagged summary of every transaction:
```
[GEN] : [100] paddr: ab | pwdata: 5555 | prdata: 0 | pwrite: 1 | psel: 0 | penable: 0 | pready: 0 | pslverr: 0
```

---

### 3. APB Generator

**File:** `env/apb_generator.sv`

The base generator class is intentionally minimal — its `run()` task is declared `virtual` so each test overrides it with specific stimulus:

```systemverilog
class apb_generator;
  apb_transaction tr;
  mailbox gdmbx;

  virtual task run();
    // Base: empty — each test class overrides this
  endtask : run
endclass
```

Each test class **extends** `apb_generator` and overrides `run()` to define its own transaction sequence. This is the key extensibility point of the entire testbench.

---

### 4. APB Driver

**File:** `env/apb_driver.sv`

The driver gets a transaction from the generator mailbox and drives it onto the APB bus using the driver clocking block. It implements **two modes** selected via plusarg:

**With Wait States (`with_wait_logic`):**
```
Cycle 1: PSEL=0, PENABLE=0                    (IDLE)
Cycle 2: PSEL=1, PENABLE=0, set PADDR/PWRITE/PWDATA  (SETUP)
Cycle 3: PENABLE=1                             (ACCESS)
         wait(pready==1)                       (DUT controls completion)
```

**Zero Wait State (`zero_wait_logic`):**  
Same as above but **without** `wait(pready)` — driver immediately moves to the next transaction without waiting for PREADY acknowledgement.

```systemverilog
task run();
  if ($test$plusargs("zerowaitstate")) zero_wait_logic();
  else with_wait_logic();
endtask
```

---

### 5. APB Monitor

**File:** `env/apb_monitor.sv`

The monitor is **purely passive** — it observes the bus using the read-only `mo_cb` clocking block and never drives any signals.

**Capture sequence (`with_wait_logic`):**
```
1. Wait for: psel=1, penable=0     (SETUP phase detected)
2. Advance one clock
3. Confirm: psel=1, penable=1     (ACCESS phase)
4. Wait for: pready=1             (transfer complete)
5. Capture all signals into transaction object
6. Put into mpmbx (for predictor) AND msmbx (for scoreboard)
7. Trigger ->e1                   (unblock generator)
```

In `zero_wait_logic` mode step 4 (waiting for PREADY) is skipped.

---

### 6. APB Predictor

**File:** `env/apb_predictor.sv`

The predictor is a **software reference model** of the DUT. It maintains its own internal `mem[256]` shadow memory and independently computes what `PRDATA` should be for every read transaction.

**Prediction logic:**

```
If rst_n=0:
  → prdata=0, pready=1
  → mem[i] = i  (mirror DUT reset initialization)

Else if pslverr=1:
  → Pass-through error fields (no memory update)

Else if pwrite=1  (WRITE):
  → mem[paddr] = pwdata  (update shadow memory)

Else (READ):
  → pspkt.prdata = mem[paddr]  (predict expected read data)
```

The predicted packet is forwarded to the scoreboard via `psmbx`.

---

### 7. APB Scoreboard & Functional Coverage

**File:** `env/apb_scoreboard.sv`

The scoreboard receives packets from both the monitor (`msmbx`) and predictor (`psmbx`) and compares them for every **read transaction**:

```systemverilog
if (mon2sco.pwrite == 1'b0) begin
  if (mon2sco.prdata == pre2sco.prdata)
    $display("[SCO] PASS = PRDATA mon=%0h <=> %0h = pre", ...);
  else
    $display("[SCO] FAIL = PRDATA mon=%0h <=> %0h = pre", ...);
end
```

**Functional Coverage Group (`apb_cov1`):**

| Coverpoint   | Signal            | Bins Description |
|--------------|-------------------|------------------|
| `CP1`        | `paddr`           | `b1`: addresses 0–127; `b2`: error address `0xFFFFFFFF` |
| `CP2`        | `pwdata`          | `b3`: write data values 0–255 |
| `CP3`        | `prdata`          | `b4`: read data values 0–255 |
| `CP4`        | `psel`            | Selected state (=1) |
| `CP5`        | `pwrite`          | Write direction (=1) and Read direction (=0) |
| `CP6`        | `pslverr`         | Error asserted (=1) and not asserted (=0) |
| `CP2_X_CP5`  | `pwdata × pwrite` | Cross coverage: data patterns vs. transfer direction |
| `CP3_X_CP5`  | `prdata × pwrite` | Cross coverage: read data vs. transfer direction |

---

### 8. APB Environment

**File:** `env/apb_enviroment.sv`

The environment is the glue layer — it instantiates all TB components and connects them via mailboxes and virtual interfaces:

```systemverilog
class apb_envrionment;
  apb_generator  gen;
  apb_driver     dvr;
  apb_monitor    mon;
  apb_predictor  pre;
  apb_scoreboard sco;

  mailbox gdmbx = new(1);   // Bounded(1): flow control gen→drv
  mailbox mpmbx = new();    // mon → pre
  mailbox msmbx = new();    // mon → sco
  mailbox psmbx = new();    // pre → sco
```

`build()` creates all component instances. `run()` waits 20 time units then forks all component `run()` tasks in parallel:

```systemverilog
task start_process();
  fork
    gen.run();
    dvr.run();
    mon.run();
    pre.run();
    sco.run();
  join_none
endtask
```

---

### 9. APB Test & Top Module

**File:** `test/apb_test.sv` | `top/apb_top.sv`

The `apb_test` class uses `$test$plusargs` to select which test to run at simulation time — no recompilation needed to switch tests:

```systemverilog
if ($test$plusargs("apb_write_read_test")) begin
  apb_wr_rd = new(env.gdmbx);
  env.build();
  env.gen = apb_wr_rd;   // Inject test-specific generator
  env.run();
end
```

The `apb_top` module generates the clock, drives initial reset, and calls `test_h.build_and_run()`. Simulation finishes at **1820 ps** via `$finish`.

```systemverilog
always #5 vif.pclk = ~vif.pclk;   // 10 ps clock period

initial begin
  vif.rst_n = 1'b0;
  #40;
  vif.rst_n = 1'b1;   // Deassert reset after 4 clock cycles
end
```

---

## 🧪 Test Suite

All 10 tests run against the same DUT. The first 5 use **random wait states (0–5 cycles)**; the last 5 use **zero wait state mode** (`+zerowaitstate`).

| TC   | Test Name                        | Mode       | Transactions  | Description |
|------|----------------------------------|------------|---------------|-------------|
| tc1  | `apb_write_read_test`            | Wait states | 10W + 10R    | First 10 constrained-random writes, then 10 reads back to verify data retention |
| tc2  | `apb_write_test`                 | Wait states | 20W          | 20 constrained-random write-only transactions |
| tc3  | `apb_read_test`                  | Wait states | 20R          | 20 constrained-random read-only transactions (PWDATA forced to 0) |
| tc4  | `apb_slverr_test`                | Wait states | 2            | 2 transactions targeting `PADDR=0xFFFFFFFF` to trigger and verify `PSLVERR` |
| tc5  | `apb_reset_test`                 | Wait states | 20 + resets  | Mixed 10W+10R with `rst_n` pulsed low at t=500, 650, 800, 1000 ps |
| tc6  | `apb_write_read_zerowait_test`   | Zero wait  | 10W + 10R    | Same as tc1, DUT wait states disabled via `+zerowaitstate` |
| tc7  | `apb_write_zerowait_test`        | Zero wait  | 20W          | Same as tc2, zero wait state mode |
| tc8  | `apb_read_zerowait_test`         | Zero wait  | 20R          | Same as tc3, zero wait state mode |
| tc9  | `apb_slverr_zerowait_test`       | Zero wait  | 2            | Same as tc4, zero wait state mode |
| tc10 | `apb_reset_zerowait_test`        | Zero wait  | 20 + resets  | Same as tc5, zero wait state mode |

### Reset Test — Reset Injection Timeline

The reset test injects `rst_n=0` pulses at 4 different simulation times to verify DUT recovery mid-transaction:

```
t=500 ps  → rst_n=0 for 10 ps
t=650 ps  → rst_n=0 for 30 ps
t=800 ps  → rst_n=0 for 50 ps
t=1000 ps → rst_n=0 for 50 ps
```

---

## ⏱ APB Transfer Phases

### Write Transfer — With Wait State

```
          T0        T1        T2       T3(wait)   T4
           │         │         │         │         │
PCLK   ───┐ ┌───┐ ┌───┐ ┌───┐ ┌───┐ ┌───┐ ┌───
       │   └─┘   └─┘   └─┘   └─┘   └─┘   └─┘

PSEL   ────────────┌─────────────────────────┐─────
                   │                         │
PENABLE────────────────────┌─────────────────┐─────
                            │                │
PADDR  ────────────┌────────────────────────┐──────
                   │    0xAB                │
PWDATA ────────────┌────────────────────────┐──────
                   │    0x5555              │
PREADY ──────────────────────────┐──────────────────
                                 │  wait   │
                                 └─────────┘  HIGH

Phase     IDLE      SETUP              ACCESS (wait) ACCESS (done)
```

### Read Transfer — Zero Wait State

```
          T0        T1        T2        T3
           │         │         │         │
PCLK   ───┐ ┌───┐ ┌───┐ ┌───┐ ┌───┐ ┌───
       │   └─┘   └─┘   └─┘   └─┘   └─┘

PSEL   ────────────┌─────────────────┐─────────
                   │                 │
PENABLE────────────────────┌─────────┐─────────
                            │        │
PADDR  ────────────┌──────────────┐───────────
                   │    0xAB      │
PRDATA ──────────────────────────┌──────┐─────
                                 │ DATA │
PREADY ──────────────────────────────────────── (always HIGH, no wait)

Phase     IDLE      SETUP      ACCESS       IDLE
```

---

## 🔄 Simulation Flow

```
  ┌─────────────────────────────────────────────────────────────────┐
  │  1.  VCS compiles:  RTL + ENV + PKG + TOP                       │
  │  2.  simv invoked with  +<test_name>  plusarg                   │
  │  3.  apb_top: assert rst_n=0 for 40ps → deassert               │
  │  4.  apb_test: dispatch test via $test$plusargs                 │
  │  5.  env.build():  create gen / drv / mon / pre / sco           │
  │  6.  env.run():  fork all component run() tasks                 │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
             ┌───────────────▼───────────────┐
             │         Per Transaction        │
             │                               │
             │  Generator ──gdmbx──▶ Driver  │
             │                       │       │
             │               IDLE → SETUP    │
             │                    → ACCESS   │
             │                       │       │
             │                    DUT responds│
             │               (PREADY / PRDATA│
             │                / PSLVERR)     │
             │                       │       │
             │              Monitor captures │
             │              ┌────────┴──────┐│
             │              ▼               ▼│
             │          Predictor      Scoreboard
             │          (mpmbx)    ◀── (msmbx) ──▶ PASS/FAIL
             │              │          Coverage sample
             │              └──psmbx──▶ Scoreboard
             │                               │
             │          Monitor ──e1──▶ Generator (next txn)
             └───────────────────────────────┘
                             │
             ┌───────────────▼───────────────┐
             │  $finish at 1820 ps            │
             │  urg → HTML coverage report    │
             └───────────────────────────────┘
```

---

## 🚀 Running Simulations

All commands are run from the `sim/` directory.

### Compile

```bash
cd apb_sv_project/sim/
make compile
```

This executes:
```bash
vcs -full64 -sverilog -kdb -debug_access+all \
    ../rtl/apb_slave_design.sv    \
    ../env/apb_interface.sv       \
    ../test/apb_pkg.sv            \
    ../top/apb_top.sv             \
    +incdir+../test/ +incdir+../env/ +incdir+../top/
```

### Run Individual Tests

```bash
make tc1    # apb_write_read_test          (with wait states)
make tc2    # apb_write_test
make tc3    # apb_read_test
make tc4    # apb_slverr_test
make tc5    # apb_reset_test
make tc6    # apb_write_read_zerowait_test (zero wait state)
make tc7    # apb_write_zerowait_test
make tc8    # apb_read_zerowait_test
make tc9    # apb_slverr_zerowait_test
make tc10   # apb_reset_zerowait_test
```

Each target runs simulation, generates a `.vdb` coverage database, and produces an HTML report. For example, `tc1` internally executes:

```bash
vcs -R -full64 -sverilog -kdb -debug_access+all         \
    +ntb_random_seed_automatic                           \
    -override_timescale=1ps/1ps                          \
    ../rtl/apb_slave_design.sv ../env/apb_interface.sv  \
    ../test/apb_pkg.sv ../top/apb_top.sv                 \
    +incdir+../test/ +incdir+../env/ +incdir+../top/     \
    -cm_dir apb_write_read_test_coverage.vdb             \
    +apb_write_read_test                                 \
    -l apb_write_read_test.log

urg -dir apb_write_read_test_coverage.vdb \
    -report apb_write_read_test_report
```

### Run All 10 Tests

```bash
make tc
```

### Merge Coverage & Open Report

```bash
make merge     # Merge all 10 .vdb files → merged_report/
make report    # Open merged_report/dashboard.html in Firefox
```

### Full Regression (Compile + All Tests + Merge + Report)

```bash
make regression
```

### Python Regression

```bash
python3 regression.py
```

### Clean All Build Artifacts

```bash
make clean
```

Removes: `csrc/`, `simv`, `simv.daidir/`, all `.vdb` databases, all `*_report/` directories, all `.log` files.

---

## 📊 Coverage Results

All 10 test cases were run and coverage was merged. Results from the reference simulation run:

```
Tool     : Synopsys VCS T-2022.06_Full64
Date     : Wed Oct 29 16:53:42 2025
Tests    : 10

-------------------------------------------
 Total Coverage Summary
 SCORE     GROUP
 100.00    100.00
-------------------------------------------
```

**Merged functional coverage: 100.00%** ✅

### Per-Test Coverage Reports

| Test                         | Coverage DB                              | HTML Report |
|------------------------------|------------------------------------------|-------------|
| tc1 – apb_write_read_test    | `apb_write_read_test_coverage.vdb`       | `apb_write_read_test_report/dashboard.html` |
| tc2 – apb_write_test         | `apb_write_test_coverage.vdb`            | `apb_write_test_report/dashboard.html` |
| tc3 – apb_read_test          | `apb_read_test_coverage.vdb`             | `apb_read_test_report/dashboard.html` |
| tc4 – apb_slverr_test        | `apb_slverr_test_coverage.vdb`           | `apb_slverr_test_report/dashboard.html` |
| tc5 – apb_reset_test         | `apb_reset_test_coverage.vdb`            | `apb_reset_test_report/dashboard.html` |
| tc6–10 – zero wait variants  | `*_zerowait_*_coverage.vdb`              | `*_zerowait_*_report/dashboard.html` |
| **Merged (all tests)**       | all 10 VDBs                              | `merged_report/dashboard.html` ✅ |

---

## 🛠 Tools & Requirements

| Tool               | Version        | Purpose |
|--------------------|----------------|---------|
| **Synopsys VCS**   | T-2022.06_Full64 | Compilation and simulation |
| **Synopsys Verdi** | T-2022.06      | Waveform viewing and debug (`verdi_config_file` included) |
| **urg**            | T-2022.06      | Coverage report generation (bundled with VCS) |
| **Python 3**       | 3.x            | Regression automation (`regression.py`) |
| **Firefox**        | any            | View HTML coverage reports (`make report`) |
| **GNU Make**       | any            | Build automation |

---

## ⚙️ Setup Before First Run

### Fix Absolute Paths in `apb_pkg.sv`

The package file currently contains hardcoded absolute paths from the original development machine. Replace them with relative paths:

```systemverilog
// BEFORE (must change):
`include "/home/dvft0901/apb_sv_project/env/apb_transaction.sv"
`include "/home/dvft0901/apb_sv_project/env/apb_generator.sv"
// ...

// AFTER (relative paths):
`include "../env/apb_transaction.sv"
`include "../env/apb_generator.sv"
`include "../env/apb_driver.sv"
`include "../env/apb_monitor.sv"
`include "../env/apb_predictor.sv"
`include "../env/apb_scoreboard.sv"
`include "../env/apb_enviroment.sv"
`include "../test/apb_test.sv"
```

Apply the same fix in `test/apb_test.sv` for the test file includes:

```systemverilog
`include "../test/apb_write_read_test.sv"
`include "../test/apb_write_test.sv"
`include "../test/apb_read_test.sv"
`include "../test/apb_slverr_test.sv"
`include "../test/apb_reset_test.sv"
`include "../test/apb_write_read_zerowait_test.sv"
`include "../test/apb_write_zerowait_test.sv"
`include "../test/apb_read_zerowait_test.sv"
`include "../test/apb_slverr_zerowait_test.sv"
`include "../test/apb_reset_zerowait_test.sv"
```

---

## 📝 .gitignore Recommendation

Create a `.gitignore` in the project root before your first commit:

```gitignore
# Simulation build artifacts
sim/csrc/
sim/simv
sim/simv.daidir/
sim/ucli.key
sim/*.key
sim/*.vpd
sim/*.vcd
sim/*.dump

# Coverage databases
sim/*.vdb/

# Per-test HTML coverage reports
sim/*_report/
sim/urgReport/

# Simulation log files
sim/*.log

# Vim editor swap files
**/.*.swp
**/.*.swo

# VCS internal files
sim/.restartSimSession.tcl.old
sim/.fsm.sch.verilog.xml
**/-picarchive.daidir/

# Python cache
__pycache__/
*.pyc
```

---

## 💡 Key Design Decisions

**Bounded mailbox (`gdmbx = new(1)`)** — The size-1 bounded mailbox between generator and driver creates natural back-pressure. The generator blocks on `put()` until the driver calls `get()`, preventing the generator from racing ahead of the DUT.

**Event `e1` handshake** — The monitor triggers `->e1` only after a complete, verified transaction is captured (including `PREADY=1`). The generator waits `@(e1)` before producing the next stimulus. This ensures no new stimulus arrives while the DUT is still processing.

**Virtual `run()` in generator** — Declaring the base generator's `run()` task as `virtual` is the cornerstone of the entire test architecture. Adding a new test requires only writing a new class that extends `apb_generator` and overrides `run()` — no other TB file needs to change.

**Shadow memory in predictor** — The predictor maintains its own independent `mem[256]` that mirrors every write the DUT receives. This allows the predictor to independently compute expected read data without querying the DUT, making the scoreboard comparison truly self-checking.

**`+ntb_random_seed_automatic`** — A different random seed is used every simulation run. This ensures that corner cases missed by one seed may be caught in another, making regression more robust over time.

---

*Designed and verified using Synopsys VCS T-2022.06 | AMBA APB3 Specification | SystemVerilog IEEE 1800-2017*
