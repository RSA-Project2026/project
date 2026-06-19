# Investigating LLM-based TLA+ Specification Generation for Paxos Implementations

##### Authors: Aanhar Al Haydar, Andrea Vezzuto

---

This repository contains the experiments and helper scripts for generating TLA+ specifications from Paxos implementations, running a repair loop, and evaluating generated specifications using the SysMoBench evaluation suite.

**Prerequisites**

- Python 3.10+. Use `zsh` for the example commands below.
- Java + `tla2tools.jar` for TLC (the SysMoBench CLI checks for these and can download them via its setup helper).
- A virtual environment is recommended.

**1) Setup (virtualenv & dependencies)**

This workspace expects two repositories to be present side-by-side. Clone both into the same parent directory:

```
git clone https://github.com/RSA-Project2026/project
git clone https://github.com/RSA-Project2026/SysMoBench
```

After cloning, your workspace layout should look like:

```
<parent-dir>/project/            # this repository
<parent-dir>/SysMoBench/         # the SysMoBench evaluation toolset
```

Then, from the repository root:

```
# 1) create a venv if you don't have one
python3 -m venv .venv
source .venv/bin/activate

# 2) install Python deps for generating the specifications
cd project
pip install -r requirements.txt

# 3) install SysMoBench requirements to run SysMoBench CLI
cd ../SysMoBench
pip install -e .
sysmobench-setup
```

Set API keys (if you use Gemini / other LLMs). For the provided Gemini-based scripts, create a `.env` in `project/` with:

```
GEMINI_API_KEY=your_gemini_api_key_here
```

---

**2) Verify the Paxos implementations and run the unit tests (optional)**

This repository contains three Paxos implementations: essential, practical, and functional. The can be found under `project/implementations`, and have been derived from https://github.com/cocagne/paxos.
The functionality of each implementation is as follows:

- **Essential**:  A minimal implementation of the Paxos algorithm, only containing what is strictly necessary to achieve the aforementioned definition. In practice, it may be inefficient.
- **Practical**: Enhances the essential implementation with leadership tracking, NACKs, and state persistence.
- **Functional**: Builds on the practical implementation with a heartbeating mechanism to detect leadership failure and efficiently initiate recovery.

To run the experiments in the most fair and independent manner, we have slightly modified the implementations to remove an inheritance between them. As such, each implementation is completely independent of the others.
To verify that these modifications have not modified protocol functionality, you can run the following unit tests in `project/test/`, once again derived from https://github.com/cocagne/paxos.
To run all tests:

```
cd project
python -m test.test_essential
python -m test.test_practical
python -m test.test_functional
```

---

**3) Generate specifications (TLA+ and TLC cfg)**

There are two main ways to generate specifications in this repo:

- Use the generator in `project/prompt_gemini.py` (requires Gemini API key):

```
cd project
# Writes outputs to `generated_specs/<implementation>/direct_call/generated_specification.tla` and `_cfg`.
python prompt_gemini.py
```

- Alternatively run SysMoBench generation methods (via the SysMoBench CLI) if you want to use the benchmark's full prompt/method pipeline; see the SysMoBench section below.

---

**4) Repair loop**

This repository provides a small repair driver `fix_gemini.py` which:

- reads a generated spec and a TLC config from `generated_specs/...`;
- reads compilation/runtime errors emitted by the SysMoBench `compilation_check` / `runtime_check` runs in `SysMoBench/output/...`;
- calls the LLM (Gemini) using a repair prompt and writes `after_fixes` TLA+/cfg files.

Repair-loop steps:

1. Generate a spec (see section 3).
2. Run SysMoBench `compilation_check` and `runtime_check` on the generated spec so the relevant `output/` JSON is produced. Example (using an existing Paxos essential spec):

```
# from repository root
cd SysMoBench
sysmobench --task paxos_essential --method direct_call --model local_file_gemini \
  --metric compilation_check --spec-file ../project/generated_specs/paxos_essential/direct_call/paxos_essential.tla

sysmobench --task paxos_essential --method direct_call --model local_file_gemini \
  --metric runtime_check --spec-file ../project/generated_specs/paxos_essential/direct_call/paxos_essential.tla \
  --config-file ../project/generated_specs/paxos_essential/direct_call/paxos_essential.cfg
```

3. Run the repair script (it expects the SysMoBench outputs in `SysMoBench/output/...`):

```
cd ../project
python fix_gemini.py
```

`fix_gemini.py` will write the repaired spec and cfg into `generated_specs/paxos_<impl>/after_fixes/`.

4. Re-run the SysMoBench checks on the `after_fixes` spec (repeat steps in (2)), and iterate until satisfied.

Notes:

- `fix_gemini.py` is a small example driver using Gemini; adapt or replace it if you use a different LLM.
- Ensure `SysMoBench/output/` is writable and that you run the SysMoBench runner from the `SysMoBench/` project root (the repo scripts assume relative paths).

---

**5) Running the SysMoBench metrics**

SysMoBench supports a number of evaluation metrics. The canonical CLI wrapper is `SysMoBench/scripts/run_benchmark.py`. To list all available metrics and descriptions:

```
sysmobench --list-metrics
```

The typical four evaluation phases/metrics that correspond to SysMoBench scoring are:

- **P1 — action_decomposition**: Basic syntax/compilation check (SANY/TLA+ parser).

  - Run with:

  ```
  sysmobench --task <task> --method <method> --model <model> --metric compilation_check --spec-file path/to/spec.tla --config-file path/to/spec.cfg
  ```
- **P2 — runtime_coverage**: TLC model checking using the spec's invariants (runtime semantics check).

  - Run with:

  ```
  sysmobench --task <task> --method <method> --model <model> --metric runtime_coverage --spec-file path/to/spec.tla --config-file path/to/spec.cfg
  ```
- **P3 — transition_validation (TV)**: Per-action conformance to system traces. This is agent-driven and will require passing a `--tv-agent`/`--tv-model` and confirming API budget. Alternatively, you can use an AI-enabled IDE and prompt it to follow the guides in `SysMoBench/tla_eval/skills/harness-gen` and `SysMoBench/tla_eval/skills/tv-eval`.

  - Run with:

  ```
  sysmobench --task <task> --method <method> --model <model> --metric transition_validation \
    --spec-file path/to/spec.tla --config-file path/to/spec.cfg --tv-agent <agent-cli> --tv-model <model-name>
  ```
- **P4 — invariant_verification**: Check the model using expert invariants or translated invariants for deeper correctness.

  - Run with:

  ```
  sysmobench --task <task> --method <method> --model <model> \
    --metric invariant_verification --spec-file path/to/spec.tla --config-file path/to/spec.cfg --inv-translator-type direct
  ```

Replace `<task>`, `<method>`, `<model>`, and `path/to/spec.*` with the appropriate task name (e.g. `paxos` or the task name used in your SysMoBench copy), method (e.g. `direct_call`), and the model name (or `local_file_gemini` when evaluating an existing spec file).

---

**6) Troubleshooting & notes**

- If Java or `tla2tools.jar` are missing, run the SysMoBench setup helper: `python3 -m SysMoBench.tla_eval.setup_cli` or read `SysMoBench/tla_eval/README.md` for the environment setup steps.
- If you plan to use Gemini or any paid model APIs for generation or TV agents, confirm API credentials and budgets before running `transition_validation`.
- The provided `fix_gemini.py` and `prompt_gemini.py` are example drivers — you may adapt them to other LLMs by replacing the client code and prompts in `prompts/`.
