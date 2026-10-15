# Language-Model-Assisted Proof Construction for Parameterised Relational Hardware

Select a model and benchmark, supply the provider's API key, and follow live Rocq
goals and proof progress. Includes twelve model presets and six benchmarks:
`preHorners`, `Horners`, `interchange_2x2`, `monitor`, `contour_row`, `contour_right`.
Each benchmark's statement and guidance are in `benchmarks/<name>/`;
required Rocq modules are under `library/`.

## Setup

Requires Python 3.12, opam and system build prerequisites on Linux:

```sh
python3.12 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt
opam switch create proof-tool ocaml-base-compiler.4.14.2
eval "$(opam env --switch=proof-tool --set-switch)"
opam repository add coq-released https://coq.inria.fr/opam/released
opam install coq.8.19.2 coq-lsp.0.2.3+8.19
```

Keep `coqc`, `coqchk` and `coq-lsp` on PATH in the terminal used to run the prover.

## Run

```sh
python scripts/run_prover.py
```

Choose a model and benchmark from the terminal menu. Set `OPENAI_API_KEY`,
`ANTHROPIC_API_KEY` or `GEMINI_API_KEY` (`GOOGLE_API_KEY` also works) as an
environment variable, or enter the selected provider's key at the hidden prompt.

For example, for an OpenAI model:

```sh
export OPENAI_API_KEY="your-api-key"
python scripts/run_prover.py
```

Without an interactive terminal, supply a key through an environment variable or
`--key-file`. Keys are not saved in session logs. `--list` and `--prepare` do not
require a key.

```sh
python scripts/run_prover.py --list
python scripts/run_prover.py --model gpt-6.1-sol --benchmark monitor
python scripts/run_prover.py --provider openai --model YOUR_MODEL_ID --benchmark preHorners
```

Model presets are in `environment/models.json`. `--max-output`, `--effort` and
Anthropic's `--thinking` adjust native request settings. `--max-calls` sets an
optional request limit. Preset output allowances can be large; use `--help` for
all controls. API usage is billed by the provider, and model access may vary.

Horners needs a checked preHorners prerequisite. First run preHorners, then pass
that session's `candidate.v` with `--prerequisite PATH` when running Horners.
No target proof is included in this repository.

Sessions save current goals, the checked prefix, model exchanges and the final
result under ignored `runs/`. `--output PATH` chooses a new directory; `--verbose`
also displays prompts and responses. Accepted proofs pass statement/action checks,
compilation, approved extensionality assumptions and independent `coqchk` replay.
Use `--prepare` to compile dependencies and prepare prompts without model calls.
