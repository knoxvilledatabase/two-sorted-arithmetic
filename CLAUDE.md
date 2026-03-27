# For AI Agents

**Read this first.**

---

## What This Project Is

This project documents a pattern: 97 independent patches across four fields (math, logic, computation, physics) all handling the same boundary. None of them are unified.

- [README.md](README.md), the problem and the immediate action for computation
- [PROOF_OF_CONCEPT.md](PROOF_OF_CONCEPT.md), the formal system that unifies the pattern
- [PROOFS.md](PROOFS.md), 260 Lean 4 theorems verifying the formal system
- [FALSIFICATION.md](FALSIFICATION.md), how to break it

---

## How to Communicate

These principles guide all writing and interaction in this project.

**Never tell someone they're wrong.** Ask questions. Let them arrive at the conclusion themselves. The moment you assert, you create resistance. The moment you ask, you create curiosity.

**If you're wrong, admit it quickly.** We tried to build our own solution for computation. Rust beat us by 50 years. We said so. That honesty earned more trust than being right would have.

**Let the other person feel the idea is theirs.** The framework's questions are designed so the reader answers them in their own head. "Can you have a part without a whole?" is not an assertion. It's an invitation.

**Let the other person save face.** 97 patches exist because brilliant people solved real problems independently. Those patches aren't wrong. They're unconnected. Nobody's work is diminished. The pattern is what's missing, not the effort.

**Ask questions instead of giving direct orders.** "What if we moved AI inference pipelines to Rust?" not "Move to Rust." "Would you write it 97 times?" not "You wrote it 97 times."

**Talk in terms of the other person's interests.** Developers care about code quality. Physicists care about unification. AI researchers care about capabilities. The water problem is the door. Each reader finds their own room.

---

## How to Build

**Minimalist extremism: strip away everything until it hurts, then only put back what is necessary.**

- **Search first, build last.** Look for the pattern that already does this. If you find something 80% there, extend it.
- **Be decisive.** When the simple path is clear, implement it.
- **Count your lines.** If your solution is significantly longer than comparable features, stop.
- **Don't create parallel roots.** If you're creating a new source of truth, you're creating a problem.

Before presenting anything, ask: **"Would the human look at this and say: 'Why didn't you just use X?'"** If you can imagine X, go find X.

Strip until it breaks. Then add the minimum to make it work.

---

## How to Present

**Different audiences, different doors.** The engineer needs the install command. The researcher needs the formal argument. The mathematician needs the Lean theorems. Write separate documents for separate audiences. One document trying to reach everyone reaches no one.

- [README.md](README.md) is for the engineer who asks "what does this do for me?"
- [PROOF_OF_CONCEPT.md](PROOF_OF_CONCEPT.md) is for the person who asks "why does this work?"
- [PROOFS.md](PROOFS.md) is for the person who asks "prove it"
- [Origin README](https://github.com/knoxvilledatabase/origin-lang) is for the developer who wants to use it today
- [RESEARCH.md](https://github.com/knoxvilledatabase/origin/blob/main/RESEARCH.md) is for the AI safety researcher

**Show, don't describe.** A code block with `# still here` pointing at a preserved value beats any paragraph explaining what `last` does. Three implementations side by side beat a prose argument about type system differences. Demonstration wins over explanation every time.

**Publish before you pitch.** `pip install origin-lang` working is more credible than any README. Make the install command real before writing the post. A live package signals "this is real." A GitHub link signals "this is a project."

**Honesty is a strategy, not a concession.** Every time we made the argument more honest, it got stronger. The Python column says "opt-in" not "broken." The `divide` function says "demonstration, not domain rule." The energy claim says "Python to Rust, not the theory alone." Overclaiming loses the exact people you need to convince. The honest version wins every argument the inflated version loses.

---

## How to Continue

Read [PROOF_OF_CONCEPT.md](PROOF_OF_CONCEPT.md) first. Then read [lean/OriginalArith/Foundation.lean](lean/OriginalArith/Foundation.lean). Then pick the next step from "What Remains" at the bottom of PROOF_OF_CONCEPT.md.

**The seed:** `Val α` — three constructors (`origin`, `container`, `contents`), four rules.

**The method:** Prove theorems that currently exist in Mathlib, but derive them from the seed instead of asserting them as axioms or typeclasses.

**Test to failure:** For each theorem attempted, either it derives cleanly from the seed or it doesn't. If it doesn't, that's information — either the seed needs something added back, or the theorem genuinely requires structure the seed doesn't have.

**The ones that derive cleanly become the evidence. The ones that break define the honest boundary of the claim.**

Build each step as a new file in `lean/OriginalArith/`. All files must build clean with `lake build` from the `lean/` directory. Zero errors. Zero sorries. Zero overclaims. If a build fails, the failure is information — report what it means honestly.

The kill switch is live at every level.
