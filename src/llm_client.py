"""
LLM Client for Formal Verification Tasks

Uses Claude API via environment variable or Claude Code authentication.
Provides structured prompts for verification tasks across different languages.
"""

import os
from dataclasses import dataclass
from typing import Optional
import anthropic


@dataclass
class VerificationResult:
    """Result from a verification attempt."""
    success: bool
    output: str
    error: Optional[str] = None


@dataclass
class LLMResponse:
    """Response from the LLM."""
    content: str
    model: str
    input_tokens: int
    output_tokens: int


class LLMClient:
    """Client for LLM-assisted formal verification."""

    def __init__(self, model: str = "claude-sonnet-4-20250514"):
        """Initialize the LLM client.

        Args:
            model: The Claude model to use. Defaults to Claude 3.5 Sonnet.
        """
        self.client = anthropic.Anthropic()
        self.model = model
        self.conversation_history: list[dict] = []

    def reset_conversation(self):
        """Clear conversation history for a fresh start."""
        self.conversation_history = []

    def _make_request(self, system: str, messages: list[dict]) -> LLMResponse:
        """Make a request to the Claude API."""
        response = self.client.messages.create(
            model=self.model,
            max_tokens=4096,
            system=system,
            messages=messages,
        )

        return LLMResponse(
            content=response.content[0].text,
            model=response.model,
            input_tokens=response.usage.input_tokens,
            output_tokens=response.usage.output_tokens,
        )

    # === Dafny Methods ===

    def generate_dafny_annotations(
        self,
        code: str,
        error: Optional[str] = None
    ) -> LLMResponse:
        """Generate or fix Dafny annotations (loop invariants, pre/postconditions).

        Args:
            code: The Dafny code needing annotations.
            error: Optional verification error from a previous attempt.

        Returns:
            LLMResponse with the annotated code.
        """
        system = """You are an expert in formal verification with Dafny.
Your task is to add or fix annotations (requires, ensures, invariant, decreases)
to make the code verify successfully.

Rules:
1. Return ONLY the complete Dafny code, no explanations
2. Preserve the original logic - only add/fix annotations
3. Use minimal annotations that are sufficient for verification
4. Loop invariants must be inductive and maintained by the loop body
5. Ensure termination with decreases clauses where needed"""

        if error:
            user_msg = f"""The following Dafny code failed verification:

```dafny
{code}
```

Verification error:
{error}

Fix the annotations to make it verify. Return only the corrected code."""
        else:
            user_msg = f"""Add verification annotations to this Dafny code:

```dafny
{code}
```

Return only the annotated code."""

        messages = [{"role": "user", "content": user_msg}]
        return self._make_request(system, messages)

    # === Lean4 Methods ===

    def suggest_lean_tactics(
        self,
        theorem: str,
        goal_state: str,
        error: Optional[str] = None
    ) -> LLMResponse:
        """Suggest Lean4 tactics to prove a goal.

        Args:
            theorem: The theorem statement being proved.
            goal_state: Current proof state / goals.
            error: Optional error from previous tactic attempt.

        Returns:
            LLMResponse with suggested tactics.
        """
        system = """You are an expert in Lean4 theorem proving.
Your task is to suggest tactics to make progress on the current proof goal.

Rules:
1. Return ONLY the tactic(s), one per line, no explanations
2. Start with the most likely tactic to work
3. Use common tactics: simp, rfl, exact, apply, intro, cases, induction, omega
4. For arithmetic, try omega or decide
5. Be precise with hypothesis names"""

        if error:
            user_msg = f"""Proving theorem:
```lean
{theorem}
```

Current goal state:
{goal_state}

Previous tactic failed with:
{error}

Suggest alternative tactics. Return only the tactics."""
        else:
            user_msg = f"""Proving theorem:
```lean
{theorem}
```

Current goal state:
{goal_state}

Suggest tactics to make progress. Return only the tactics."""

        messages = [{"role": "user", "content": user_msg}]
        return self._make_request(system, messages)

    def generate_lean_proof(self, theorem: str) -> LLMResponse:
        """Generate a complete Lean4 proof.

        Args:
            theorem: The theorem to prove (just the statement).

        Returns:
            LLMResponse with the complete proof.
        """
        system = """You are an expert in Lean4 theorem proving.
Generate a complete proof for the given theorem.

Rules:
1. Return ONLY valid Lean4 code
2. Include necessary imports at the top
3. Use term-mode proofs when simple, tactic mode for complex proofs
4. Prefer automation (simp, omega, decide) when applicable"""

        user_msg = f"""Write a complete Lean4 proof for:

{theorem}

Return only the Lean4 code."""

        messages = [{"role": "user", "content": user_msg}]
        return self._make_request(system, messages)

    # === TLA+ Methods ===

    def generate_tlaplus_spec(
        self,
        description: str,
        error: Optional[str] = None
    ) -> LLMResponse:
        """Generate a TLA+ specification from natural language.

        Args:
            description: Natural language description of the system.
            error: Optional counterexample or error from TLC.

        Returns:
            LLMResponse with the TLA+ specification.
        """
        system = """You are an expert in TLA+ formal specification.
Your task is to write TLA+ specifications that can be model-checked with TLC.

Rules:
1. Return ONLY the complete TLA+ module, no explanations
2. Use PlusCal (--algorithm) when the system is naturally procedural
3. Include INVARIANT and PROPERTY definitions for verification
4. Define sensible CONSTANTS with example values for model checking
5. Keep state space bounded for TLC to explore"""

        if error:
            user_msg = f"""The TLA+ specification needs to be fixed.

Original description: {description}

TLC found this counterexample or error:
{error}

Generate a corrected specification. Return only the TLA+ code."""
        else:
            user_msg = f"""Write a TLA+ specification for:

{description}

Return only the TLA+ module code."""

        messages = [{"role": "user", "content": user_msg}]
        return self._make_request(system, messages)

    # === Generic Verification Loop ===

    def verification_loop(
        self,
        initial_code: str,
        verify_fn,
        fix_fn,
        max_attempts: int = 5
    ) -> tuple[bool, str, list[dict]]:
        """Run an iterative verification loop.

        Args:
            initial_code: Starting code to verify.
            verify_fn: Function that takes code and returns VerificationResult.
            fix_fn: Function that takes (code, error) and returns LLMResponse.
            max_attempts: Maximum fix attempts.

        Returns:
            Tuple of (success, final_code, attempt_history).
        """
        code = initial_code
        history = []

        for attempt in range(max_attempts):
            result = verify_fn(code)
            history.append({
                "attempt": attempt + 1,
                "code": code,
                "success": result.success,
                "output": result.output,
                "error": result.error,
            })

            if result.success:
                return True, code, history

            # Ask LLM to fix
            response = fix_fn(code, result.error or result.output)
            code = self._extract_code(response.content)
            history[-1]["llm_response"] = response.content
            history[-1]["tokens_used"] = response.input_tokens + response.output_tokens

        return False, code, history

    def _extract_code(self, response: str) -> str:
        """Extract code from LLM response, handling markdown fences."""
        # Try to extract from code blocks
        import re

        # Match ```language ... ``` or ``` ... ```
        pattern = r"```(?:\w+)?\n(.*?)```"
        matches = re.findall(pattern, response, re.DOTALL)

        if matches:
            return matches[0].strip()

        # No code blocks, return as-is (might be raw code)
        return response.strip()
