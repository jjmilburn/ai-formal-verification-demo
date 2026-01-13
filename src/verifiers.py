"""
Verifier Wrappers for Formal Verification Tools

Provides uniform interfaces for running Dafny, Lean4, and TLC verification.
"""

import subprocess
import tempfile
import os
from pathlib import Path
from dataclasses import dataclass
from typing import Optional
import shutil


@dataclass
class VerificationResult:
    """Result from a verification attempt."""
    success: bool
    output: str
    error: Optional[str] = None
    returncode: int = 0


class DafnyVerifier:
    """Wrapper for Dafny verification."""

    def __init__(self, dafny_path: str = "dafny"):
        """Initialize Dafny verifier.

        Args:
            dafny_path: Path to dafny executable.
        """
        self.dafny_path = dafny_path
        self._check_installation()

    def _check_installation(self):
        """Verify Dafny is installed."""
        if not shutil.which(self.dafny_path):
            raise RuntimeError(
                f"Dafny not found at '{self.dafny_path}'. "
                "Run setup.sh or install from https://github.com/dafny-lang/dafny"
            )

    def verify(self, code: str) -> VerificationResult:
        """Verify Dafny code.

        Args:
            code: Dafny source code to verify.

        Returns:
            VerificationResult with success status and output.
        """
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".dfy", delete=False
        ) as f:
            f.write(code)
            temp_path = f.name

        try:
            result = subprocess.run(
                [self.dafny_path, "verify", temp_path],
                capture_output=True,
                text=True,
                timeout=60,
            )

            output = result.stdout + result.stderr
            success = result.returncode == 0 and "0 errors" in output

            # Extract error details if verification failed
            error = None
            if not success:
                error = self._extract_error(output)

            return VerificationResult(
                success=success,
                output=output,
                error=error,
                returncode=result.returncode,
            )

        except subprocess.TimeoutExpired:
            return VerificationResult(
                success=False,
                output="",
                error="Verification timed out after 60 seconds",
                returncode=-1,
            )
        finally:
            os.unlink(temp_path)

    def verify_file(self, path: str) -> VerificationResult:
        """Verify a Dafny file.

        Args:
            path: Path to .dfy file.

        Returns:
            VerificationResult with success status and output.
        """
        with open(path) as f:
            code = f.read()
        return self.verify(code)

    def _extract_error(self, output: str) -> str:
        """Extract the most relevant error message from Dafny output."""
        lines = output.split("\n")
        errors = [l for l in lines if "Error" in l or "error" in l]
        if errors:
            return "\n".join(errors[:5])  # First 5 error lines
        return output[:500]  # Fallback to first 500 chars


class LeanVerifier:
    """Wrapper for Lean4 verification."""

    def __init__(self, lean_path: str = "lean"):
        """Initialize Lean verifier.

        Args:
            lean_path: Path to lean executable.
        """
        self.lean_path = lean_path
        self._check_installation()

    def _check_installation(self):
        """Verify Lean is installed."""
        if not shutil.which(self.lean_path):
            raise RuntimeError(
                f"Lean not found at '{self.lean_path}'. "
                "Run setup.sh or install via elan: https://elan.lean-lang.org"
            )

    def verify(self, code: str) -> VerificationResult:
        """Verify Lean4 code.

        Args:
            code: Lean4 source code to verify.

        Returns:
            VerificationResult with success status and output.
        """
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False
        ) as f:
            f.write(code)
            temp_path = f.name

        try:
            result = subprocess.run(
                [self.lean_path, temp_path],
                capture_output=True,
                text=True,
                timeout=60,
            )

            output = result.stdout + result.stderr
            success = result.returncode == 0 and "error" not in output.lower()

            error = None
            if not success:
                error = self._extract_error(output)

            return VerificationResult(
                success=success,
                output=output,
                error=error,
                returncode=result.returncode,
            )

        except subprocess.TimeoutExpired:
            return VerificationResult(
                success=False,
                output="",
                error="Verification timed out after 60 seconds",
                returncode=-1,
            )
        finally:
            os.unlink(temp_path)

    def verify_file(self, path: str) -> VerificationResult:
        """Verify a Lean file.

        Args:
            path: Path to .lean file.

        Returns:
            VerificationResult with success status and output.
        """
        with open(path) as f:
            code = f.read()
        return self.verify(code)

    def _extract_error(self, output: str) -> str:
        """Extract the most relevant error message from Lean output."""
        lines = output.split("\n")
        errors = [l for l in lines if "error" in l.lower()]
        if errors:
            return "\n".join(errors[:5])
        return output[:500]


class TLCVerifier:
    """Wrapper for TLA+ TLC model checker."""

    def __init__(self, tla_jar: Optional[str] = None):
        """Initialize TLC verifier.

        Args:
            tla_jar: Path to tla2tools.jar. Defaults to ~/.tla/tla2tools.jar
        """
        if tla_jar is None:
            tla_jar = os.path.expanduser("~/.tla/tla2tools.jar")

        self.tla_jar = tla_jar
        self._check_installation()

    def _check_installation(self):
        """Verify TLC is installed."""
        if not os.path.exists(self.tla_jar):
            raise RuntimeError(
                f"TLA+ tools not found at '{self.tla_jar}'. "
                "Run setup.sh to install."
            )

    def verify(
        self,
        spec: str,
        config: Optional[str] = None,
        workers: int = 4
    ) -> VerificationResult:
        """Verify a TLA+ specification with TLC.

        Args:
            spec: TLA+ specification code.
            config: Optional TLC config. If None, uses defaults from spec.
            workers: Number of TLC worker threads.

        Returns:
            VerificationResult with success status and output.
        """
        # Create temp directory for TLA+ files
        with tempfile.TemporaryDirectory() as tmpdir:
            spec_path = Path(tmpdir) / "Spec.tla"
            spec_path.write_text(spec)

            if config:
                cfg_path = Path(tmpdir) / "Spec.cfg"
                cfg_path.write_text(config)

            try:
                cmd = [
                    "java", "-jar", self.tla_jar,
                    "-tool", "tlc2.TLC",
                    "-workers", str(workers),
                    "-cleanup",
                    str(spec_path),
                ]

                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=120,
                    cwd=tmpdir,
                )

                output = result.stdout + result.stderr

                # TLC success indicators
                success = (
                    "Model checking completed" in output and
                    "Error:" not in output and
                    "Invariant" not in output.split("is violated")[-1] if "is violated" in output else True
                )

                # More precise success check
                if "Error:" in output or "is violated" in output:
                    success = False

                error = None
                if not success:
                    error = self._extract_error(output)

                return VerificationResult(
                    success=success,
                    output=output,
                    error=error,
                    returncode=result.returncode,
                )

            except subprocess.TimeoutExpired:
                return VerificationResult(
                    success=False,
                    output="",
                    error="TLC timed out after 120 seconds",
                    returncode=-1,
                )

    def verify_file(
        self,
        path: str,
        config_path: Optional[str] = None
    ) -> VerificationResult:
        """Verify a TLA+ file.

        Args:
            path: Path to .tla file.
            config_path: Optional path to .cfg file.

        Returns:
            VerificationResult with success status and output.
        """
        with open(path) as f:
            spec = f.read()

        config = None
        if config_path:
            with open(config_path) as f:
                config = f.read()

        return self.verify(spec, config)

    def _extract_error(self, output: str) -> str:
        """Extract counterexample or error from TLC output."""
        lines = output.split("\n")

        # Look for counterexample trace
        in_trace = False
        trace_lines = []

        for line in lines:
            if "Error:" in line or "is violated" in line:
                in_trace = True
            if in_trace:
                trace_lines.append(line)
                if len(trace_lines) > 30:
                    break

        if trace_lines:
            return "\n".join(trace_lines)

        # Fallback: just return errors
        errors = [l for l in lines if "Error" in l or "error" in l]
        if errors:
            return "\n".join(errors[:5])

        return output[:500]


# === Convenience function ===

def get_verifier(language: str):
    """Get the appropriate verifier for a language.

    Args:
        language: One of 'dafny', 'lean', 'tlaplus'

    Returns:
        Verifier instance.
    """
    verifiers = {
        "dafny": DafnyVerifier,
        "lean": LeanVerifier,
        "tlaplus": TLCVerifier,
        "tla+": TLCVerifier,
    }

    if language.lower() not in verifiers:
        raise ValueError(f"Unknown language: {language}. Choose from: {list(verifiers.keys())}")

    return verifiers[language.lower()]()
