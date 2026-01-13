#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
VENV_DIR="$SCRIPT_DIR/.venv"

echo "=== AI + Formal Verification Demo Setup ==="
echo ""

# Check for required base tools
check_command() {
    if ! command -v $1 &> /dev/null; then
        echo "ERROR: $1 is required but not installed."
        return 1
    fi
    echo "OK: $1 found"
}

echo "Checking base requirements..."
check_command python3

# --- Dafny Installation ---
echo ""
echo "=== Installing Dafny ==="
if command -v dafny &> /dev/null; then
    echo "Dafny already installed: $(dafny --version 2>&1 | head -1)"
else
    if [[ "$OSTYPE" == "darwin"* ]]; then
        echo "Installing Dafny via Homebrew..."
        brew install dafny
    elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
        echo "Installing Dafny via dotnet..."
        if ! command -v dotnet &> /dev/null; then
            echo "Please install .NET SDK first: https://dotnet.microsoft.com/download"
            exit 1
        fi
        dotnet tool install --global dafny
    else
        echo "Please install Dafny manually: https://github.com/dafny-lang/dafny/releases"
        exit 1
    fi
fi

# --- Lean4 Installation ---
echo ""
echo "=== Installing Lean4 (via elan) ==="
if command -v lean &> /dev/null; then
    echo "Lean already installed: $(lean --version)"
else
    echo "Installing elan (Lean version manager)..."
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
    source "$HOME/.elan/env"
    echo "Lean installed: $(lean --version)"
fi

# --- TLA+ Tools Installation ---
echo ""
echo "=== Installing TLA+ Tools ==="
TLA_DIR="$HOME/.tla"
if [ -f "$TLA_DIR/tla2tools.jar" ]; then
    echo "TLA+ tools already installed at $TLA_DIR"
else
    echo "Downloading TLA+ tools..."
    mkdir -p "$TLA_DIR"
    curl -L -o "$TLA_DIR/tla2tools.jar" \
        "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
    echo "TLA+ tools installed at $TLA_DIR/tla2tools.jar"
fi

# Create helper script for TLC
cat > "$TLA_DIR/tlc" << 'EOF'
#!/bin/bash
java -jar "$HOME/.tla/tla2tools.jar" -tool tlc2.TLC "$@"
EOF
chmod +x "$TLA_DIR/tlc"
echo "TLC helper script created at $TLA_DIR/tlc"

# --- Python Virtual Environment ---
echo ""
echo "=== Setting Up Python Virtual Environment ==="
cd "$SCRIPT_DIR"

if [ -d "$VENV_DIR" ]; then
    echo "Virtual environment already exists at $VENV_DIR"
else
    echo "Creating virtual environment..."
    python3 -m venv "$VENV_DIR"
fi

echo "Activating virtual environment..."
source "$VENV_DIR/bin/activate"

echo "Upgrading pip..."
pip install --upgrade pip --quiet

echo "Installing Python dependencies..."
pip install -e .

echo ""
echo "=== Setup Complete ==="
echo ""
echo "Tools installed:"
echo "  - Dafny: $(dafny --version 2>&1 | head -1 || echo 'check installation')"
echo "  - Lean:  $(lean --version 2>&1 || echo 'run: source ~/.elan/env')"
echo "  - TLC:   $TLA_DIR/tlc"
echo ""
echo "To use TLC, add to your PATH:"
echo "  export PATH=\"\$PATH:$TLA_DIR\""
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "NEXT STEPS:"
echo ""
echo "  1. Activate the virtual environment:"
echo ""
echo "     source .venv/bin/activate"
echo ""
echo "  2. Run the notebooks:"
echo ""
echo "     jupyter notebook notebooks/"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
