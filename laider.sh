#!/bin/bash

DEFAULT_ENDPOINT="http://192.168.1.104:11434"
DEFAULT_MODEL="hf.co/bartowski/THUDM_GLM-4-32B-0414-GGUF:Q6_K"

# parse command line arguments for configuration
OLLAMA_ENDPOINT="$DEFAULT_ENDPOINT"
MODEL_NAME="$DEFAULT_MODEL"
while getopts u:m: flag
do
    case "${flag}" in
        u) OLLAMA_ENDPOINT=${OPTARG};;
        m) MODEL_NAME=${OPTARG};;
    esac
done

# aider directory setup
if [ ! -d ".aider" ]; then
    echo "creating local .aider directory, add it to .gitignore"
    mkdir .aider
fi

# aider venv setup
if [ ! -d ".aider/venv" ]; then
    echo "aider venv not found, creating it an installing aider"
    python3 -m venv .aider/venv
    source .aider/venv/bin/activate
    pip install aider-install
    aider-install
else
    source .aider/venv/bin/activate
fi

export OLLAMA_API_BASE=$OLLAMA_ENDPOINT
echo "OLLAMA_API_BASE set to: $OLLAMA_API_BASE"
echo "using model: $MODEL_NAME"

echo "Starting aider..."
aider --model ollama_chat/"$MODEL_NAME" --no-auto-commits
