#!/bin/bash

# Source environment variables
source .env

# Check if required variables are set
if [ -z "$CSIHO" ]; then
  echo "Error: CSIHO variable is not set"
  exit 1
fi

if [ -z "$SCT" ]; then
  echo "Error: SCT variable is not set"
  exit 1
fi

if [ -z "$LAMBDAPI" ]; then
  echo "Error: LAMBDAPI variable is not set"
  exit 1
fi

# Check if filename argument is provided
if [ $# -eq 0 ]; then
  echo "Error: No filename provided"
  echo "Usage: $0 <filename>"
  exit 1
fi

FILENAME="$1"

# Run the lambdapi command
$LAMBDAPI check "$FILENAME" --confluence "$CSIHO -ext trs --stdin" --termination "cat > /tmp/output.xml && $SCT --no-color /tmp/output.xml"