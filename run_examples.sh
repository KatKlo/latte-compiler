#!/bin/bash

# Path to program
PROGRAM="./latc_x86_64"

# List of directories containing input files
GOOD_INPUT_DIRS=("lattests/good" "lattests/extensions/arrays1")
BAD_INPUT_DIRS=("lattests/bad")

# Test function
function run_test() {
  local INPUT_DIR=$1
  echo "Testing $INPUT_DIR"

  for INPUT_FILE in $INPUT_DIR/*.lat; do
    # Prepare filenames,
    BASENAME=${INPUT_FILE%.*}
    OUTPUT_FILE="$BASENAME.output"
    OUT_FILE="$BASENAME.out"
    ERR_FILE="$BASENAME.err"

    # Run program on input file and save output
    $PROGRAM $INPUT_FILE 1> $OUT_FILE 2> $ERR_FILE

    # Check if errors from compilation process are returned properly
    if [ ! -s $ERR_FILE ]; then
      if [ $2 == false ]; then
        echo "${INPUT_FILE} ERROR (error in latte code should be detected)"
      fi
    else
      if [ $2 == true ]; then
        echo "${INPUT_FILE} ERROR (good latte code caused error)"
      fi
    fi

    # compare output if expected
    if [ $2 == true ]; then
      if ! cmp -s "${OUTPUT_FILE}" "${OUT_FILE}"; then
        echo "${INPUT_FILE} ERROR (incorrect output)"
      fi
    fi

    # remove out file if empty
    if [ ! -s $OUT_FILE ]; then
      rm $OUT_FILE
    fi

    # remove err file if empty
    if [ ! -s $ERR_FILE ]; then
      rm $ERR_FILE
    fi

  done
}

# Test good examples
for INPUT_DIR in "${GOOD_INPUT_DIRS[@]}"; do
  run_test $INPUT_DIR true
done

# Test bad examples
for INPUT_DIR in "${BAD_INPUT_DIRS[@]}"; do
  run_test $INPUT_DIR false
done
