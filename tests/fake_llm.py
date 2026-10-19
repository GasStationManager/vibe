#!/usr/bin/env python3
"""A fake agent CLI for tests: reads the vibe prompt on stdin and writes the
candidate named by $FAKE_CANDIDATE (a JSON file) to the path the prompt asks for."""
import os, re, sys, shutil
prompt = sys.stdin.read()
m = re.search(r"Write a JSON file to `([^`]+)`", prompt)
src = os.environ["FAKE_CANDIDATE"]
# FAKE_CANDIDATE may list several files separated by ':' -- one per round.
choices = src.split(":")
n = int(open(m.group(1) + ".round").read()) if os.path.exists(m.group(1) + ".round") else 0
open(m.group(1) + ".round", "w").write(str(n + 1))
shutil.copy(choices[min(n, len(choices) - 1)], m.group(1))
