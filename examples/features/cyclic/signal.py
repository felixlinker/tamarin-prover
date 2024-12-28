#!/usr/bin/env python3

from sys import stdin, exit

def splitter(line):
  splitted = line.split(':')
  return (splitted[0], splitted[1].strip())

lines = list(map(splitter, stdin.readlines()))
if not lines:
  exit(0)

goals = []

for (nr, line) in lines:
  if '!KU( kdf' in line or '!KU( ~' in line:
    goals.insert(0, nr)
  if not 'splitEqs' in line:
    goals.append(nr)

for nr in goals:
  print(nr)
