#!/usr/bin/env python3

from sys import argv, stdin, exit
import re

def splitter(line):
  splitted = line.split(':')
  return (splitted[0], splitted[1].strip())

lines = list(map(splitter, stdin.readlines()))
if not lines:
  exit(0)
lines = sorted(lines, key=lambda t: len(t[1]), reverse=True)

def subToken(token, line):
  (num, goal) = line
  if isinstance(token, str):
    return num if token in goal else None
  else:
    return num if token.search(goal) is not None else None

def matchAgainstList(priorityList, lines):
  for token in priorityList:
    try:
      return next(filter(bool, map(lambda line: subToken(token, line), lines)))
    except StopIteration:
      pass

match = None
if argv[1] == 'KeysHonest':
  match = matchAgainstList([
    re.compile(r'@ #y \)$'),
    re.compile(r'Honest.+inv'),
    re.compile(r'KU.+inv\(+~'),
    '!KU( ~',
    'splitEqs',
    'Honest',
  ], lines)

if match is not None:
  print(match)
