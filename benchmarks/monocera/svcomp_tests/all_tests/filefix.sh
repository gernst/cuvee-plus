#!/bin/bash

TOOLS="monocera seahorn"
for tool in TOOLS
do
  files=find polished_tests/${tool}/ -type f
  for file in files
  do
    cp original_svcomp_folders/*/${file}.yml
  done
done

X=find ./ -type f
  for file in X do
    cp ../../original_svcomp_folders/*/${file}.yml .
  done
