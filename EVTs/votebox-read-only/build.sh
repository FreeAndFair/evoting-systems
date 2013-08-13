#!/bin/bash

export CLASSPATH=".:./lib/junit.jar:./lib/sdljava.jar"

echo "deleting"
find . -name "*.class*" | xargs -I {} rm {}
echo "building"
find ./verifier/ -name "*.java" | xargs javac
find ./votebox/ -name "*.java" | xargs javac
