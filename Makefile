# cuvee.jar, which Cuvee.sh runs, and cuvee.native, a native executable built from it by GraalVM

# the native launcher of mill 1.1.8, as downloaded to its cache, since mill is not on the PATH
MILL ?= $(HOME)/.cache/mill/download/1.1.8-native-linux-amd64
GRAALVM ?= graalvm-java25:25.0.2
NATIVE_IMAGE ?= $(shell coursier java-home --jvm $(GRAALVM))/bin/native-image

.PHONY: all native
all: cuvee.jar
native: cuvee.native

# mill decides what to rebuild, hence always called
.PHONY: cuvee.jar
cuvee.jar:
	$(MILL) -i assembly < /dev/null
	cp out/assembly.dest/out.jar cuvee.jar

# native-image misses the resources in the jar itself, whose zip archive follows a launcher
# script, hence the unpacked jar; resources/META-INF/native-image includes the resources
cuvee.native: cuvee.jar
	rm -rf out/native && mkdir -p out/native/classes
	cd out/native/classes && unzip -q ../../../cuvee.jar || test $$? -eq 1
	$(NATIVE_IMAGE) -cp out/native/classes cuvee.Cuvee -o cuvee.native --no-fallback
