# geisha.gs — Self-Hosting Geisha Compiler Makefile

CC          ?= cc
CFLAGS      ?= -O2 -Wall -Wextra -Iruntime/include
STAGE0      ?= miko
BUILD_DIR   := build
RUNTIME_LIB := $(BUILD_DIR)/libgeisha_runtime.a
ENTRY       := src/mod.gs

.PHONY: all runtime stdlib-bundle stage1 stage2 stage3 bootstrap test clean

all: stage2

$(BUILD_DIR):
	@mkdir -p $(BUILD_DIR)

runtime: $(RUNTIME_LIB)

$(RUNTIME_LIB): runtime/base.c runtime/runtime/gc_bitmap.c runtime/runtime/gs_conc.c runtime/include/*.h | $(BUILD_DIR)
	MACOSX_DEPLOYMENT_TARGET=14.0 $(CC) $(CFLAGS) -c runtime/base.c -o $(BUILD_DIR)/base.o
	MACOSX_DEPLOYMENT_TARGET=14.0 $(CC) $(CFLAGS) -c runtime/runtime/gc_bitmap.c -o $(BUILD_DIR)/gc_bitmap.o
	MACOSX_DEPLOYMENT_TARGET=14.0 $(CC) $(CFLAGS) -c runtime/runtime/gs_conc.c -o $(BUILD_DIR)/gs_conc.o
	ar rcs $(RUNTIME_LIB) $(BUILD_DIR)/base.o $(BUILD_DIR)/gc_bitmap.o $(BUILD_DIR)/gs_conc.o

stdlib-bundle:
	python3 scripts/gen_stdlib.py

stage1: $(BUILD_DIR)/geisha1

$(BUILD_DIR)/geisha1: $(RUNTIME_LIB) src/*.gs
	$(STAGE0) --src-root . --runtime $(RUNTIME_LIB) -o $(BUILD_DIR)/geisha1 $(ENTRY)

stage2: $(BUILD_DIR)/geisha2

$(BUILD_DIR)/stage2.ll: $(BUILD_DIR)/geisha1 src/*.gs
	$(BUILD_DIR)/geisha1 --src-root . -e -o $(BUILD_DIR)/stage2.ll $(ENTRY)

$(BUILD_DIR)/geisha2: $(BUILD_DIR)/stage2.ll $(RUNTIME_LIB)
	MACOSX_DEPLOYMENT_TARGET=14.0 $(CC) -O2 -Wno-override-module -pthread -x ir $(BUILD_DIR)/stage2.ll -x none $(RUNTIME_LIB) -o $(BUILD_DIR)/geisha2

stage3: $(BUILD_DIR)/geisha3

$(BUILD_DIR)/stage3.ll: $(BUILD_DIR)/geisha2 src/*.gs
	$(BUILD_DIR)/geisha2 --src-root . -e -o $(BUILD_DIR)/stage3.ll $(ENTRY)

$(BUILD_DIR)/geisha3: $(BUILD_DIR)/stage3.ll $(RUNTIME_LIB)
	MACOSX_DEPLOYMENT_TARGET=14.0 $(CC) -O2 -Wno-override-module -pthread -x ir $(BUILD_DIR)/stage3.ll -x none $(RUNTIME_LIB) -o $(BUILD_DIR)/geisha3

bootstrap: $(BUILD_DIR)/stage2.ll $(BUILD_DIR)/stage3.ll $(BUILD_DIR)/geisha3
	diff -u $(BUILD_DIR)/stage2.ll $(BUILD_DIR)/stage3.ll
	@echo "Fixed-point verified: stage2.ll and stage3.ll are byte-for-byte identical."

test: $(BUILD_DIR)/geisha2
	GEISHA_BIN=$(BUILD_DIR)/geisha2 GEISHA_RUNTIME=$(RUNTIME_LIB) sh tests/run_tests.sh

clean:
	rm -rf $(BUILD_DIR)
