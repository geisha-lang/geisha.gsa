# geisha.gsa — Self-Hosting Geisha Compiler Makefile

UNAME_S := $(shell uname -s)
UNAME_M := $(shell uname -m)

ifeq ($(origin CC),default)
  CC := clang
endif
CC                  ?= clang
BUILD_DIR           := build
DIST_DIR            ?= dist
VERSION             ?= dev
RUNTIME_LIB         := $(BUILD_DIR)/libgeisha_runtime.a
RUNTIME_IOS_LIB     := $(BUILD_DIR)/libgeisha_runtime_ios.a
RUNTIME_IOS_SIM_LIB := $(BUILD_DIR)/libgeisha_runtime_ios_sim.a
WASM_RT_OBJ         := $(BUILD_DIR)/wasm_rt.o
BOOTSTRAP_SEED      := bootstrap/stage0.ll.xz
ENTRY               := src/geisha.gsa
PREFIX              ?= $(HOME)/.geisha
XCODE_DEV           ?= /Applications/Xcode.app/Contents/Developer
IOS_CFLAGS          ?= -O2 -Wall -Wextra -Iruntime/include

ifeq ($(UNAME_S),Darwin)
  HOST_OS     := darwin
  HOST_ARCH   := $(if $(filter arm64 aarch64,$(UNAME_M)),arm64,x86_64)
  HOST_ENV    := MACOSX_DEPLOYMENT_TARGET=14.0
  HOST_TARGET := -target $(HOST_ARCH)-apple-macosx14.0
  HOST_LIBS   :=
else
  HOST_OS     := linux
  HOST_ARCH   := $(if $(filter aarch64 arm64,$(UNAME_M)),arm64,x86_64)
  HOST_ENV    :=
  HOST_TARGET :=
  HOST_LIBS   := -lm
endif

CFLAGS ?= $(HOST_TARGET) -O2 -Wall -Wextra -Iruntime/include

WASM_CC ?= $(shell \
	if [ -x /opt/homebrew/opt/llvm/bin/clang ]; then echo /opt/homebrew/opt/llvm/bin/clang; \
	elif [ -x /opt/homebrew/opt/llvm@20/bin/clang ]; then echo /opt/homebrew/opt/llvm@20/bin/clang; \
	elif [ -x /usr/local/opt/llvm/bin/clang ]; then echo /usr/local/opt/llvm/bin/clang; \
	elif [ -x /usr/local/opt/llvm@20/bin/clang ]; then echo /usr/local/opt/llvm@20/bin/clang; \
	elif command -v clang-20 >/dev/null 2>&1; then command -v clang-20; \
	else echo clang; fi)
WASM_FLAGS ?= --target=wasm32 -O2 -mbulk-memory -mnontrapping-fptoint

ifeq ($(origin STAGE0),undefined)
  STAGE0     := $(BUILD_DIR)/geisha0
  STAGE0_DEP := $(BUILD_DIR)/geisha0
else
  STAGE0_DEP :=
endif

.PHONY: all runtime runtime-ios runtime-ios-sim wasm-runtime stdlib-bundle check-docs stage0 stage1 stage2 stage3 bootstrap update-bootstrap dist install test test-sanitizers verify-core clean

all: stage2

$(BUILD_DIR):
	@mkdir -p $(BUILD_DIR)

runtime: $(RUNTIME_LIB)

wasm-runtime: $(WASM_RT_OBJ)

$(WASM_RT_OBJ): runtime/wasm_rt.c | $(BUILD_DIR)
	$(WASM_CC) $(WASM_FLAGS) -Wall -Wextra -nostdlib -ffreestanding -c runtime/wasm_rt.c -o $(WASM_RT_OBJ)

$(RUNTIME_LIB): runtime/base.c runtime/gs_sys.c runtime/runtime/gc_bitmap.c runtime/runtime/gs_conc.c runtime/include/*.h | $(BUILD_DIR)
	$(HOST_ENV) $(CC) $(CFLAGS) -c runtime/base.c -o $(BUILD_DIR)/base.o
	$(HOST_ENV) $(CC) $(CFLAGS) -c runtime/gs_sys.c -o $(BUILD_DIR)/gs_sys.o
	$(HOST_ENV) $(CC) $(CFLAGS) -c runtime/runtime/gc_bitmap.c -o $(BUILD_DIR)/gc_bitmap.o
	$(HOST_ENV) $(CC) $(CFLAGS) -c runtime/runtime/gs_conc.c -o $(BUILD_DIR)/gs_conc.o
	ar rcs $(RUNTIME_LIB) $(BUILD_DIR)/base.o $(BUILD_DIR)/gs_sys.o $(BUILD_DIR)/gc_bitmap.o $(BUILD_DIR)/gs_conc.o

runtime-ios: $(RUNTIME_IOS_LIB)

$(RUNTIME_IOS_LIB): runtime/base.c runtime/gs_sys.c runtime/runtime/gc_bitmap.c runtime/runtime/gs_conc.c runtime/include/*.h | $(BUILD_DIR)
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphoneos clang -target arm64-apple-ios16.0 $(IOS_CFLAGS) -c runtime/base.c -o $(BUILD_DIR)/ios_base.o
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphoneos clang -target arm64-apple-ios16.0 $(IOS_CFLAGS) -c runtime/gs_sys.c -o $(BUILD_DIR)/ios_gs_sys.o
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphoneos clang -target arm64-apple-ios16.0 $(IOS_CFLAGS) -c runtime/runtime/gc_bitmap.c -o $(BUILD_DIR)/ios_gc_bitmap.o
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphoneos clang -target arm64-apple-ios16.0 $(IOS_CFLAGS) -c runtime/runtime/gs_conc.c -o $(BUILD_DIR)/ios_gs_conc.o
	ar rcs $(RUNTIME_IOS_LIB) $(BUILD_DIR)/ios_base.o $(BUILD_DIR)/ios_gs_sys.o $(BUILD_DIR)/ios_gc_bitmap.o $(BUILD_DIR)/ios_gs_conc.o

runtime-ios-sim: $(RUNTIME_IOS_SIM_LIB)

$(RUNTIME_IOS_SIM_LIB): runtime/base.c runtime/gs_sys.c runtime/runtime/gc_bitmap.c runtime/runtime/gs_conc.c runtime/include/*.h | $(BUILD_DIR)
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphonesimulator clang -target arm64-apple-ios16.0-simulator $(IOS_CFLAGS) -c runtime/base.c -o $(BUILD_DIR)/iossim_base.o
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphonesimulator clang -target arm64-apple-ios16.0-simulator $(IOS_CFLAGS) -c runtime/gs_sys.c -o $(BUILD_DIR)/iossim_gs_sys.o
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphonesimulator clang -target arm64-apple-ios16.0-simulator $(IOS_CFLAGS) -c runtime/runtime/gc_bitmap.c -o $(BUILD_DIR)/iossim_gc_bitmap.o
	DEVELOPER_DIR=$(XCODE_DEV) IPHONEOS_DEPLOYMENT_TARGET=16.0 xcrun --sdk iphonesimulator clang -target arm64-apple-ios16.0-simulator $(IOS_CFLAGS) -c runtime/runtime/gs_conc.c -o $(BUILD_DIR)/iossim_gs_conc.o
	ar rcs $(RUNTIME_IOS_SIM_LIB) $(BUILD_DIR)/iossim_base.o $(BUILD_DIR)/iossim_gs_sys.o $(BUILD_DIR)/iossim_gc_bitmap.o $(BUILD_DIR)/iossim_gs_conc.o

stdlib-bundle:
	python3 scripts/gen_stdlib.py

check-docs:
	python3 scripts/check_agent_docs.py

stage0: $(BUILD_DIR)/geisha0

$(BUILD_DIR)/stage0.ll: $(BOOTSTRAP_SEED) | $(BUILD_DIR)
	xz -dc $(BOOTSTRAP_SEED) > $(BUILD_DIR)/stage0.ll

$(BUILD_DIR)/geisha0: $(BUILD_DIR)/stage0.ll $(RUNTIME_LIB)
	$(HOST_ENV) $(CC) $(HOST_TARGET) -O2 -Wno-override-module -pthread -x ir $(BUILD_DIR)/stage0.ll -x none $(RUNTIME_LIB) $(HOST_LIBS) -o $(BUILD_DIR)/geisha0

stage1: $(BUILD_DIR)/geisha1

$(BUILD_DIR)/geisha1: $(RUNTIME_LIB) $(STAGE0_DEP) src/*.gsa
	$(HOST_ENV) CC="$(CC)" $(STAGE0) --src-root . --runtime $(RUNTIME_LIB) -o $(BUILD_DIR)/geisha1 $(ENTRY)

stage2: $(BUILD_DIR)/geisha2

$(BUILD_DIR)/stage2.ll: $(BUILD_DIR)/geisha1 src/*.gsa
	$(BUILD_DIR)/geisha1 --src-root . -e -o $(BUILD_DIR)/stage2.ll $(ENTRY)

$(BUILD_DIR)/geisha2: $(BUILD_DIR)/stage2.ll $(RUNTIME_LIB)
	$(HOST_ENV) $(CC) $(HOST_TARGET) -O2 -Wno-override-module -pthread -x ir $(BUILD_DIR)/stage2.ll -x none $(RUNTIME_LIB) $(HOST_LIBS) -o $(BUILD_DIR)/geisha2

stage3: $(BUILD_DIR)/geisha3

$(BUILD_DIR)/stage3.ll: $(BUILD_DIR)/geisha2 src/*.gsa
	$(BUILD_DIR)/geisha2 --src-root . -e -o $(BUILD_DIR)/stage3.ll $(ENTRY)

$(BUILD_DIR)/geisha3: $(BUILD_DIR)/stage3.ll $(RUNTIME_LIB)
	$(HOST_ENV) $(CC) $(HOST_TARGET) -O2 -Wno-override-module -pthread -x ir $(BUILD_DIR)/stage3.ll -x none $(RUNTIME_LIB) $(HOST_LIBS) -o $(BUILD_DIR)/geisha3

bootstrap: $(BUILD_DIR)/stage2.ll $(BUILD_DIR)/stage3.ll $(BUILD_DIR)/geisha3
	diff -u $(BUILD_DIR)/stage2.ll $(BUILD_DIR)/stage3.ll
	@echo "Fixed-point verified: stage2.ll and stage3.ll are byte-for-byte identical."

update-bootstrap: bootstrap
	@mkdir -p bootstrap
	xz -9 -e -c $(BUILD_DIR)/stage3.ll > $(BOOTSTRAP_SEED)
	@echo "Updated portable bootstrap seed $(BOOTSTRAP_SEED)"

dist: $(BUILD_DIR)/geisha3 $(RUNTIME_LIB) $(WASM_RT_OBJ)
	VERSION="$(VERSION)" DIST_DIR="$(DIST_DIR)" BUILD_DIR="$(BUILD_DIR)" CC="$(CC)" sh scripts/package_release.sh

install: $(BUILD_DIR)/geisha3 $(RUNTIME_LIB) $(WASM_RT_OBJ)
	@mkdir -p "$(PREFIX)/bin" "$(PREFIX)/lib"
	cp $(BUILD_DIR)/geisha3 "$(PREFIX)/bin/geisha"
	cp $(RUNTIME_LIB) "$(PREFIX)/lib/libgeisha_runtime.a"
	cp $(WASM_RT_OBJ) "$(PREFIX)/lib/wasm_rt.o"
	@if [ -f "$(RUNTIME_IOS_LIB)" ]; then cp "$(RUNTIME_IOS_LIB)" "$(PREFIX)/lib/libgeisha_runtime_ios.a"; fi
	@if [ -f "$(RUNTIME_IOS_SIM_LIB)" ]; then cp "$(RUNTIME_IOS_SIM_LIB)" "$(PREFIX)/lib/libgeisha_runtime_ios_sim.a"; fi
	@if [ -d "$(HOME)/.local/bin" ]; then ln -sf "$(PREFIX)/bin/geisha" "$(HOME)/.local/bin/geisha"; fi
	@echo "Installed geisha toolchain to $(PREFIX)/bin/geisha"

test: check-docs $(BUILD_DIR)/geisha2
	CC="$(CC)" GEISHA_BIN=$(BUILD_DIR)/geisha2 GEISHA_RUNTIME=$(RUNTIME_LIB) sh tests/run_tests.sh

test-sanitizers: $(BUILD_DIR)/geisha2
	CC="$(CC)" GEISHA_BIN=$(BUILD_DIR)/geisha2 sh tests/run_sanitizers.sh

verify-core: $(BUILD_DIR)/geisha2
	cd formal && lake build geisha-check
	CC="$(CC)" GEISHA_BIN=$(BUILD_DIR)/geisha2 GEISHA_RUNTIME=$(RUNTIME_LIB) sh formal/tests/verify_core.sh

clean:
	rm -rf $(BUILD_DIR) $(DIST_DIR)
