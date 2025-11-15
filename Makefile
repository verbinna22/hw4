TARGET_EXEC:=interpreter
UNAME_S := $(shell uname -s)

ifeq ($(UNAME_S),Linux)
    CC=gcc
	CXX=g++
else ifeq ($(UNAME_S),Darwin)
    CC=clang
	CXX=clang++
    ARCH = -arch x86_64
endif

BUILD_DIR:=build
SRC_DIRS:=main/src
EXCLUDES:=
SRCS:=main/src/main.cpp
OBJS:=$(SRCS:%=$(BUILD_DIR)/%.o)
DEPS:=$(OBJS:.o=.d)
# INC_DIRS:=include lib
# INC_DIRS += $(shell find $(INC_DIRS) -type d)
LIBS:=:runtime.a
INC_FLAGS:=#$(addprefix -I, $(INC_DIRS))
CPP_FLAGS:=$(INC_FLAGS) -MMD -MP
LDFLAGS:=$(addprefix -l, $(LIBS)) -L main/src/runtime
CFLAGS:=-Wall -Wextra -std=c11 -pedantic
CXXFLAGS:=-Wall -Wextra -std=c++20 -pedantic

debug: CXXFLAGS += -O0 -DDEBUG -g3
debug: LDFLAGS += -g
debug: CCFLAGS += -O0 -DDEBUG -g3
debug: $(BUILD_DIR)/$(TARGET_EXEC)

release: CXXFLAGS += -DNDEBUG
# release: LDFLAGS += -g
release: CCFLAGS += -DNDEBUG
release: $(BUILD_DIR)/$(TARGET_EXEC)

asan: CXXFLAGS += -fsanitize=address
asan: CCFLAGS += -fsanitize=address
asan: LDFLAGS += -fsanitize=address
asan: debug

ubsan: CXXFLAGS += -fsanitize=undefined
ubsan: CCFLAGS += -fsanitize=undefined
ubsan: LDFLAGS += -fsanitize=undefined
ubsan: debug

tsan: CXXFLAGS += -fsanitize=thread
tsan: CCFLAGS += -fsanitize=thread
tsan: LDFLAGS += -fsanitize=thread
tsan: debug

clangd: clean
	bear -- make

$(BUILD_DIR)/$(TARGET_EXEC): main/src/runtime $(OBJS)
	$(CXX) $(OBJS) -o $@ $(LDFLAGS)

$(BUILD_DIR)/%.cpp.o: %.cpp
	mkdir -p $(dir $@)
	$(CXX) $(CPP_FLAGS) $(CXXFLAGS) -c $< -o $@

clean:
	-rm -r $(BUILD_DIR)
-include $(DEPS)

.PHONY: clean
