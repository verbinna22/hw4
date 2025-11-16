/* Lama SM Bytecode interpreter */

#include <climits>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <new>
#include <stdexcept>
#include <stdint.h>
#include <unordered_set>
#include <vector>

extern "C" {
#define _Noreturn [[noreturn]]
#include "runtime/gc.h"
#include "runtime/runtime.h"
#include "runtime/runtime_common.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void *Bstring (aint *args /*void *p*/);
extern void *Bsexp (aint *args, aint bn);
extern void *Bsta (void *x, aint i, void *v);
extern void *Belem (void *p, aint i);
extern void *Bclosure (aint *args, aint bn);
extern aint  Btag (void *d, aint t, aint n);
extern aint  Barray_patt (void *d, aint n);
extern void  Bmatch_failure (void *v, char *fname, aint line, aint col);
extern aint  Bboxed_patt (void *x);
extern aint  Bunboxed_patt (void *x);
extern aint  Bstring_patt (void *x, void *y);
extern aint  Bstring_tag_patt (void *x);
extern aint  Barray_tag_patt (void *x);
extern aint  Bsexp_tag_patt (void *x);
extern aint  Bclosure_tag_patt (void *x);
extern aint  Lread ();
extern aint  Lwrite (aint n);
extern aint  Llength (void *p);
extern void *Lstring (aint *args /* void *p */);
extern void *Barray (aint *args, aint bn);
extern aint  LtagHash (char *s);
void         dump_heap ();

extern size_t __gc_stack_top, __gc_stack_bottom;
}

/* The unpacked representation of bytecode file */
typedef struct {
  const char     *string_ptr; /* A pointer to the beginning of the string table */
  const uint32_t *public_ptr; /* A pointer to the beginning of publics table    */
  const char     *code_ptr; /* A pointer to the bytecode itself               */
  const uint32_t *global_ptr; /* A pointer to the global area                   */
  uint32_t        stringtab_size; /* The size (in bytes) of the string table        */
  uint32_t        global_area_size; /* The size (in words) of global area             */
  uint32_t        public_symbols_number; /* The number of public symbols                   */
  const char      buffer[0];
} bytefile;

static size_t          bytefile_size;
static const bytefile *file;
static size_t code_size;
static const char     *file_name;

/* Gets a string from a string table by an index */
static inline const char *get_string (const bytefile *f, uint32_t pos) {
  if (pos >= f->stringtab_size) [[unlikely]] { throw std::logic_error("incorrect string offset"); }
  const char *string = &f->string_ptr[pos];
  return string;
}

/* Gets a name for a public symbol */
static inline const char *get_public_name (const bytefile *f, uint32_t i) {
  return get_string(f, f->public_ptr[i * 2]);
}

/* Gets an offset for a publie symbol */
static inline uint32_t get_public_offset (const bytefile *f, uint32_t i) {
  return f->public_ptr[i * 2 + 1];
}

static inline void errno_failure () { failure("%s\n", strerror(errno)); }

/* Reads a binary bytecode file by name and unpacks it */
static const bytefile *read_file (const char *fname) {
  FILE     *f = fopen(fname, "rb");
  long      size;
  bytefile *file;

  if (f == 0) { errno_failure(); }

  if (fseek(f, 0, SEEK_END) == -1) { errno_failure(); }

  bytefile_size = sizeof(void *) * 4 + (size = ftell(f));
  file          = (bytefile *)malloc(bytefile_size);

  if (file == 0) { failure("*** FAILURE: unable to allocate memory.\n"); }

  rewind(f);

  if (size != fread(&file->stringtab_size, 1, size, f)) { errno_failure(); }

  fclose(f);

  constexpr size_t SIZE_OF_PUBLIC_SYMBOL = 2 * sizeof(uint32_t);
  size_t           raw_size              = size - 3 * sizeof(uint32_t);
  // buffer: 3 * uint32_t | public symbols | string table | code
  if (file->public_symbols_number * SIZE_OF_PUBLIC_SYMBOL >= raw_size) {
    throw std::logic_error("public_symbols_number field is corrupted");
  }
  if (file->public_symbols_number * SIZE_OF_PUBLIC_SYMBOL + file->stringtab_size >= raw_size) {
    throw std::logic_error("stringtab_size field is corrupted");
  }
  file->string_ptr = &file->buffer[file->public_symbols_number * SIZE_OF_PUBLIC_SYMBOL];
  file->public_ptr = (uint32_t *)file->buffer;
  file->code_ptr   = &file->string_ptr[file->stringtab_size];
  file->global_ptr = nullptr;
  code_size = raw_size - (file->code_ptr - file->buffer);

  if (file->stringtab_size > 0 && file->string_ptr[file->stringtab_size - 1] != 0) {
    throw std::logic_error("stringtab is corrupted");
  }

  return file;
}

#define STRING get_string(file, INT)
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)

enum class HightSymbols {
  END   = 15,
  BINOP = 0,
  FIRST_GROUP,
  LD = 2,
  LDA,
  ST,
  SECOND_GROUP,
  PATT = 6,
  CALL_SPECIAL,
};

enum class FirstGroup {
  CONST,
  STR,
  SEXP,
  STI,
  STA,
  JMP,
  END,
  RET,
  DROP,
  DUP,
  SWAP,
  ELEM,
};

enum class SecondGroup {
  CJMPZ,
  CJMPNZ,
  BEGIN,
  CBEGIN,
  CLOSURE,
  CALLC,
  CALL,
  TAG,
  ARRAY,
  FAIL_COMMAND,
  LINE,
};

enum class Patterns {
  STRCMP,
  STR,
  ARRAY,
  SEXP,
  BOXED,
  UNBOXED,
  CLOSURE,
};

enum class Locs {
  GLOB = 0,
  LOC,
  ARG,
  CLOS,
};

enum class SpecialCalls {
  LREAD,
  LWRITE,
  LLENGTH,
  LSTRING,
  BARRAY,
};

enum class Binops {
  PLUS = 1,
  MINUS,
  MUL,
  DIV,
  MOD,
  LESS,
  LEQ,
  GT,
  GEQ,
  EQ,
  NEQ,
  AND,
  OR,
};

#  define INT (ip += sizeof(uint32_t), *(uint32_t *)(ip - sizeof(uint32_t)))
#  define BYTE *ip++

#ifndef NDEBUG   // for debug only
static void print_code (const char *ip, FILE *f = stderr) {
  const char *ops[]  = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  const char *pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
  const char *lds[]  = {"LD", "LDA", "ST"};

  char x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;

  fprintf(f, "0x%.8x:\t", ip - file->code_ptr - 1);

  switch (static_cast<HightSymbols>(h)) {
    case HightSymbols::END: fprintf(f, "<end>"); break;

    /* BINOP */
    case HightSymbols::BINOP: fprintf(f, "BINOP\t%s", ops[l - 1]); break;

    case HightSymbols::FIRST_GROUP:
      switch (static_cast<FirstGroup>(l)) {
        case FirstGroup::CONST: fprintf(f, "CONST\t%d", INT); break;

        case FirstGroup::STR: fprintf(f, "STRING\t%s", STRING); break;

        case FirstGroup::SEXP:
          fprintf(f, "SEXP\t%s ", STRING);
          fprintf(f, "%d", INT);
          break;

        case FirstGroup::STI: fprintf(f, "STI"); break;

        case FirstGroup::STA: fprintf(f, "STA"); break;

        case FirstGroup::JMP: fprintf(f, "JMP\t0x%.8x", INT); break;

        case FirstGroup::END: fprintf(f, "END"); break;

        case FirstGroup::RET: fprintf(f, "RET"); break;

        case FirstGroup::DROP: fprintf(f, "DROP"); break;

        case FirstGroup::DUP: fprintf(f, "DUP"); break;

        case FirstGroup::SWAP: fprintf(f, "SWAP"); break;

        case FirstGroup::ELEM: fprintf(f, "ELEM"); break;

        default: FAIL;
      }
      break;

    case HightSymbols::LD:
    case HightSymbols::LDA:
    case HightSymbols::ST:
      fprintf(f, "%s\t", lds[h - 2]);
      switch (static_cast<Locs>(l)) {
        case Locs::GLOB: fprintf(f, "G(%d)", INT); break;
        case Locs::LOC: fprintf(f, "L(%d)", INT); break;
        case Locs::ARG: fprintf(f, "A(%d)", INT); break;
        case Locs::CLOS: fprintf(f, "C(%d)", INT); break;
        default: FAIL;
      }
      break;

    case HightSymbols::SECOND_GROUP:
      switch (static_cast<SecondGroup>(l)) {
        case SecondGroup::CJMPZ: fprintf(f, "CJMPz\t0x%.8x", INT); break;

        case SecondGroup::CJMPNZ: fprintf(f, "CJMPnz\t0x%.8x", INT); break;

        case SecondGroup::BEGIN:
          fprintf(f, "BEGIN\t%d ", INT);
          fprintf(f, "%d", INT);
          break;

        case SecondGroup::CBEGIN:
          fprintf(f, "CBEGIN\t%d ", INT);
          fprintf(f, "%d", INT);
          break;

        case SecondGroup::CLOSURE:
          fprintf(f, "CLOSURE\t0x%.8x", INT);
          {
            uint32_t n = INT;
            for (int i = 0; i < n; i++) {
              switch (static_cast<Locs>(BYTE)) {
                case Locs::GLOB: fprintf(f, "G(%d)", INT); break;
                case Locs::LOC: fprintf(f, "L(%d)", INT); break;
                case Locs::ARG: fprintf(f, "A(%d)", INT); break;
                case Locs::CLOS: fprintf(f, "C(%d)", INT); break;
                default: FAIL;
              }
            }
          };
          break;

        case SecondGroup::CALLC: fprintf(f, "CALLC\t%d", INT); break;

        case SecondGroup::CALL:
          fprintf(f, "CALL\t0x%.8x ", INT);
          fprintf(f, "%d", INT);
          break;

        case SecondGroup::TAG:
          fprintf(f, "TAG\t%s ", STRING);
          fprintf(f, "%d", INT);
          break;

        case SecondGroup::ARRAY: fprintf(f, "ARRAY\t%d", INT); break;

        case SecondGroup::FAIL_COMMAND:
          fprintf(f, "FAIL\t%d", INT);
          fprintf(f, "%d", INT);
          break;

        case SecondGroup::LINE: fprintf(f, "LINE\t%d", INT); break;

        default: FAIL;
      }
      break;

    case HightSymbols::PATT: fprintf(f, "PATT\t%s", pats[l]); break;

    case HightSymbols::CALL_SPECIAL: {
      switch (static_cast<SpecialCalls>(l)) {
        case SpecialCalls::LREAD: fprintf(f, "CALL\tLread"); break;

        case SpecialCalls::LWRITE: fprintf(f, "CALL\tLwrite"); break;

        case SpecialCalls::LLENGTH: fprintf(f, "CALL\tLlength"); break;

        case SpecialCalls::LSTRING: fprintf(f, "CALL\tLstring"); break;

        case SpecialCalls::BARRAY: fprintf(f, "CALL\tBarray\t%d", INT); break;

        default: FAIL;
      }
    } break;

    default: FAIL;
  }

  fprintf(f, "\n");
}

#endif

constexpr size_t OPERAND_STACK_SIZE_U = 1024 * 1024;
constexpr size_t CALL_STACK_SIZE_U    = 1024 * 1024;

// __gc_stack_top ( operands || current_closure_register || globals
// || args | RA | prev_nargs | prev_nlocals | prev_closure | locals ) __gc_stack_bottom
static aint memory_to_simulation[1 + OPERAND_STACK_SIZE_U + CALL_STACK_SIZE_U];

constexpr aint *OPERAND_STACK_BEGIN_INCL = memory_to_simulation + OPERAND_STACK_SIZE_U - 1;
constexpr aint *OPERAND_STACK_END_INCL   = memory_to_simulation;
constexpr aint *CLOSURE_ADDRESS          = memory_to_simulation + OPERAND_STACK_SIZE_U;
constexpr aint *GLOBALS_BEGIN            = memory_to_simulation + OPERAND_STACK_SIZE_U + 1;
#define GLOBALS_END CALL_STACK_BEGIN
static aint *CALL_STACK_BEGIN = memory_to_simulation + OPERAND_STACK_SIZE_U + 1;
#define sp __gc_stack_bottom
#define operand_stack_end __gc_stack_top
constexpr aint *CALL_STACK_END =
    &memory_to_simulation[1 + OPERAND_STACK_SIZE_U + CALL_STACK_SIZE_U];

static size_t main_addr;

static size_t    nargs_in_current_function   = 2;
static size_t    nlocals_in_current_function = 0;
static size_t    nglobals;
constexpr size_t NUTIL_VALUES = 4;

static inline void move_globals (size_t number_of_globals) {
  if (CALL_STACK_BEGIN + number_of_globals > CALL_STACK_END) [[unlikely]] {
    throw std::logic_error("too much globals");
  }
  nglobals = number_of_globals;
  CALL_STACK_BEGIN += nglobals;
  sp += nglobals * sizeof(aint);
}

static inline aint *get_global (size_t i) {
  // if (i >= nglobals) [[unlikely]] { throw std::logic_error("invalid index of global"); }
  return (GLOBALS_BEGIN + i);   // file->global_ptr + i;
}

static inline aint pop_operand () {
  // if (reinterpret_cast<aint *>(operand_stack_end) == OPERAND_STACK_BEGIN_INCL) [[unlikely]] {
  //   throw std::logic_error("op stack underflow");
  // }
  operand_stack_end += sizeof(aint);
  aint result = *reinterpret_cast<aint *>(operand_stack_end);
  return result;
}

static inline void pop_noperands(size_t n) {
  operand_stack_end += (n * sizeof(aint));
}

static inline void check_has_operands_on_stack (size_t n) {
  if (OPERAND_STACK_BEGIN_INCL - reinterpret_cast<aint *>(operand_stack_end) < n) [[unlikely]] {
    throw std::logic_error("op stack underflow");
  }
}

static inline void stack_reorder(size_t n) {
  aint *end = reinterpret_cast<aint *>(operand_stack_end) + 1;
  aint *begin = reinterpret_cast<aint *>(operand_stack_end) + n;
  while (begin > end) {
    std::swap(*begin, *end);
    --begin;
    ++end;
  }
}

static inline void push_operand (aint operand) {
  // if (reinterpret_cast<aint *>(operand_stack_end) < OPERAND_STACK_END_INCL) [[unlikely]] {
  //   throw std::logic_error("op stack overflow");
  // }
  *reinterpret_cast<aint *>(operand_stack_end) = operand;
  operand_stack_end -= sizeof(aint);
}

static inline void check_stack_overflow(size_t stack_size) {
  if ((reinterpret_cast<aint *>(operand_stack_end) + 1 - stack_size) < OPERAND_STACK_END_INCL) [[unlikely]] {
    throw std::logic_error("op stack overflow");
  }
}

static inline void main_begin () {
  // must be successful: nargs in main = 2
  sp += (nargs_in_current_function + NUTIL_VALUES) * sizeof(aint);
}

static inline void call_begin (size_t nargs, const char *next) {
  if (reinterpret_cast<aint *>(sp) + nargs + NUTIL_VALUES >= CALL_STACK_END) [[unlikely]] {
    throw std::logic_error("call stack overflow");
  }
  for (int i = 0; i < nargs; ++i) { reinterpret_cast<aint *>(sp)[i] = pop_operand(); }
  reinterpret_cast<aint *>(sp)[nargs]     = reinterpret_cast<aint>(next);
  reinterpret_cast<aint *>(sp)[nargs + 1] = nargs_in_current_function;
  reinterpret_cast<aint *>(sp)[nargs + 2] = nlocals_in_current_function;
  reinterpret_cast<aint *>(sp)[nargs + 3] = *CLOSURE_ADDRESS;
  *CLOSURE_ADDRESS                            = 0;
  sp += (nargs + NUTIL_VALUES) * sizeof(aint);
  nargs_in_current_function = nargs;
}

static inline void alloc_locals (size_t nlocals) {
  sp += nlocals * sizeof(aint);
  if (reinterpret_cast<aint *>(sp) >= CALL_STACK_END) [[unlikely]] {
    throw std::logic_error("call stack overflow");
  }
  nlocals_in_current_function = nlocals;
}

static inline aint *get_local (size_t i) {
  // if (i >= nlocals_in_current_function) [[unlikely]] {
  //   throw std::logic_error("invalid index of local");
  // }
  return reinterpret_cast<aint *>(sp - (i + 1) * sizeof(aint));
}

#ifndef NDEBUG   // for debug only
static void print_stacks () {
  fprintf(stderr, "\n\nstack:");
  for (aint *i = reinterpret_cast<aint *>(operand_stack_end) + 1;
       i <= OPERAND_STACK_BEGIN_INCL;
       ++i) {
    fprintf(stderr, " %li ", *i);
  }
  fprintf(stderr, "\n\nglobals:");
  for (aint *i = GLOBALS_BEGIN; i < GLOBALS_END; ++i) { fprintf(stderr, " %li ", *i); }
  fprintf(stderr, "\n\nclosure:");
  fprintf(stderr, " %li ", *CLOSURE_ADDRESS);
  fprintf(stderr, "\n\ncall stack:");
  for (aint *i = reinterpret_cast<aint *>(sp) - 1; i >= CALL_STACK_BEGIN; --i) {
    fprintf(stderr, " %li (%lx) ", *i, *i);
  }
  fprintf(stderr, "\n\n");
}
#endif

static inline aint *get_arg (size_t i) {
  // if (i >= nargs_in_current_function) [[unlikely]] {
  //   throw std::logic_error("invalid index of arg");
  // }
  return (reinterpret_cast<aint *>(sp) - nlocals_in_current_function - NUTIL_VALUES - i - 1);
}

static inline aint *get_closure (size_t i) {
  if (*CLOSURE_ADDRESS == 0 || i >= LEN(TO_DATA((*CLOSURE_ADDRESS))) - 1) [[unlikely]] {
    throw std::logic_error("bad access to closure");
  }
  return reinterpret_cast<aint *>(*CLOSURE_ADDRESS)
         + (i + 1);   //  Value.Access i -> I (word_size * (i + 1), r15)
}

static inline const char *call_end () {
  const char *result = reinterpret_cast<char *>(
      *(reinterpret_cast<aint *>(sp) - nlocals_in_current_function - 4));
  size_t nargs   = *(reinterpret_cast<size_t *>(sp) - nlocals_in_current_function - 3);
  size_t nlocals = *(reinterpret_cast<size_t *>(sp) - nlocals_in_current_function - 2);
  *CLOSURE_ADDRESS = *(reinterpret_cast<aint *>(sp) - nlocals_in_current_function - 1);
  sp -= (nlocals_in_current_function + nargs_in_current_function + NUTIL_VALUES) * sizeof(aint);
  nlocals_in_current_function = nlocals;
  nargs_in_current_function   = nargs;
  return result;
}

static inline aint make_boxed (aint n) { return (n << 1) + 1; }

static inline aint make_unboxed (aint n) { return n >> 1; }

static inline void check_unboxed (aint n, const std::string &message) {
  if (!(n & 1)) [[unlikely]] { throw std::logic_error(message); }
}

static inline const char *safe_get_ip (const char *ip, size_t size) {
  if (ip + size - 1 >= (char *)file + bytefile_size || ip < (char *)file) [[unlikely]] {
    throw std::logic_error("bad ip");
  }
  return ip;
}

#define SAFE_INT                                                                                        \
  (ip += sizeof(uint32_t), *(const uint32_t *)safe_get_ip(ip - sizeof(uint32_t), sizeof(uint32_t)))
#define SAFE_BYTE (ip += 1, *safe_get_ip(ip - 1, 1))

#define TRANSFORM_STACK(pop, push, max_use) do { if (current_stack_level < (pop)) throw std::logic_error("may be stack underflow"); max_stack_level_in_func = std::max<uint16_t>(max_stack_level_in_func, current_stack_level + (max_use)); current_stack_level = current_stack_level - (pop) + (push); } while (0)

static void verify () {
  std::vector<size_t> addresses_to_process = { main_addr };
  std::unordered_set<size_t> processed_addressed;
  std::vector<uint16_t> stack_levels_before(code_size, -1);
  nglobals = file->global_area_size;
  while (!addresses_to_process.empty()) {
    size_t begin_addr = addresses_to_process.back();
    addresses_to_process.pop_back();
    processed_addressed.insert(begin_addr);
    const char *ip             = begin_addr + file->code_ptr;
    bool expected_begin = true;
    bool end_found = false;
    std::unordered_set<size_t> front_jump_addrs;
    uint16_t max_stack_level_in_func = 0;
    uint16_t current_stack_level = 0;
    bool was_fail = false;
    do {
      //print_code(ip); ////
      size_t current_addr = ip - file->code_ptr;
      //fprintf(stderr, "-->%d -- %d\n", current_stack_level, stack_levels_before[current_addr]);///
    char x = SAFE_BYTE, h = uint8_t(x & 0xF0) >> 4, l = x & 0x0F;
    //dump_heap();
    // print_stacks();
    if (expected_begin
        && (static_cast<HightSymbols>(h) != HightSymbols::SECOND_GROUP
            || (static_cast<SecondGroup>(l) != SecondGroup::BEGIN
                   && static_cast<SecondGroup>(l) != SecondGroup::CBEGIN))) {
      throw std::logic_error("BEGIN or CBEGIN was expected");
    }
    if (stack_levels_before[current_addr] != uint16_t(-1)) {
      if (stack_levels_before[current_addr] != current_stack_level) {
        throw std::logic_error("invalid stack level merge");
      }
      front_jump_addrs.erase(current_addr);
    }
    stack_levels_before[current_addr] = current_stack_level;
    switch (static_cast<HightSymbols>(h)) {
      /* BINOP  must be valid*/
      case HightSymbols::END: throw std::logic_error("end of bytecode was reached");
      case HightSymbols::BINOP: {
        TRANSFORM_STACK(2, 1, 0);
        switch (static_cast<Binops>(l)) {
          case Binops::PLUS: break;
          case Binops::MINUS: break;
          case Binops::MUL: break;
          case Binops::DIV:
            break;
          case Binops::MOD:
            break;
          case Binops::LESS: break;
          case Binops::LEQ: break;
          case Binops::GT: break;
          case Binops::GEQ: break;
          case Binops::EQ: break;
          case Binops::NEQ: break;
          case Binops::AND: break;
          case Binops::OR: break;
          default: FAIL;
        }
        break;
      }

      case HightSymbols::FIRST_GROUP:
        switch (static_cast<FirstGroup>(l)) {
          case FirstGroup::CONST: {
            aint n = SAFE_INT;
            TRANSFORM_STACK(0, 1, 1);
            break;
          }

          case FirstGroup::STR: {
            aint ptr = reinterpret_cast<aint>(STRING);
            TRANSFORM_STACK(0, 1, 1);
            break;
          }

          case FirstGroup::SEXP: {
            aint          ptr = reinterpret_cast<aint>(STRING);
            aint          n   = SAFE_INT;
            TRANSFORM_STACK(n, 1, 1);
            break;
          }

          case FirstGroup::STA: {
            TRANSFORM_STACK(3, 1, 0);
            break;
          }

          case FirstGroup::STI: throw std::logic_error("STI is temporary prohibited");

          case FirstGroup::JMP: {
            size_t addr = SAFE_INT;
            if (addr < current_addr) {
              if (addr < begin_addr) {
                throw std::logic_error("jump outside function");
              }
              if (stack_levels_before[addr] != current_stack_level) {
                throw std::logic_error("invalid stack level merge");
              }
            } else {
              if (was_fail) {
                was_fail = false;
                current_stack_level = stack_levels_before[addr];
                if (stack_levels_before[addr] == uint16_t(-1)) {
                  throw std::logic_error("must be not fail jump");
                }
              } else {
                if (stack_levels_before[addr] != uint16_t(-1) &&
                    stack_levels_before[addr] != current_stack_level) {
                      throw std::logic_error("invalid stack merge 1");
                }
                stack_levels_before[addr] = current_stack_level;
                front_jump_addrs.insert(addr);
              }
            }
            size_t next_instr_addr = current_addr + 1 + 4;
            if (next_instr_addr >= stack_levels_before.size()) {
              throw std::logic_error("must be next instr after JMP");
            }
            // fprintf(stderr, "|||%d\n", stack_levels_before[next_instr_addr]); ///
            if (stack_levels_before[next_instr_addr] != uint16_t(-1)) {
              current_stack_level = stack_levels_before[next_instr_addr];
            }
            break;
          }

          case FirstGroup::END:
            if (current_stack_level != 1) {
              //fprintf(stderr, "++%d\n", current_stack_level);///
              throw std::logic_error("invalid stack level in END");
            }
            end_found = true;
            break;

          case FirstGroup::RET:
            if (current_stack_level != 1) {
              throw std::logic_error("invalid stack level in RET");
            }
            break;

          case FirstGroup::DROP:
            TRANSFORM_STACK(1, 0, 0);
            break;

          case FirstGroup::DUP: {
            TRANSFORM_STACK(1, 2, 1);
            break;
          }

          case FirstGroup::SWAP: {
            TRANSFORM_STACK(2, 2, 0);
            break;
          }

          case FirstGroup::ELEM: {
            TRANSFORM_STACK(2, 1, 0);
            break;
          }

          default: FAIL;
        }
        break;

      case HightSymbols::LD: {
        size_t i = SAFE_INT;
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB:
            if (i >= nglobals) {
              throw std::logic_error("bad access to global");
            }
            break;
          case Locs::LOC:
            if (i >= nlocals_in_current_function) {
              throw std::logic_error("bad access to local");
            }
            break;
          case Locs::ARG:
            if (i >= nargs_in_current_function) {
                throw std::logic_error("bad access to local");
            }
            break;
          case Locs::CLOS: break;
          default: throw std::logic_error("invalid loc");
        }
        TRANSFORM_STACK(0, 1, 1);
        break;
      }
      case HightSymbols::LDA: throw std::logic_error("LDA is temporary prohibited");
      case HightSymbols::ST: {
        size_t i     = SAFE_INT;
        TRANSFORM_STACK(1, 1, 0);
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB: {
            if (i >= nglobals) {
              throw std::logic_error("bad access to global");
            }
            break;
          }
          case Locs::LOC: {
            if (i >= nlocals_in_current_function) {
              throw std::logic_error("bad access to local");
            }
            break;
          }
          case Locs::ARG: {
            if (i >= nargs_in_current_function) {
                throw std::logic_error("bad access to local");
            }
            break;
          }
          case Locs::CLOS: {
            break;
          }
          default: throw std::logic_error("invalid loc");
        }
        break;
      }

      case HightSymbols::SECOND_GROUP:
        switch (static_cast<SecondGroup>(l)) {
          case SecondGroup::CJMPZ: {
            size_t addr  = SAFE_INT;
            TRANSFORM_STACK(1, 0, 0);
            if (addr < current_addr) {
              if (addr < begin_addr) {
                throw std::logic_error("jump outside function");
              }
              if (stack_levels_before[addr] != current_stack_level) {
                throw std::logic_error("invalid stack level merge");
              }
            } else {
              if (stack_levels_before[addr] != uint16_t(-1) &&
                  stack_levels_before[addr] != current_stack_level) {
                    throw std::logic_error("invalid stack merge 2");
              }
              stack_levels_before[addr] = current_stack_level;
              front_jump_addrs.insert(addr);
            }
            break;
          }

          case SecondGroup::CJMPNZ: {
            size_t addr  = SAFE_INT;
            TRANSFORM_STACK(1, 0, 0);
            if (addr < current_addr) {
              if (addr < begin_addr) {
                throw std::logic_error("jump outside function");
              }
              if (stack_levels_before[addr] != current_stack_level) {
                throw std::logic_error("invalid stack level merge");
              }
            } else {
              if (stack_levels_before[addr] != uint16_t(-1) &&
                  stack_levels_before[addr] != current_stack_level) {
                    throw std::logic_error("invalid stack merge 3");
              }
              stack_levels_before[addr] = current_stack_level;
              front_jump_addrs.insert(addr);
            }
            break;
          }

          case SecondGroup::BEGIN: {
            size_t nargs   = SAFE_INT;
            size_t nlocals = SAFE_INT;
            if (!expected_begin) [[unlikely]] { throw std::logic_error("BEGIN was not expected"); }
            expected_begin = false;
            nlocals_in_current_function = nlocals;
            nargs_in_current_function = nargs;
            break;
          }

          case SecondGroup::CBEGIN: {
            size_t nargs   = SAFE_INT;
            size_t nlocals = SAFE_INT;
            if (!expected_begin) [[unlikely]] { throw std::logic_error("CBEGIN was not expected"); }
            expected_begin = false;
            nlocals_in_current_function = nlocals;
            nargs_in_current_function = nargs;
            break;
          }

          case SecondGroup::CLOSURE: {
            size_t          addr = SAFE_INT;
            uint32_t          n    = SAFE_INT;
            if (!processed_addressed.contains(addr)) {
              addresses_to_process.push_back(addr);
            }
            {
              for (int i = 0; i < n; i++) {
                size_t loc = SAFE_BYTE;
                size_t j  = SAFE_INT;
                switch (static_cast<Locs>(loc)) {
                  case Locs::GLOB: {
                    if (j >= nglobals) {
                      throw std::logic_error("bad access to global");
                    }
                    break;
                  }
                  case Locs::LOC: {
                    if (j >= nlocals_in_current_function) {
                      throw std::logic_error("bad access to local");
                    }
                    break;
                  }
                  case Locs::ARG: {
                    if (j >= nargs_in_current_function) {
                      throw std::logic_error("bad access to arg");
                    }
                    break;
                  }
                  case Locs::CLOS: {
                    break;
                  }
                  default: throw std::logic_error("invalid loc");
                }
              }
              TRANSFORM_STACK(0, 1, n + 1);
            };
            break;
          }

          case SecondGroup::CALLC: {
            size_t args_number = SAFE_INT;
            TRANSFORM_STACK(args_number + 1, 1, 0);
            break;
          }

          case SecondGroup::CALL: {
            size_t addr        = SAFE_INT;
            size_t args_number = SAFE_INT;
            if (!processed_addressed.contains(addr)) {
              addresses_to_process.push_back(addr);
            }
            TRANSFORM_STACK(args_number, 1, std::max<size_t>(args_number, 1));
            break;
          }

          case SecondGroup::TAG: {
            aint string_ptr = reinterpret_cast<aint>(STRING);
            aint size       = SAFE_INT;
            TRANSFORM_STACK(1, 1, 0);
            break;
          }

          case SecondGroup::ARRAY: {
            aint size  = SAFE_INT;
            TRANSFORM_STACK(1, 1, 0);
            break;
          }

          case SecondGroup::FAIL_COMMAND: {
            aint line   = SAFE_INT;
            aint column = SAFE_INT;
            TRANSFORM_STACK(1, 1, 0);
            was_fail = true;
            break;
          }

          case SecondGroup::LINE: {
            size_t n = SAFE_INT;
            break;
          }

          default: FAIL;
        }
        break;

      case HightSymbols::PATT: {
        switch (static_cast<Patterns>(l)) {
          case Patterns::STRCMP: {
            TRANSFORM_STACK(2, 1, 0);
            break;
          }
          case Patterns::STR:
            TRANSFORM_STACK(1, 1, 0);
            break;
          case Patterns::ARRAY:
            TRANSFORM_STACK(1, 1, 0);
            break;
          case Patterns::SEXP:
            TRANSFORM_STACK(1, 1, 0);
            break;
          case Patterns::BOXED:
            TRANSFORM_STACK(1, 1, 0);
            break;
          case Patterns::UNBOXED:
            TRANSFORM_STACK(1, 1, 0);
            break;
          case Patterns::CLOSURE:
            TRANSFORM_STACK(1, 1, 0);
            break;
          default: throw std::logic_error("invalid pattern");
        }
        break;
      }

      case HightSymbols::CALL_SPECIAL: {
        switch (static_cast<SpecialCalls>(l))
        {
          case SpecialCalls::LREAD:
            TRANSFORM_STACK(0, 1, 1);
            break;

          case SpecialCalls::LWRITE: {
            TRANSFORM_STACK(1, 1, 0);
            break;
          }

          case SpecialCalls::LLENGTH:
            TRANSFORM_STACK(1, 1, 0);
            break;

          case SpecialCalls::LSTRING: {
            TRANSFORM_STACK(1, 1, 0);
            break;
          }

          case SpecialCalls::BARRAY: {
            aint n = SAFE_INT;
            TRANSFORM_STACK(n, 1, std::max<aint>(1, n));
            break;
          }
          default: FAIL;
        }
      } break;

      default: FAIL;
    }
    } while(!end_found);
    if (!front_jump_addrs.empty()) {
      throw std::logic_error("front jump outside the function detected");
    }
    auto first_param = const_cast<uint32_t *> (reinterpret_cast<const uint32_t *>(&file->code_ptr[begin_addr + 1]));
    *first_param = (*first_param & 0x0000FFFF) | (static_cast<uint32_t>(current_stack_level) << (sizeof(uint16_t) * CHAR_BIT));
  }
}

static void run_interpreter () {
  const char *ip             = main_addr + file->code_ptr;
  __gc_init();
  __gc_stack_bottom = reinterpret_cast<size_t>(CALL_STACK_BEGIN);
  __gc_stack_top    = reinterpret_cast<size_t>(OPERAND_STACK_BEGIN_INCL);
  move_globals(file->global_area_size);
  main_begin();
  nargs_in_current_function = 2;
  do {
    // print_code(ip);
    char x = BYTE, h = uint8_t(x & 0xF0) >> 4, l = x & 0x0F;
    //dump_heap();
    // print_stacks();
    switch (static_cast<HightSymbols>(h)) {
      /* BINOP  must be valid*/
      case HightSymbols::END: throw std::logic_error("end of bytecode was reached");
      case HightSymbols::BINOP: {
        aint result;
        aint first  = make_unboxed(pop_operand());
        aint second = make_unboxed(pop_operand());
        switch (static_cast<Binops>(l)) {
          case Binops::PLUS: result = second + first; break;
          case Binops::MINUS: result = second - first; break;
          case Binops::MUL: result = int64_t(second) * int64_t(first); break;
          case Binops::DIV:
            if (first == 0) { throw std::logic_error("divide by zero"); }
            result = int64_t(second) / int64_t(first);
            break;
          case Binops::MOD:
            if (first == 0) { throw std::logic_error("divide by zero"); }
            result = int64_t(second) % int64_t(first);
            break;
          case Binops::LESS: result = int64_t(second) < int64_t(first); break;
          case Binops::LEQ: result = int64_t(second) <= int64_t(first); break;
          case Binops::GT: result = int64_t(second) > int64_t(first); break;
          case Binops::GEQ: result = int64_t(second) >= int64_t(first); break;
          case Binops::EQ: result = (second == first); break;
          case Binops::NEQ: result = (second != first); break;
          case Binops::AND: result = (second && first); break;
          case Binops::OR: result = (second || first); break;
          default: FAIL;
        }
        push_operand(make_boxed(result));
        break;
      }

      case HightSymbols::FIRST_GROUP:
        switch (static_cast<FirstGroup>(l)) {
          case FirstGroup::CONST: {   // CONST
            aint n = INT;
            push_operand(make_boxed(n));
            break;
          }

          case FirstGroup::STR: {   // STRING
            aint ptr = reinterpret_cast<aint>(STRING);
            aint allocated_ptr =
                reinterpret_cast<aint>(Bstring(reinterpret_cast<aint *>(&ptr)));
            push_operand(allocated_ptr);
            break;
          }

          case FirstGroup::SEXP: {   // SEXP
            aint          ptr = reinterpret_cast<aint>(STRING);
            aint          n   = INT;
            // check_has_operands_on_stack(n);
            push_operand(LtagHash(reinterpret_cast<char *>(ptr)));
            stack_reorder(n + 1);
            aint allocated_value = reinterpret_cast<aint>(
                Bsexp(reinterpret_cast<aint *>(operand_stack_end) + 1, static_cast<aint>(make_boxed(n + 1))));
            pop_noperands(n + 1);
            push_operand(allocated_value);
            break;
          }

          case FirstGroup::STA: {   // STA
            aint v = pop_operand();
            aint i = pop_operand();
            aint y = pop_operand();
            push_operand(reinterpret_cast<aint>(Bsta(
                reinterpret_cast<void *>(y), i, reinterpret_cast<void *>(v))));
            break;
          }

          case FirstGroup::STI: throw std::logic_error("STI is temporary prohibited");

          case FirstGroup::JMP: {   // JMP
            size_t addr = INT;
            ip            = addr + file->code_ptr;
            break;
          }

          case FirstGroup::END:   // END
            ip = call_end();
            break;

          case FirstGroup::RET:   // RET
            ip = call_end();
            break;

          case FirstGroup::DROP:   // DROP
            pop_operand();
            break;

          case FirstGroup::DUP: {   // DUP
            aint value = pop_operand();
            push_operand(value);
            push_operand(value);
            break;
          }

          case FirstGroup::SWAP: {   // SWAP
            aint first  = pop_operand();
            aint second = pop_operand();
            push_operand(first);
            push_operand(second);
            break;
          }

          case FirstGroup::ELEM: {   // ELEM
            aint i = pop_operand();
            aint p = pop_operand();
            push_operand(reinterpret_cast<aint>(
                Belem(reinterpret_cast<void *>(p), i)));
            break;
          }

          default: FAIL;
        }
        break;

      case HightSymbols::LD: {   // LD
        aint variable;
        size_t i = INT;
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB: variable = *get_global(i); break;
          case Locs::LOC: variable = *get_local(i); break;
          case Locs::ARG: variable = *get_arg(i); break;
          case Locs::CLOS: variable = *get_closure(i); break;
          default: throw std::logic_error("invalid loc");
        }
        push_operand(variable);
        break;
      }
      case HightSymbols::LDA: throw std::logic_error("LDA is temporary prohibited");
      case HightSymbols::ST: {   // ST
        size_t i     = INT;
        aint value = pop_operand();
        push_operand(value);
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB: {
            *get_global(i) = value;
            break;
          }
          case Locs::LOC: {
            *get_local(i) = value;
            break;
          }
          case Locs::ARG: {
            *get_arg(i) = value;
            break;
          }
          case Locs::CLOS: {
            *get_closure(i) = value;
            break;
          }
          default: throw std::logic_error("invalid loc");
        }
        break;
      }

      case HightSymbols::SECOND_GROUP:
        switch (static_cast<SecondGroup>(l)) {
          case SecondGroup::CJMPZ: {   // CJMPz
            size_t addr  = INT;
            aint value = make_unboxed(pop_operand());
            if (value == 0) { ip = addr + file->code_ptr; }
            break;
          }

          case SecondGroup::CJMPNZ: {   // CJMPnz
            size_t addr  = INT;
            aint value = make_unboxed(pop_operand());
            if (value != 0) { ip = addr + file->code_ptr; }
            break;
          }

          case SecondGroup::BEGIN: {   // BEGIN
            size_t nargs   = INT;
            size_t nstack_size = (nargs & 0xFFFF0000) >> (sizeof(uint16_t) * CHAR_BIT);
            check_stack_overflow(nstack_size);
            nargs &= 0x0000FFFF;
            size_t nlocals = INT;
            if (nargs != nargs_in_current_function) [[unlikely]] {
              throw std::logic_error("incorrect argument number");
            }
            alloc_locals(nlocals);
            break;
          }

          case SecondGroup::CBEGIN: {   // CBEGIN
            size_t nargs   = INT;
            size_t nlocals = INT;
            size_t nstack_size = (nargs & 0xFFFF0000) >> (sizeof(uint16_t) * CHAR_BIT);
            check_stack_overflow(nstack_size);
            nargs &= 0x0000FFFF;
            if (nargs != nargs_in_current_function) [[unlikely]] {
              throw std::logic_error("incorrect argument number");
            }
            alloc_locals(nlocals);
            break;
          }

          case SecondGroup::CLOSURE: {   // CLOSURE
            size_t          addr = INT;
            uint32_t          n    = INT;
            {
              push_operand(addr);
              for (int i = 0; i < n; i++) {
                switch (static_cast<Locs>(BYTE)) {
                  case Locs::GLOB: {
                    size_t j  = INT;
                    push_operand(*get_global(j));
                    break;
                  }
                  case Locs::LOC: {
                    size_t j  = INT;
                    push_operand(*get_local(j));
                    break;
                  }
                  case Locs::ARG: {
                    size_t j  = INT;
                    push_operand(*get_arg(j));
                    break;
                  }
                  case Locs::CLOS: {
                    size_t j  = INT;
                    push_operand(*get_closure(j));
                    break;
                  }
                  default: throw std::logic_error("invalid loc");
                }
              }
            };
            stack_reorder(n + 1);
            aint value = reinterpret_cast<aint>(Bclosure(reinterpret_cast<aint *>(operand_stack_end) + 1, make_boxed(n)));
            pop_noperands(n + 1);
            push_operand(value);
            break;
          }

          case SecondGroup::CALLC: {   // CALLC
            size_t args_number = INT;
            call_begin(args_number, ip);
            *CLOSURE_ADDRESS = pop_operand();
            if (!Bclosure_tag_patt(reinterpret_cast<void *>(*CLOSURE_ADDRESS))) [[unlikely]] {
              throw std::logic_error("closure expected");
            }
            ip = *reinterpret_cast<size_t *>(*CLOSURE_ADDRESS) + file->code_ptr;
            break;
          }

          case SecondGroup::CALL: {   // CALL
            size_t addr        = INT;
            size_t args_number = INT;
            call_begin(args_number, ip);
            ip = addr + file->code_ptr;
            break;
          }

          case SecondGroup::TAG: {   // TAG
            aint string_ptr = reinterpret_cast<aint>(STRING);
            aint size       = INT;
            aint data       = pop_operand();
            aint value      = Btag(reinterpret_cast<char *>(data),
                                  LtagHash(reinterpret_cast<char *>(string_ptr)),
                                  make_boxed(size));
            push_operand(value);
            break;
          }

          case SecondGroup::ARRAY: {   // ARRAY
            aint size  = INT;
            aint data  = pop_operand();
            aint value = Barray_patt(reinterpret_cast<void *>(data), make_boxed(size));
            push_operand(value);
            break;
          }

          case SecondGroup::FAIL_COMMAND: {   // FAIL
            aint line   = INT;
            aint column = INT;
            aint data   = pop_operand();
            push_operand(data);
            Bmatch_failure(
                reinterpret_cast<void *>(data), const_cast<char *>(file_name), line, column);
            break;
          }

          case SecondGroup::LINE: {   // LINE
            size_t n = INT;
            break;
          }

          default: FAIL;
        }
        break;

      case HightSymbols::PATT: {   // PATT
        switch (static_cast<Patterns>(l)) {
          case Patterns::STRCMP: {   // strcmp
            void *first  = reinterpret_cast<void *>(pop_operand());
            void *second = reinterpret_cast<void *>(pop_operand());
            push_operand(Bstring_patt(first, second));
            break;
          }
          case Patterns::STR:   // string
            push_operand(Bstring_tag_patt(reinterpret_cast<void *>(pop_operand())));
            break;
          case Patterns::ARRAY:   // array
            push_operand(Barray_tag_patt(reinterpret_cast<void *>(pop_operand())));
            break;
          case Patterns::SEXP:   // sexp
            push_operand(Bsexp_tag_patt(reinterpret_cast<void *>(pop_operand())));
            break;
          case Patterns::BOXED:   // ref = boxed
            push_operand(Bboxed_patt(reinterpret_cast<void *>(pop_operand())));
            break;
          case Patterns::UNBOXED:   // val = unboxed
            push_operand(Bunboxed_patt(reinterpret_cast<void *>(pop_operand())));
            break;
          case Patterns::CLOSURE:   // fun
            push_operand(Bclosure_tag_patt(reinterpret_cast<void *>(pop_operand())));
            break;
          default: throw std::logic_error("invalid pattern");
        }
        break;
      }

      case HightSymbols::CALL_SPECIAL: {
        switch (static_cast<SpecialCalls>(l))   // Lread
        {
          case SpecialCalls::LREAD:
            fprintf(stdout, " ");
            push_operand(Lread());
            break;

          case SpecialCalls::LWRITE: {   // Lwrite
            aint value = pop_operand();
            check_unboxed(value, "Lwrite accept only numbers");
            Lwrite(value);
            push_operand(0);
            break;
          }

          case SpecialCalls::LLENGTH:   // Llength
            push_operand(Llength(reinterpret_cast<void *>(pop_operand())));
            break;

          case SpecialCalls::LSTRING: {   // Lstring
            aint value = pop_operand();
            push_operand(reinterpret_cast<aint>(Lstring(reinterpret_cast<aint *>(&value))));
            break;
          }

          case SpecialCalls::BARRAY: {   // Barray
            aint n = INT;
            check_has_operands_on_stack(n);
            stack_reorder(n);
            aint value = reinterpret_cast<aint>(Barray(reinterpret_cast<aint *>(operand_stack_end) + 1, make_boxed(n)));
            pop_noperands(n);
            push_operand(value);
            break;
          }
          default: FAIL;
        }
      } break;

      default: FAIL;
    }
  } while (ip != nullptr);
  __shutdown();
}

static void find_main () {
  bool found = false;
  for (int i = 0; i < file->public_symbols_number; i++) {
    const char *name   = get_public_name(file, i);
    size_t    offset = get_public_offset(file, i);
    if (std::strcmp(name, "main") == 0) {
      main_addr = offset;
      found     = true;
      break;
    }
  }
  if (!found) [[unlikely]] { throw std::logic_error("file doesn't contain main function"); }
}

int main (int argc, const char *argv[]) {
  if (argc != 2) [[unlikely]] {
    fprintf(stderr, "Error: should be 1 argument *.bc file!\n");
    std::exit(1);
  }
  file_name = argv[1];
  try {
    file = read_file(file_name);
    find_main();
    verify();
  } catch (std::logic_error &e) {
    fprintf(stderr, "Error in bytecode: %s!\n", e.what());
    std::exit(1);
  }
  try {
    run_interpreter();
  } catch (std::logic_error &e) {
    fprintf(stderr, "Error: %s!\n", e.what());
    std::exit(1);
  }
  return 0;
}
