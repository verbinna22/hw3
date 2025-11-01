#include <algorithm>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <functional>
#include <iterator>
#include <stdexcept>
#include <stdint.h>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

// TODO: entry point is main
// TODO: generalize code
// TODO: vector bool
// TODO: representation
// TODO: memcmp

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
static const char     *file_name;

[[noreturn]] static void vfailure (const char *s, va_list args) {
  fprintf(stderr, "*** FAILURE: ");
  vfprintf(stderr, s, args);   // vprintf (char *, va_list) <-> printf (char *, ...)
  exit(255);
}

[[noreturn]] void failure (const char *s, ...) {
  va_list args;

  va_start(args, s);
  vfailure(s, args);
  va_end(args);
}

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
  size_t    size;
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

static inline const char *safe_get_ip (const char *ip, size_t size) {
  if (ip + size - 1 >= (char *)file + bytefile_size || ip < (char *)file) [[unlikely]] {
    throw std::logic_error("bad ip");
  }
  return ip;
}

#define INT                                                                                        \
  (ip += sizeof(uint32_t), *(const uint32_t *)safe_get_ip(ip - sizeof(uint32_t), sizeof(uint32_t)))
#define BYTE (ip += 1, *safe_get_ip(ip - 1, 1))

static const char *const ops[] = {
    "+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
static const char *const pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
static const char *const lds[]  = {"LD", "LDA", "ST"};

enum class BytecodeProcessingMode {
  PRINT,
  LABEL_FIND,
};

enum class LabelFindModeFSM {
  CHECK_BEGIN,
  PROCESS,
  FOUND_CALL,
  FOUND_JUMP,
  END,
};

static LabelFindModeFSM label_find_mode_state;
static size_t           address_found;

template <BytecodeProcessingMode mode>
const char *process_bytecode (const char *ip) {
  char x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;
  switch (static_cast<HightSymbols>(h)) {
    case HightSymbols::END:
      if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("<end>"); }
      if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
        throw std::logic_error("unexpected EOF");
      }
      break;

    case HightSymbols::BINOP: {
      switch (static_cast<Binops>(l)) {
        case Binops::PLUS:
        case Binops::MINUS:
        case Binops::MUL:
        case Binops::DIV:
        case Binops::MOD:
        case Binops::LESS:
        case Binops::LEQ:
        case Binops::GT:
        case Binops::GEQ:
        case Binops::EQ:
        case Binops::NEQ:
        case Binops::AND:
        case Binops::OR: break;
        default: FAIL;
      }
      if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("BINOP\t%s", ops[l - 1]); }
      break;
    }

    case HightSymbols::FIRST_GROUP:
      switch (static_cast<FirstGroup>(l)) {
        case FirstGroup::CONST: {
          size_t n = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CONST\t%d", n); }
          break;
        }

        case FirstGroup::STR: {
          const char *str = STRING;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("STRING\t%s", str); }
          break;
        }

        case FirstGroup::SEXP: {
          const char *str = STRING;
          size_t      n   = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) {
            printf("SEXP\t%s ", str);
            printf("%d", n);
          }
          break;
        }

        case FirstGroup::STI: throw std::logic_error("STI is temporary prohibited");

        case FirstGroup::STA:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("STA"); }
          break;

        case FirstGroup::JMP: {
          size_t addr = INT;
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::PROCESS) {
              label_find_mode_state = LabelFindModeFSM::FOUND_JUMP;
              address_found = addr;
            }
          }
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("JMP\t0x%.8x", addr); }
          break;
        }

        case FirstGroup::END:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("END"); }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::PROCESS) {
              label_find_mode_state = LabelFindModeFSM::END;
            }
          }
          break;

        case FirstGroup::RET:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("RET"); }
          break;

        case FirstGroup::DROP:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("DROP"); }
          break;

        case FirstGroup::DUP:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("DUP"); }
          break;

        case FirstGroup::SWAP:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("SWAP"); }
          break;

        case FirstGroup::ELEM:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("ELEM"); }
          break;

        default: FAIL;
      }
      break;

    case HightSymbols::LD: {
      size_t i = INT;
      if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("%s\t", lds[h - 2]); }

      switch (static_cast<Locs>(l)) {
        case Locs::GLOB:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("G(%d)", i); }
          break;
        case Locs::LOC:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("L(%d)", i); }
          break;
        case Locs::ARG:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("A(%d)", i); }
          break;
        case Locs::CLOS:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("C(%d)", i); }
          break;
        default: throw std::logic_error("invalid loc");
      }
      break;
    }
    case HightSymbols::LDA: throw std::logic_error("LDA is temporary prohibited");
    case HightSymbols::ST: {
      size_t i = INT;
      if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("%s\t", lds[h - 2]); }

      switch (static_cast<Locs>(l)) {
        case Locs::GLOB:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("G(%d)", i); }
          break;
        case Locs::LOC:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("L(%d)", i); }
          break;
        case Locs::ARG:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("A(%d)", i); }
          break;
        case Locs::CLOS:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("C(%d)", i); }
          break;
        default: throw std::logic_error("invalid loc");
      }
      break;
    }

    case HightSymbols::SECOND_GROUP:
      switch (static_cast<SecondGroup>(l)) {
        case SecondGroup::CJMPZ: {
          size_t addr = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CJMPz\t0x%.8x", addr); }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::PROCESS) {
              label_find_mode_state = LabelFindModeFSM::FOUND_JUMP;
              address_found = addr;
            }
          }
          break;
        }

        case SecondGroup::CJMPNZ: {
          size_t addr = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CJMPnz\t0x%.8x", addr); }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::PROCESS) {
              label_find_mode_state = LabelFindModeFSM::FOUND_JUMP;
              address_found = addr;
            }
          }
          break;
        }

        case SecondGroup::BEGIN: {
          size_t nargs   = INT;
          size_t nlocals = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) {
            printf("BEGIN\t%d ", nargs);
            printf("%d", nlocals);
          }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::CHECK_BEGIN) {
              label_find_mode_state = LabelFindModeFSM::PROCESS;
            } else {
              throw std::logic_error("BEGIN wasn't expected");
            }
          }
          break;
        }

        case SecondGroup::CBEGIN: {
          size_t nargs   = INT;
          size_t nlocals = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) {
            printf("CBEGIN\t%d ", nargs);
            printf("%d", nlocals);
          }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::CHECK_BEGIN) {
              label_find_mode_state = LabelFindModeFSM::PROCESS;
            } else {
              throw std::logic_error("CBEGIN wasn't expected");
            }
          }
          break;
        }

        case SecondGroup::CLOSURE: {
          size_t   addr = INT;
          uint32_t n    = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CLOSURE\t0x%.8x", addr); }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::PROCESS) {
              label_find_mode_state = LabelFindModeFSM::FOUND_CALL;
              address_found = addr;
            }
          }
          for (int i = 0; i < n; i++) {
            int    loc = BYTE;
            size_t j   = INT;
            switch (static_cast<Locs>(loc)) {
              case Locs::GLOB:
                if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("G(%d)", j); }
                break;
              case Locs::LOC:
                if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("L(%d)", j); }
                break;
              case Locs::ARG:
                if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("A(%d)", j); }
                break;
              case Locs::CLOS:
                if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("C(%d)", j); }
                break;
              default: throw std::logic_error("invalid loc");
            }
          }
        }; break;

        case SecondGroup::CALLC: {
          size_t args_number = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CALLC\t%d", args_number); }
          break;
        }

        case SecondGroup::CALL: {
          size_t addr        = INT;
          size_t args_number = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) {
            printf("CALL\t0x%.8x ", addr);
            printf("%d", args_number);
          }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == LabelFindModeFSM::PROCESS) {
              label_find_mode_state = LabelFindModeFSM::FOUND_CALL;
              address_found = addr;
            }
          }
          break;
        }

        case SecondGroup::TAG: {
          const char *ptr  = STRING;
          size_t      size = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) {
            printf("TAG\t%s ", ptr);
            printf("%d", size);
          }
          break;
        }

        case SecondGroup::ARRAY: {
          size_t size = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("ARRAY\t%d", size); }
          break;
        }

        case SecondGroup::FAIL_COMMAND: {
          size_t line   = INT;
          size_t column = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) {
            printf("FAIL\t%d", line);
            printf("%d", column);
          }
          break;
        }

        case SecondGroup::LINE: {
          size_t n = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("LINE\t%d", n); }
          break;
        }

        default: FAIL;
      }
      break;

    case HightSymbols::PATT: {
      switch (static_cast<Patterns>(l)) {
        case Patterns::STRCMP:   // strcmp
        case Patterns::STR:   // string
        case Patterns::ARRAY:   // array
        case Patterns::SEXP:   // sexp
        case Patterns::BOXED:   // ref = boxed
        case Patterns::UNBOXED:   // val = unboxed
        case Patterns::CLOSURE:   // fun
          break;
        default: throw std::logic_error("invalid pattern");
      }
      if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("PATT\t%s", pats[l]); }
      break;
    }

    case HightSymbols::CALL_SPECIAL: {
      switch (static_cast<SpecialCalls>(l)) {
        case SpecialCalls::LREAD:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CALL\tLread"); }
          break;

        case SpecialCalls::LWRITE:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CALL\tLwrite"); }
          break;

        case SpecialCalls::LLENGTH:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CALL\tLlength"); }
          break;

        case SpecialCalls::LSTRING:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CALL\tLstring"); }
          break;

        case SpecialCalls::BARRAY: {
          size_t size = INT;
          printf("CALL\tBarray\t%d", size);
          break;
        }

        default: FAIL;
      }
    } break;

    default: FAIL;
  }
  if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
    if (label_find_mode_state == LabelFindModeFSM::CHECK_BEGIN) {
      throw std::logic_error("BEGIN or CBEGIN was expected");
    }
  }
  return ip;
}

static const char *print_code (const char *ip, FILE *f = stderr) {   // TODO
  return process_bytecode<BytecodeProcessingMode::PRINT>(ip);
}

static size_t main_addr;

static std::unordered_set<size_t> find_labels (std::unordered_set<size_t> &reachable_faddresses) {
  std::vector<size_t> faddresses_to_process = {main_addr};
  std::unordered_set<size_t> labels;
  while (!faddresses_to_process.empty()) {
    size_t faddress = faddresses_to_process.back();
    faddresses_to_process.pop_back();
    reachable_faddresses.insert(faddress);
    const char *ip = file->code_ptr + faddress;
    label_find_mode_state = LabelFindModeFSM::CHECK_BEGIN;
    do {
      // print_code(ip); fflush(stdout); fprintf(stderr, "\n");
      ip = process_bytecode<BytecodeProcessingMode::LABEL_FIND>(ip);
      switch (label_find_mode_state) {
        case LabelFindModeFSM::FOUND_CALL:
          if (!reachable_faddresses.contains(address_found)) {
            faddresses_to_process.push_back(address_found);
          }
          break;
        case LabelFindModeFSM::FOUND_JUMP:
          labels.insert(address_found);
          break;
        default: break;
      }
    } while (label_find_mode_state != LabelFindModeFSM::END);
  }
  return labels;
}

static std::unordered_set<size_t> find_labels () {
  const char                *ip = file->code_ptr;
  std::unordered_set<size_t> labels;
  labels.insert(main_addr);
  do {
    // print_code(ip); fflush(stdout); fprintf(stderr, "\n");
    char x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;
    switch (static_cast<HightSymbols>(h)) {
      case HightSymbols::END: return labels;
      case HightSymbols::BINOP: {
        switch (static_cast<Binops>(l)) {
          case Binops::PLUS:
          case Binops::MINUS:
          case Binops::MUL:
          case Binops::DIV:
          case Binops::MOD:
          case Binops::LESS:
          case Binops::LEQ:
          case Binops::GT:
          case Binops::GEQ:
          case Binops::EQ:
          case Binops::NEQ:
          case Binops::AND:
          case Binops::OR: break;
          default: FAIL;
        }
        break;
      }

      case HightSymbols::FIRST_GROUP:
        switch (static_cast<FirstGroup>(l)) {
          case FirstGroup::CONST: {   // CONST
            INT;   // n
            break;
          }

          case FirstGroup::STR: {   // STRING
            STRING;   // ptr
            break;
          }

          case FirstGroup::SEXP: {   // SEXP
            STRING;   // ptr
            INT;   // n
            break;
          }

          case FirstGroup::STA: {   // STA
            break;
          }

          case FirstGroup::STI: throw std::logic_error("STI is temporary prohibited");

          case FirstGroup::JMP: {   // JMP
            size_t addr = INT;
            labels.insert(addr);
            break;
          }

          case FirstGroup::END:   // END
            break;

          case FirstGroup::RET:   // RET
            break;

          case FirstGroup::DROP:   // DROP
            break;

          case FirstGroup::DUP: {   // DUP
            break;
          }

          case FirstGroup::SWAP: {   // SWAP
            break;
          }

          case FirstGroup::ELEM: {   // ELEM
            break;
          }

          default: FAIL;
        }
        break;

      case HightSymbols::LD: {   // LD
        size_t i = INT;
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB:
          case Locs::LOC:
          case Locs::ARG:
          case Locs::CLOS: break;
          default: throw std::logic_error("invalid loc");
        }
        break;
      }
      case HightSymbols::LDA: throw std::logic_error("LDA is temporary prohibited");
      case HightSymbols::ST: {   // ST
        size_t i = INT;
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB:
          case Locs::LOC:
          case Locs::ARG:
          case Locs::CLOS: break;
          default: throw std::logic_error("invalid loc");
        }
        break;
      }

      case HightSymbols::SECOND_GROUP:
        switch (static_cast<SecondGroup>(l)) {
          case SecondGroup::CJMPZ: {   // CJMPz
            size_t addr = INT;
            labels.insert(addr);
            break;
          }

          case SecondGroup::CJMPNZ: {   // CJMPnz
            size_t addr = INT;
            labels.insert(addr);
            break;
          }

          case SecondGroup::BEGIN: {   // BEGIN
            size_t nargs   = INT;
            size_t nlocals = INT;
            break;
          }

          case SecondGroup::CBEGIN: {   // CBEGIN
            size_t nargs   = INT;
            size_t nlocals = INT;
            break;
          }

          case SecondGroup::CLOSURE: {   // CLOSURE
            size_t   addr = INT;
            uint32_t n    = INT;
            labels.insert(addr);
            for (int i = 0; i < n; i++) {
              int    loc = BYTE;
              size_t j   = INT;
              switch (static_cast<Locs>(loc)) {
                case Locs::GLOB:
                case Locs::LOC:
                case Locs::ARG:
                case Locs::CLOS: break;
                default: throw std::logic_error("invalid loc");
              }
            }
            break;
          }

          case SecondGroup::CALLC: {   // CALLC
            size_t args_number = INT;
            break;
          }

          case SecondGroup::CALL: {   // CALL
            size_t addr        = INT;
            size_t args_number = INT;
            labels.insert(addr);
            break;
          }

          case SecondGroup::TAG: {   // TAG
            STRING;   // ptr
            INT;   // size
            break;
          }

          case SecondGroup::ARRAY: {   // ARRAY
            INT;   // size
            break;
          }

          case SecondGroup::FAIL_COMMAND: {   // FAIL
            INT;   // line
            INT;   // column
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
          case Patterns::STRCMP:   // strcmp
          case Patterns::STR:   // string
          case Patterns::ARRAY:   // array
          case Patterns::SEXP:   // sexp
          case Patterns::BOXED:   // ref = boxed
          case Patterns::UNBOXED:   // val = unboxed
          case Patterns::CLOSURE:   // fun
            break;
          default: throw std::logic_error("invalid pattern");
        }
        break;
      }

      case HightSymbols::CALL_SPECIAL: {
        switch (static_cast<SpecialCalls>(l))   // Lread
        {
          case SpecialCalls::LREAD:
          case SpecialCalls::LWRITE:   // Lwrite
          case SpecialCalls::LLENGTH:   // Llength
          case SpecialCalls::LSTRING:   // Lstring
            break;
          case SpecialCalls::BARRAY: {   // Barray
            INT;
            break;
          }
          default: FAIL;
        }
      } break;

      default: FAIL;
    }
  } while (true);
}

struct bytecode {
  const char *begin;
  const char *end;

  bytecode (const char *begin, const char *end)
      : begin(begin)
      , end(end) { }

  size_t get_size () const { return std::distance(begin, end); }

  bool operator== (const bytecode &other) const {
    const size_t size = get_size();
    if (size != other.get_size()) { return false; }
    return std::strncmp(begin, other.begin, size) == 0;
  }

  bool operator!= (const bytecode &other) const { return !(*this == other); }
};

template <>
struct std::hash<bytecode> {
  size_t operator() (const bytecode &b) const {
    constexpr size_t k   = 39916801;
    constexpr size_t mod = 1e9 + 7;
    size_t           h   = 0;
    for (const char *ptr = b.begin; ptr != b.end; ++ptr) { h = (h * k + *ptr) % mod; }
    return ~h;
  }
};

static std::unordered_map<bytecode, size_t> count_frequency (std::unordered_set<size_t> &labels) {
  const char                          *ip = file->code_ptr;
  std::unordered_map<bytecode, size_t> bytecode_frequency;
  const char                          *previous_begin = nullptr;
  do {
    // print_code(ip);
    const size_t current_addr  = ip - file->code_ptr;
    const char  *current_begin = ip;
    const char  *current_end   = nullptr;
    char         x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;
    switch (static_cast<HightSymbols>(h)) {
      case HightSymbols::END: return bytecode_frequency;
      case HightSymbols::BINOP: {
        switch (static_cast<Binops>(l)) {
          case Binops::PLUS:
          case Binops::MINUS:
          case Binops::MUL:
          case Binops::DIV:
          case Binops::MOD:
          case Binops::LESS:
          case Binops::LEQ:
          case Binops::GT:
          case Binops::GEQ:
          case Binops::EQ:
          case Binops::NEQ:
          case Binops::AND:
          case Binops::OR: break;
          default: FAIL;
        }
        break;
      }

      case HightSymbols::FIRST_GROUP:
        switch (static_cast<FirstGroup>(l)) {
          case FirstGroup::CONST: {   // CONST
            INT;   // n
            break;
          }

          case FirstGroup::STR: {   // STRING
            STRING;   // ptr
            break;
          }

          case FirstGroup::SEXP: {   // SEXP
            STRING;   // ptr
            INT;   // n
            break;
          }

          case FirstGroup::STA: {   // STA
            break;
          }

          case FirstGroup::STI: throw std::logic_error("STI is temporary prohibited");

          case FirstGroup::JMP: {   // JMP
            size_t addr = INT;
            break;
          }

          case FirstGroup::END:   // END
            break;

          case FirstGroup::RET:   // RET
            break;

          case FirstGroup::DROP:   // DROP
            break;

          case FirstGroup::DUP: {   // DUP
            break;
          }

          case FirstGroup::SWAP: {   // SWAP
            break;
          }

          case FirstGroup::ELEM: {   // ELEM
            break;
          }

          default: FAIL;
        }
        break;

      case HightSymbols::LD: {   // LD
        size_t i = INT;
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB:
          case Locs::LOC:
          case Locs::ARG:
          case Locs::CLOS: break;
          default: throw std::logic_error("invalid loc");
        }
        break;
      }
      case HightSymbols::LDA: throw std::logic_error("LDA is temporary prohibited");
      case HightSymbols::ST: {   // ST
        size_t i = INT;
        switch (static_cast<Locs>(l)) {
          case Locs::GLOB:
          case Locs::LOC:
          case Locs::ARG:
          case Locs::CLOS: break;
          default: throw std::logic_error("invalid loc");
        }
        break;
      }

      case HightSymbols::SECOND_GROUP:
        switch (static_cast<SecondGroup>(l)) {
          case SecondGroup::CJMPZ: {   // CJMPz
            size_t addr = INT;
            break;
          }

          case SecondGroup::CJMPNZ: {   // CJMPnz
            size_t addr = INT;
            break;
          }

          case SecondGroup::BEGIN: {   // BEGIN
            size_t nargs   = INT;
            size_t nlocals = INT;
            break;
          }

          case SecondGroup::CBEGIN: {   // CBEGIN
            size_t nargs   = INT;
            size_t nlocals = INT;
            break;
          }

          case SecondGroup::CLOSURE: {   // CLOSURE
            size_t   addr = INT;
            uint32_t n    = INT;
            for (int i = 0; i < n; i++) {
              int    loc = BYTE;
              size_t j   = INT;
              switch (static_cast<Locs>(loc)) {
                case Locs::GLOB:
                case Locs::LOC:
                case Locs::ARG:
                case Locs::CLOS: break;
                default: throw std::logic_error("invalid loc");
              }
            }
            break;
          }

          case SecondGroup::CALLC: {   // CALLC
            size_t args_number = INT;
            break;
          }

          case SecondGroup::CALL: {   // CALL
            size_t addr        = INT;
            size_t args_number = INT;
            break;
          }

          case SecondGroup::TAG: {   // TAG
            STRING;   // ptr
            INT;   // size
            break;
          }

          case SecondGroup::ARRAY: {   // ARRAY
            INT;   // size
            break;
          }

          case SecondGroup::FAIL_COMMAND: {   // FAIL
            INT;   // line
            INT;   // column
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
          case Patterns::STRCMP:   // strcmp
          case Patterns::STR:   // string
          case Patterns::ARRAY:   // array
          case Patterns::SEXP:   // sexp
          case Patterns::BOXED:   // ref = boxed
          case Patterns::UNBOXED:   // val = unboxed
          case Patterns::CLOSURE:   // fun
            break;
          default: throw std::logic_error("invalid pattern");
        }
        break;
      }

      case HightSymbols::CALL_SPECIAL: {
        switch (static_cast<SpecialCalls>(l))   // Lread
        {
          case SpecialCalls::LREAD:
          case SpecialCalls::LWRITE:   // Lwrite
          case SpecialCalls::LLENGTH:   // Llength
          case SpecialCalls::LSTRING:   // Lstring
            break;
          case SpecialCalls::BARRAY: {   // Barray
            INT;
            break;
          }
          default: FAIL;
        }
      } break;

      default: FAIL;
    }
    current_end = ip;
    ++bytecode_frequency[bytecode(current_begin, current_end)];
    if (!labels.contains(current_addr)) {
      ++bytecode_frequency[bytecode(previous_begin, current_end)];
    }
    previous_begin = current_begin;
  } while (true);
}

static void find_main () {
  bool found = false;
  for (int i = 0; i < file->public_symbols_number; i++) {
    const char *name   = get_public_name(file, i);
    size_t      offset = get_public_offset(file, i);
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
  } catch (std::logic_error &e) {
    fprintf(stderr, "Error in bytecode: %s!\n", e.what());
    std::exit(1);
  }
  try {
    auto                                     labels      = find_labels();
    auto                                     frequencies = count_frequency(labels);
    std::vector<std::pair<bytecode, size_t>> sequences(frequencies.begin(), frequencies.end());
    std::sort(sequences.begin(), sequences.end(), [] (const auto &a, const auto &b) {
      return a.second > b.second;
    });
    for (auto &[bc, frequency]: sequences) {
      const char *end = print_code(bc.begin, stdout);
      if (end != bc.end) {
        std::printf("\t||\t");
        print_code(end, stdout);
      }
      std::printf(": %zu\n", frequency);
    }
  } catch (std::logic_error &e) {
    fprintf(stderr, "Error: %s!\n", e.what());
    std::exit(1);
  }
  return 0;
}
