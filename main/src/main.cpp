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

#define INT (ip += sizeof(uint32_t), *((uint32_t *)(ip - sizeof(uint32_t))))
#define BYTE *ip++

static const char *print_code (const char *ip, FILE *f = stderr) {
  const char *ops[]  = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  const char *pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
  const char *lds[]  = {"LD", "LDA", "ST"};

  char x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;

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
  return ip;
}

#undef INT
#undef BYTE

static size_t main_addr;

static inline const char *safe_get_ip (const char *ip, size_t size) {
  if (ip + size - 1 >= (char *)file + bytefile_size || ip < (char *)file) [[unlikely]] {
    throw std::logic_error("bad ip");
  }
  return ip;
}

#define INT                                                                                        \
  (ip += sizeof(uint32_t), *(const uint32_t *)safe_get_ip(ip - sizeof(uint32_t), sizeof(uint32_t)))
#define BYTE (ip += 1, *safe_get_ip(ip - 1, 1))

static std::unordered_set<size_t> find_labels () {
  const char                *ip = file->code_ptr;
  std::unordered_set<size_t> labels;
  labels.insert(main_addr);
  do {
    // print_code(ip); fprintf(stderr, "\n");
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
