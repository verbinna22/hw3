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
  CHECK,
  SKIP,
};

enum class ProcessingFSM {
  CHECK_BEGIN,
  PROCESS,
  FOUND_CALL,
  FOUND_JUMP,
  END,
};

static ProcessingFSM label_find_mode_state;
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
            if (label_find_mode_state == ProcessingFSM::PROCESS) {
              label_find_mode_state = ProcessingFSM::FOUND_JUMP;
              address_found = addr;
            }
          }
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("JMP\t0x%.8x", addr); }
          break;
        }

        case FirstGroup::END:
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("END"); }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND || mode == BytecodeProcessingMode::CHECK) {
            if (label_find_mode_state == ProcessingFSM::PROCESS) {
              label_find_mode_state = ProcessingFSM::END;
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
            if (label_find_mode_state == ProcessingFSM::PROCESS) {
              label_find_mode_state = ProcessingFSM::FOUND_JUMP;
              address_found = addr;
            }
          }
          break;
        }

        case SecondGroup::CJMPNZ: {
          size_t addr = INT;
          if constexpr (mode == BytecodeProcessingMode::PRINT) { printf("CJMPnz\t0x%.8x", addr); }
          if constexpr (mode == BytecodeProcessingMode::LABEL_FIND) {
            if (label_find_mode_state == ProcessingFSM::PROCESS) {
              label_find_mode_state = ProcessingFSM::FOUND_JUMP;
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
            if (label_find_mode_state == ProcessingFSM::CHECK_BEGIN) {
              label_find_mode_state = ProcessingFSM::PROCESS;
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
            if (label_find_mode_state == ProcessingFSM::CHECK_BEGIN) {
              label_find_mode_state = ProcessingFSM::PROCESS;
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
            if (label_find_mode_state == ProcessingFSM::PROCESS) {
              label_find_mode_state = ProcessingFSM::FOUND_CALL;
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
            if (label_find_mode_state == ProcessingFSM::PROCESS) {
              label_find_mode_state = ProcessingFSM::FOUND_CALL;
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
    if (label_find_mode_state == ProcessingFSM::CHECK_BEGIN) {
      throw std::logic_error("BEGIN or CBEGIN was expected");
    }
  }
  return ip;
}

static const char *print_code (const char *ip) { 
  return process_bytecode<BytecodeProcessingMode::PRINT>(ip);
}

static size_t main_addr;

static std::vector<bool> find_labels (std::unordered_set<size_t> &reachable_faddresses) {
  std::vector<size_t> faddresses_to_process = {main_addr};
  std::vector<bool> is_jump(bytefile_size - (reinterpret_cast<const char *>(file) - file->code_ptr), false);
  while (!faddresses_to_process.empty()) {
    size_t faddress = faddresses_to_process.back();
    faddresses_to_process.pop_back();
    reachable_faddresses.insert(faddress);
    const char *ip = file->code_ptr + faddress;
    label_find_mode_state = ProcessingFSM::CHECK_BEGIN;
    do {
      // print_code(ip); fflush(stdout); fprintf(stderr, "\n %d\n", label_find_mode_state);
      const size_t current_addr  = ip - file->code_ptr;
      ip = process_bytecode<BytecodeProcessingMode::LABEL_FIND>(ip);
      switch (label_find_mode_state) {
        case ProcessingFSM::FOUND_CALL:
          if (!reachable_faddresses.contains(address_found)) {
            faddresses_to_process.push_back(address_found);
          }
          label_find_mode_state = ProcessingFSM::PROCESS;
          break;
        case ProcessingFSM::FOUND_JUMP:
          is_jump[current_addr] = true;
          label_find_mode_state = ProcessingFSM::PROCESS;
          break;
        default: break;
      }
    } while (label_find_mode_state != ProcessingFSM::END);
  }
  return is_jump;
}

struct bytecode1 {
  uint32_t begin;

  explicit bytecode1 (uint32_t addr)
      : begin(addr) { }

  const char *get_ptr() const {
    return file->code_ptr + begin;
  }

  static size_t get_size(const char *begin) {
    const char *end = process_bytecode<BytecodeProcessingMode::SKIP>(begin);
    return std::distance(begin, end);
  }

  bool operator== (const bytecode1 &other) const {
    const char *this_ptr = get_ptr();
    const char *other_ptr = other.get_ptr();
    const size_t size = get_size(this_ptr);
    if (size != other.get_size(other_ptr)) { return false; }
    return std::memcmp(this_ptr, other_ptr, size) == 0;
  }

  bool operator!= (const bytecode1 &other) const { return !(*this == other); }
};

template <>
struct std::hash<bytecode1> {
  size_t operator() (const bytecode1 &b) const {
    constexpr size_t k   = 39916801;
    constexpr size_t mod = 1e9 + 7;
    size_t           h   = 0;
    const char *ptr = b.get_ptr();
    const char *end = ptr + b.get_size(ptr);
    for (; ptr != end; ++ptr) { h = (h * k + *ptr) % mod; }
    return ~h;
  }
};

struct bytecode2 {
  uint32_t begin;

  explicit bytecode2 (uint32_t addr)
      : begin(addr) { }

  const char *get_ptr() const {
    return file->code_ptr + begin;
  }

  static size_t get_size(const char *begin) {
    const char *end = process_bytecode<BytecodeProcessingMode::SKIP>(begin);
    end = process_bytecode<BytecodeProcessingMode::SKIP>(end);
    return std::distance(begin, end);
  }

  bool operator== (const bytecode2 &other) const {
    const char *this_ptr = get_ptr();
    const char *other_ptr = other.get_ptr();
    const size_t size = get_size(this_ptr);
    if (size != other.get_size(other_ptr)) { return false; }
    return std::memcmp(this_ptr, other_ptr, size) == 0;
  }

  bool operator!= (const bytecode2 &other) const { return !(*this == other); }
};

template <>
struct std::hash<bytecode2> {
  size_t operator() (const bytecode2 &b) const {
    constexpr size_t k   = 39916801;
    constexpr size_t mod = 1e9 + 7;
    size_t           h   = 0;
    const char *ptr = b.get_ptr();
    const char *end = ptr + b.get_size(ptr);
    for (; ptr != end; ++ptr) { h = (h * k + *ptr) % mod; }
    return ~h;
  }
};

static std::pair<std::unordered_map<bytecode1, uint32_t>, std::unordered_map<bytecode2, uint32_t>> count_frequency(const std::vector<bool> &is_jump, const std::unordered_set<size_t> &functions) {
  std::unordered_map<bytecode1, uint32_t> bytecode_frequency_1;
  std::unordered_map<bytecode2, uint32_t> bytecode_frequency_2;
  for (auto faddress: functions) {
    const char *ip = file->code_ptr + faddress;
    int64_t previous_begin = -1;
    label_find_mode_state = ProcessingFSM::PROCESS;
    do {
      // print_code(ip); fflush(stdout); fprintf(stderr, "\n"); ////
      const uint32_t current_addr  = ip - file->code_ptr;
      ip = process_bytecode<BytecodeProcessingMode::CHECK>(ip);
      ++bytecode_frequency_1[bytecode1(current_addr)];
      if (!is_jump[current_addr] && previous_begin != -1) {
        ++bytecode_frequency_2[bytecode2(previous_begin)];
      }
      previous_begin = current_addr;
    } while (label_find_mode_state != ProcessingFSM::END);
  }
  return {bytecode_frequency_1, bytecode_frequency_2};
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
    std::unordered_set<size_t> reachable_functions;
    std::vector<std::pair<bytecode1, size_t>> sequences_1;
    std::vector<std::pair<bytecode2, size_t>> sequences_2;
    {
    auto                                     is_jump      = find_labels(reachable_functions);
    auto                                     [frequencies_1, frequencies_2] = count_frequency(is_jump, reachable_functions);
    sequences_1.reserve(frequencies_1.size());
    sequences_2.reserve(frequencies_2.size());
    std::copy(frequencies_1.begin(), frequencies_1.end(), std::back_inserter(sequences_1));
    std::copy(frequencies_2.begin(), frequencies_2.end(), std::back_inserter(sequences_2));
    }
    std::sort(sequences_1.begin(), sequences_1.end(), [] (const auto &a, const auto &b) {
      return a.second > b.second;
    });
    std::sort(sequences_2.begin(), sequences_2.end(), [] (const auto &a, const auto &b) {
      return a.second > b.second;
    });
    size_t i = 0;
    size_t j = 0;
    while (i < sequences_1.size() && j < sequences_2.size()) {
      const auto &[bc_1, frequency_1] = sequences_1[i];
      const auto &[bc_2, frequency_2] = sequences_2[j];
      if (frequency_1 > frequency_2) {
        print_code(bc_1.get_ptr());
        ++i;
      } else {
        const char *end = print_code(bc_2.get_ptr());
        std::printf("\t||\t");
        print_code(end);
        ++j;
      }
      std::printf(": %zu\n", std::max(frequency_1, frequency_2));
    }
    while (i < sequences_1.size()) {
      const auto &[bc_1, frequency_1] = sequences_1[i];
      print_code(bc_1.get_ptr());
      ++i;
      std::printf(": %zu\n", frequency_1);
    }
    while (j < sequences_2.size()) {
      const auto &[bc_2, frequency_2] = sequences_2[j];
      const char *end = print_code(bc_2.get_ptr());
      print_code(end);
      ++j;
      std::printf(": %zu\n", frequency_2);
    }
  } catch (std::logic_error &e) {
    fprintf(stderr, "Error: %s!\n", e.what());
    std::exit(1);
  }
  return 0;
}
