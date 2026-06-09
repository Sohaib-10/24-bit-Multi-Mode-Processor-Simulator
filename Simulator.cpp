#include <algorithm>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using std::cerr;
using std::cin;
using std::cout;
using std::exception;
using std::find_if_not;
using std::getline;
using std::hex;
using std::isdigit;
using std::ifstream;
using std::invalid_argument;
using std::isspace;
using std::left;
using std::ostringstream;
using std::replace;
using std::runtime_error;
using std::setfill;
using std::setw;
using std::size_t;
using std::sort;
using std::stoi;
using std::stoll;
using std::stoul;
using std::string;
using std::stringstream;
using std::to_string;
using std::transform;
using std::toupper;
using std::uppercase;
using std::vector;

namespace {

using us_32bint = uint32_t;

constexpr us_32bint WORD_BITS = 24;
constexpr us_32bint WORD_MASK = (1u << WORD_BITS) - 1u;
constexpr us_32bint SIGN_BIT = 1u << (WORD_BITS - 1u);
constexpr us_32bint MEMORY_SIZE = 4096;
constexpr us_32bint STACK_START = 0xFFF;

struct NameValue {
    const char* name;
    int value;
};

struct OpcodeInfo {
    int opcode;
    const char* name;
};

struct LabelEntry {
    string name;
    us_32bint address;
};

struct SourceLineEntry {
    us_32bint address;
    string source;
};

struct Instruction {
    string op = "HLT";
    int rd = 0;
    int rs = 0;
    us_32bint address = 0;
    string mode = "NA";
    string source;
    us_32bint word = 0;
};

struct MemoryCell {
    bool is_instruction = false;
    Instruction instruction;
    us_32bint data = 0;
};

struct MemoryImageEntry {
    us_32bint address = 0;
    MemoryCell cell;
};

struct AssemblyItem {
    us_32bint address = 0;
    int line_number = 0;
    string op;
    string rest;
    string source;
};

struct AssemblyResult {
    vector<MemoryImageEntry> memory_image;
    vector<SourceLineEntry> source_map;
    us_32bint entry_point = 0;
    vector<LabelEntry> labels;
};

struct CommandParts {
    string command;
    string rest;
};

const NameValue REGISTER_NAMES[] = {
    {"R0", 0}, {"R1", 1}, {"R2", 2}, {"R3", 3},
    {"R4", 4}, {"R5", 5}, {"R6", 6}, {"R7", 7},
};

const NameValue SOURCE_REGISTER_NAMES[] = {
    {"R0", 0}, {"R1", 1}, {"R2", 2}, {"R3", 3},
};

const char* const TWO_REGISTER_OPS[] = {"ADD", "SUB", "AND", "OR", "XOR", "MOV"};
const char* const ONE_REGISTER_OPS[] = {"NOT", "INC", "CIL", "CIR", "SHL", "SHR", "PUSH", "POP", "IN", "OUT"};
const char* const MEMORY_OPS[] = {"LOAD", "STORE"};
const char* const JUMP_OPS[] = {"JMP", "JZ", "JN", "JC", "CALL"};
const char* const NO_ARGUMENT_OPS[] = {"RET", "ION", "IOF", "HLT"};

const NameValue MODE_CODES[] = {
    {"NA", 0},
    {"DMA", 1},
    {"IMA", 2},
};

const OpcodeInfo OPCODES[] = {
    {0, "AND"},   {1, "ADD"},   {2, "SUB"},   {3, "STORE"}, {4, "OR"},   {5, "LOAD"},
    {6, "XOR"},   {7, "NOT"},   {8, "CIL"},   {9, "CIR"},   {10, "SHL"}, {11, "SHR"},
    {12, "INC"},  {13, "MOV"},  {14, "JMP"},  {15, "JZ"},   {16, "JN"},  {17, "JC"},
    {18, "CALL"}, {19, "RET"},  {20, "PUSH"}, {21, "POP"},  {22, "HLT"}, {23, "ION"},
    {24, "IOF"},  {25, "IN"},   {26, "OUT"},
};

template <typename T, size_t N>
constexpr size_t count_of(const T (&)[N]) {
    return N;
}

string join_names(const char* const entries[], size_t count) {
    ostringstream stream;
    for (size_t i = 0; i < count; ++i) {
        if (i != 0) {
            stream << ", ";
        }
        stream << entries[i];
    }
    return stream.str();
}

string trim(const string& text) {
    const auto first = find_if_not(text.begin(), text.end(), [](unsigned char ch) { return isspace(ch) != 0; });
    if (first == text.end()) {
        return "";
    }
    const auto last = find_if_not(text.rbegin(), text.rend(), [](unsigned char ch) { return isspace(ch) != 0; }).base();
    return string(first, last);
}

string to_upper(string text) {
    transform(text.begin(), text.end(), text.begin(), [](unsigned char ch) { return static_cast<char>(toupper(ch)); });
    return text;
}

string format_hex(us_32bint value, int width) {
    ostringstream stream;
    stream << uppercase << hex << setw(width) << setfill('0') << value;
    return stream.str();
}

bool is_name_in_list(const string& name, const char* const entries[], size_t count) {
    for (size_t i = 0; i < count; ++i) {
        if (name == entries[i]) {
            return true;
        }
    }
    return false;
}

int find_name_value(const NameValue entries[], size_t count, const string& name) {
    for (size_t i = 0; i < count; ++i) {
        if (name == entries[i].name) {
            return entries[i].value;
        }
    }
    return -1;
}

const char* find_opcode_name(int opcode) {
    for (size_t i = 0; i < count_of(OPCODES); ++i) {
        if (OPCODES[i].opcode == opcode) {
            return OPCODES[i].name;
        }
    }
    return nullptr;
}

int find_opcode_value(const string& name) {
    for (size_t i = 0; i < count_of(OPCODES); ++i) {
        if (name == OPCODES[i].name) {
            return OPCODES[i].opcode;
        }
    }
    return -1;
}

string mode_from_bits(int bits) {
    for (size_t i = 0; i < count_of(MODE_CODES); ++i) {
        if (MODE_CODES[i].value == bits) {
            return MODE_CODES[i].name;
        }
    }
    return "";
}

int find_label_index(const vector<LabelEntry>& labels, const string& name) {
    for (size_t i = 0; i < labels.size(); ++i) {
        if (labels[i].name == name) {
            return static_cast<int>(i);
        }
    }
    return -1;
}

const LabelEntry* find_label(const vector<LabelEntry>& labels, const string& name) {
    const int index = find_label_index(labels, name);
    if (index < 0) {
        return nullptr;
    }
    return &labels[static_cast<size_t>(index)];
}

void set_memory_cell(vector<MemoryImageEntry>& image, us_32bint address, const MemoryCell& cell) {
    address &= 0xFFFu;
    for (size_t i = 0; i < image.size(); ++i) {
        if (image[i].address == address) {
            image[i].cell = cell;
            return;
        }
    }
    MemoryImageEntry entry;
    entry.address = address;
    entry.cell = cell;
    image.push_back(entry);
}

void set_source_line(vector<SourceLineEntry>& source_map, us_32bint address, const string& source) {
    address &= 0xFFFu;
    for (size_t i = 0; i < source_map.size(); ++i) {
        if (source_map[i].address == address) {
            source_map[i].source = source;
            return;
        }
    }
    SourceLineEntry entry;
    entry.address = address;
    entry.source = source;
    source_map.push_back(entry);
}

Instruction make_instruction(
    const string& op,
    int rd = 0,
    int rs = 0,
    us_32bint address = 0,
    const string& mode = "NA",
    const string& source = "",
    us_32bint word = 0) {

    Instruction instruction;
    instruction.op = to_upper(op);
    instruction.rd = rd;
    instruction.rs = rs;
    instruction.address = address;
    instruction.mode = to_upper(mode);
    instruction.source = source;
    instruction.word = word;
    return instruction;
}

string instruction_to_text(const Instruction& instruction) {
    if (is_name_in_list(instruction.op, TWO_REGISTER_OPS, count_of(TWO_REGISTER_OPS))) {
        return instruction.op + " R" + to_string(instruction.rd) + ", R" + to_string(instruction.rs);
    }
    if (is_name_in_list(instruction.op, ONE_REGISTER_OPS, count_of(ONE_REGISTER_OPS))) {
        return instruction.op + " R" + to_string(instruction.rd);
    }
    if (is_name_in_list(instruction.op, MEMORY_OPS, count_of(MEMORY_OPS))) {
        return instruction.op + " R" + to_string(instruction.rd) + ", " + format_hex(instruction.address, 3) + ", " + instruction.mode;
    }
    if (is_name_in_list(instruction.op, JUMP_OPS, count_of(JUMP_OPS))) {
        return instruction.op + " " + format_hex(instruction.address, 3);
    }
    return instruction.op;
}

us_32bint encode_instruction(const Instruction& instruction) {
    const string op = to_upper(instruction.op);
    const int opcode_value = find_opcode_value(op);
    if (opcode_value < 0) {
        throw runtime_error("Cannot encode unknown instruction '" + op + "'.");
    }

    const string mode = to_upper(instruction.mode);
    const int mode_value = find_name_value(MODE_CODES, count_of(MODE_CODES), mode);
    if (mode_value < 0) {
        throw runtime_error("Cannot encode invalid mode '" + mode + "'.");
    }

    const us_32bint opcode = static_cast<us_32bint>(opcode_value) & 0x1F;
    const us_32bint mode_bits = static_cast<us_32bint>(mode_value) & 0x3;
    const us_32bint rd = static_cast<us_32bint>(instruction.rd) & 0x7;
    const us_32bint rs = static_cast<us_32bint>(instruction.rs) & 0x3;
    const us_32bint address = instruction.address & 0xFFF;

    return (opcode << 19u) | (mode_bits << 17u) | (rd << 14u) | (rs << 12u) | address;
}

Instruction decode_instruction_word(us_32bint word, const string& source = "") {
    word &= WORD_MASK;
    const int opcode = static_cast<int>((word >> 19u) & 0x1Fu);
    const int mode_bits = static_cast<int>((word >> 17u) & 0x3u);
    const int rd = static_cast<int>((word >> 14u) & 0x7u);
    const int rs = static_cast<int>((word >> 12u) & 0x3u);
    const us_32bint address = word & 0xFFFu;

    const char* opcode_name = find_opcode_name(opcode);
    if (opcode_name == nullptr) {
        throw runtime_error("Unknown opcode in machine word " + format_hex(word, 6) + ".");
    }

    const string mode_name = mode_from_bits(mode_bits);
    if (mode_name.empty()) {
        throw runtime_error("Invalid mode bits in machine word " + format_hex(word, 6) + ".");
    }

    return make_instruction(
        opcode_name,
        rd,
        rs,
        address,
        mode_name,
        source.empty() ? "HEX " + format_hex(word, 6) : source,
        word);
}

string strip_comment(const string& line) {
    string result = line;
    for (int i = 0; i < 2; ++i) {
        const char marker = (i == 0) ? '#' : ';';
        const size_t position = result.find(marker);
        if (position != string::npos) {
            result = result.substr(0, position);
        }
    }
    return trim(result);
}

int parse_register(const string& token, int line_number) {
    const string name = to_upper(trim(token));
    const int value = find_name_value(REGISTER_NAMES, count_of(REGISTER_NAMES), name);
    if (value < 0) {
        throw runtime_error("Line " + to_string(line_number) + ": invalid register '" + token + "'. Use R0 to R7.");
    }
    return value;
}

int parse_source_register(const string& token, int line_number) {
    const string name = to_upper(trim(token));
    const int value = find_name_value(SOURCE_REGISTER_NAMES, count_of(SOURCE_REGISTER_NAMES), name);
    if (value < 0) {
        throw runtime_error("Line " + to_string(line_number) + ": source register must be R0 to R3 because Rs is 2-bit.");
    }
    return value;
}

int64_t parse_base_number(const string& token, int base) {
    size_t processed = 0;
    const int64_t value = stoll(token, &processed, base);
    if (processed != token.size()) {
        throw invalid_argument("bad number");
    }
    return value;
}

int64_t parse_value(const string& token, const vector<LabelEntry>& labels, int line_number) {
    const string clean = trim(token);
    const string upper = to_upper(clean);

    const LabelEntry* label = find_label(labels, upper);
    if (label != nullptr) {
        return static_cast<int64_t>(label->address);
    }

    try {
        if (upper.rfind("0X", 0) == 0) {
            return parse_base_number(upper, 16);
        }
        if (upper.rfind("0B", 0) == 0) {
            return parse_base_number(upper.substr(2), 2);
        }

        bool has_hex_letter = false;
        bool all_hex = !upper.empty();
        for (size_t i = 0; i < upper.size(); ++i) {
            const char ch = upper[i];
            if (string("ABCDEF").find(ch) != string::npos) {
                has_hex_letter = true;
            }
            if (string("0123456789ABCDEF").find(ch) == string::npos) {
                all_hex = false;
                break;
            }
        }

        if (has_hex_letter && all_hex) {
            return parse_base_number(upper, 16);
        }

        return parse_base_number(clean, 10);
    } catch (const exception&) {
        throw runtime_error("Line " + to_string(line_number) + ": invalid value '" + token + "'.");
    }
}

bool looks_like_hex_word(const string& text) {
    string clean = to_upper(trim(text));
    if (clean.rfind("0X", 0) == 0) {
        clean = clean.substr(2);
    }
    if (clean.empty() || clean.size() > 6) {
        return false;
    }

    for (size_t i = 0; i < clean.size(); ++i) {
        if (string("0123456789ABCDEF").find(clean[i]) == string::npos) {
            return false;
        }
    }
    return true;
}

us_32bint parse_hex_word(const string& token, int line_number) {
    string clean = to_upper(trim(token));
    if (clean.rfind("0X", 0) == 0) {
        clean = clean.substr(2);
    }
    if (!looks_like_hex_word(clean)) {
        throw runtime_error("Line " + to_string(line_number) + ": invalid 24-bit hex word '" + token + "'.");
    }
    const us_32bint value = static_cast<us_32bint>(stoul(clean, nullptr, 16));
    if (value > WORD_MASK) {
        throw runtime_error("Line " + to_string(line_number) + ": machine word '" + token + "' is larger than 24 bits.");
    }
    return value;
}

vector<string> split_args(const string& rest) {
    vector<string> parts;
    if (rest.empty()) {
        return parts;
    }

    stringstream stream(rest);
    string part;
    while (getline(stream, part, ',')) {
        part = trim(part);
        if (!part.empty()) {
            parts.push_back(part);
        }
    }
    return parts;
}

Instruction assemble_instruction(
    const string& op_raw,
    const vector<string>& args,
    const vector<LabelEntry>& labels,
    int line_number,
    const string& source_text) {

    const string op = to_upper(op_raw);

    if (is_name_in_list(op, TWO_REGISTER_OPS, count_of(TWO_REGISTER_OPS))) {
        if (args.size() != 2) {
            throw runtime_error("Line " + to_string(line_number) + ": " + op + " needs 2 registers.");
        }
        Instruction instruction = make_instruction(
            op,
            parse_register(args[0], line_number),
            parse_source_register(args[1], line_number),
            0,
            "NA",
            source_text);
        instruction.word = encode_instruction(instruction);
        return instruction;
    }

    if (is_name_in_list(op, ONE_REGISTER_OPS, count_of(ONE_REGISTER_OPS))) {
        if (args.size() != 1) {
            throw runtime_error("Line " + to_string(line_number) + ": " + op + " needs 1 register.");
        }
        const int register_index = parse_register(args[0], line_number);
        Instruction instruction = make_instruction(op, register_index, register_index, 0, "NA", source_text);
        instruction.word = encode_instruction(instruction);
        return instruction;
    }

    if (is_name_in_list(op, MEMORY_OPS, count_of(MEMORY_OPS))) {
        if (args.size() != 2 && args.size() != 3) {
            throw runtime_error("Line " + to_string(line_number) + ": " + op + " needs register, address, and optional mode.");
        }
        const string mode = (args.size() == 3) ? args[2] : "DMA";
        Instruction instruction = make_instruction(
            op,
            parse_register(args[0], line_number),
            0,
            static_cast<us_32bint>(parse_value(args[1], labels, line_number)),
            mode,
            source_text);
        instruction.word = encode_instruction(instruction);
        return instruction;
    }

    if (is_name_in_list(op, JUMP_OPS, count_of(JUMP_OPS))) {
        if (args.size() != 1) {
            throw runtime_error("Line " + to_string(line_number) + ": " + op + " needs 1 address or label.");
        }
        Instruction instruction = make_instruction(
            op,
            0,
            0,
            static_cast<us_32bint>(parse_value(args[0], labels, line_number)),
            "NA",
            source_text);
        instruction.word = encode_instruction(instruction);
        return instruction;
    }

    if (is_name_in_list(op, NO_ARGUMENT_OPS, count_of(NO_ARGUMENT_OPS))) {
        if (!args.empty()) {
            throw runtime_error("Line " + to_string(line_number) + ": " + op + " does not take arguments.");
        }
        Instruction instruction = make_instruction(op, 0, 0, 0, "NA", source_text);
        instruction.word = encode_instruction(instruction);
        return instruction;
    }

    throw runtime_error("Line " + to_string(line_number) + ": unknown instruction '" + op + "'.");
}

AssemblyResult assemble_source(const string& source_code) {
    vector<LabelEntry> labels;
    vector<AssemblyItem> items;
    us_32bint current_address = 0;
    bool has_first_instruction = false;
    us_32bint first_instruction_address = 0;

    stringstream source_stream(source_code);
    string raw_line;
    int line_number = 0;

    while (getline(source_stream, raw_line)) {
        ++line_number;
        string line = strip_comment(raw_line);
        if (line.empty()) {
            continue;
        }

        const size_t colon = line.find(':');
        if (colon != string::npos) {
            const string label = to_upper(trim(line.substr(0, colon)));
            if (label.empty()) {
                throw runtime_error("Line " + to_string(line_number) + ": empty label.");
            }
            if (find_label(labels, label) != nullptr) {
                throw runtime_error("Line " + to_string(line_number) + ": duplicate label '" + label + "'.");
            }
            LabelEntry entry;
            entry.name = label;
            entry.address = current_address;
            labels.push_back(entry);
            line = trim(line.substr(colon + 1));
            if (line.empty()) {
                continue;
            }
        }

        stringstream line_stream(line);
        string op;
        line_stream >> op;
        string rest;
        getline(line_stream, rest);
        rest = trim(rest);

        op = to_upper(op);
        if (looks_like_hex_word(op) && rest.empty()) {
            rest = op;
            op = "HEX";
        }

        if (op == "ORG") {
            if (rest.empty()) {
                throw runtime_error("Line " + to_string(line_number) + ": ORG needs an address.");
            }
            current_address = static_cast<us_32bint>(parse_value(rest, labels, line_number)) & 0xFFFu;
            continue;
        }

        AssemblyItem item;
        item.address = current_address;
        item.line_number = line_number;
        item.op = op;
        item.rest = rest;
        item.source = line;
        items.push_back(item);

        if (op != "DATA" && !has_first_instruction) {
            first_instruction_address = current_address;
            has_first_instruction = true;
        }

        current_address = (current_address + 1u) & 0xFFFu;
    }

    AssemblyResult result;
    result.entry_point = has_first_instruction ? first_instruction_address : 0;
    result.labels = labels;

    for (size_t i = 0; i < items.size(); ++i) {
        const AssemblyItem& item = items[i];
        if (item.op == "HEX") {
            Instruction instruction = decode_instruction_word(parse_hex_word(item.rest, item.line_number), item.source);
            set_memory_cell(result.memory_image, item.address, MemoryCell{true, instruction, 0});
            set_source_line(result.source_map, item.address, item.source);
            continue;
        }

        if (item.op == "DATA") {
            if (item.rest.empty()) {
                throw runtime_error("Line " + to_string(item.line_number) + ": DATA needs a value.");
            }
            const us_32bint value = static_cast<us_32bint>(parse_value(item.rest, result.labels, item.line_number)) & WORD_MASK;
            set_memory_cell(result.memory_image, item.address, MemoryCell{false, Instruction{}, value});
            set_source_line(result.source_map, item.address, item.source);
            continue;
        }

        Instruction instruction = assemble_instruction(item.op, split_args(item.rest), result.labels, item.line_number, item.source);
        set_memory_cell(result.memory_image, item.address, MemoryCell{true, instruction, 0});
        set_source_line(result.source_map, item.address, item.source);
    }

    return result;
}

class Processor24Bit {
public:
    Processor24Bit() {
        reset(true);
    }

    void reset(bool clear_memory = true) {
        if (clear_memory) {
            memory.assign(MEMORY_SIZE, MemoryCell{});
        }
        for (us_32bint& reg : registers) {
            reg = 0;
        }
        registers[7] = STACK_START;
        pc = 0;
        ar = 0;
        ir_valid = false;
        halted = false;
        psr = ProcessorStatusRegister{};
        input_buffer.clear();
        output_buffer.clear();
    }

    void load_memory_image(const vector<MemoryImageEntry>& memory_image, us_32bint start_address = 0) {
        reset(true);
        for (size_t i = 0; i < memory_image.size(); ++i) {
            memory[memory_image[i].address & 0xFFFu] = memory_image[i].cell;
        }
        pc = start_address & 0xFFFu;
    }

    us_32bint mask24(us_32bint value) const {
        return value & WORD_MASK;
    }

    string normalize_mode(string mode) const {
        mode = to_upper(trim(mode));
        if (mode == "NA" || mode == "00") {
            return "NA";
        }
        if (mode == "DMA" || mode == "01") {
            return "DMA";
        }
        if (mode == "IMA" || mode == "10") {
            return "IMA";
        }
        return mode;
    }

    us_32bint read_register(int index) const {
        const us_32bint value = registers[index];
        return value;
    }

    void write_register(int index, us_32bint value) {
        if (index == 0) {
            return;
        }
        registers[index] = mask24(value);
    }

    void update_nz_flags(us_32bint value) {
        value = mask24(value);
        psr.Z = (value == 0) ? 1 : 0;
        psr.N = ((value & SIGN_BIT) != 0) ? 1 : 0;
    }

    void update_add_flags(us_32bint a, us_32bint b, us_32bint result) {
        a = mask24(a);
        b = mask24(b);
        result = mask24(result);
        update_nz_flags(result);
        psr.C = (static_cast<uint64_t>(a) + static_cast<uint64_t>(b) > WORD_MASK) ? 1 : 0;

        const bool a_sign = (a & SIGN_BIT) != 0;
        const bool b_sign = (b & SIGN_BIT) != 0;
        const bool r_sign = (result & SIGN_BIT) != 0;
        psr.V = (a_sign == b_sign && a_sign != r_sign) ? 1 : 0;
    }

    void update_sub_flags(us_32bint a, us_32bint b, us_32bint result) {
        a = mask24(a);
        b = mask24(b);
        result = mask24(result);
        update_nz_flags(result);
        psr.C = (a >= b) ? 1 : 0;

        const bool a_sign = (a & SIGN_BIT) != 0;
        const bool b_sign = (b & SIGN_BIT) != 0;
        const bool r_sign = (result & SIGN_BIT) != 0;
        psr.V = (a_sign != b_sign && a_sign != r_sign) ? 1 : 0;
    }

    us_32bint get_data(us_32bint address) const {
        const MemoryCell& cell = memory[address & 0xFFFu];
        if (cell.is_instruction) {
            throw runtime_error("Tried to read instruction memory as data.");
        }
        return mask24(cell.data);
    }

    Instruction fetch() {
        ar = pc;
        const MemoryCell& cell = memory[ar];
        pc = (pc + 1u) & 0xFFFu;

        if (!cell.is_instruction) {
            throw runtime_error("Memory at address " + format_hex(ar, 3) + " does not contain an instruction.");
        }

        ir = cell.instruction;
        ir_valid = true;
        return ir;
    }

    us_32bint resolve_data_address(const string& raw_mode, us_32bint address) {
        const string mode = normalize_mode(raw_mode);
        address &= 0xFFFu;

        if (mode == "DMA") {
            ar = address;
            return ar;
        }

        if (mode == "IMA") {
            ar = address;
            const us_32bint pointer = get_data(ar);
            ar = pointer & 0xFFFu;
            return ar;
        }

        throw runtime_error(mode + " is not valid for memory access.");
    }

    us_32bint load_operand(const string& mode, us_32bint address) {
        const us_32bint final_address = resolve_data_address(mode, address);
        return get_data(final_address);
    }

    void store_operand(const string& mode, us_32bint address, us_32bint value) {
        const us_32bint final_address = resolve_data_address(mode, address);
        memory[final_address] = MemoryCell{false, Instruction{}, mask24(value)};
    }

    void push(us_32bint value) {
        const us_32bint sp = (read_register(7) - 1u) & 0xFFFu;
        write_register(7, sp);
        memory[sp] = MemoryCell{false, Instruction{}, mask24(value)};
    }

    us_32bint pop() {
        const us_32bint sp = read_register(7) & 0xFFFu;
        const us_32bint value = get_data(sp);
        write_register(7, (sp + 1u) & 0xFFFu);
        return value;
    }

    void step() {
        if (halted) {
            return;
        }

        const Instruction instruction = fetch();
        const string op = instruction.op;
        const int rd = instruction.rd;
        const int rs = instruction.rs;
        const us_32bint address = instruction.address;
        const string mode = normalize_mode(instruction.mode);

        const us_32bint rd_value = read_register(rd);
        const us_32bint rs_value = read_register(rs);

        if (op == "ADD") {
            const us_32bint result = rd_value + rs_value;
            write_register(rd, result);
            update_add_flags(rd_value, rs_value, result);
        } else if (op == "SUB") {
            const us_32bint result = rd_value - rs_value;
            write_register(rd, result);
            update_sub_flags(rd_value, rs_value, result);
        } else if (op == "AND") {
            const us_32bint result = rd_value & rs_value;
            write_register(rd, result);
            update_nz_flags(result);
            psr.C = 0;
            psr.V = 0;
        } else if (op == "OR") {
            const us_32bint result = rd_value | rs_value;
            write_register(rd, result);
            update_nz_flags(result);
            psr.C = 0;
            psr.V = 0;
        } else if (op == "XOR") {
            const us_32bint result = rd_value ^ rs_value;
            write_register(rd, result);
            update_nz_flags(result);
            psr.C = 0;
            psr.V = 0;
        } else if (op == "NOT") {
            const us_32bint result = ~rd_value;
            write_register(rd, result);
            update_nz_flags(result);
        } else if (op == "INC") {
            const us_32bint result = rd_value + 1u;
            write_register(rd, result);
            update_add_flags(rd_value, 1u, result);
        } else if (op == "MOV") {
            write_register(rd, rs_value);
        } else if (op == "CIL") {
            const us_32bint carry_out = (rd_value >> 23u) & 1u;
            const us_32bint result = ((rd_value << 1u) & WORD_MASK) | carry_out;
            write_register(rd, result);
            update_nz_flags(result);
            psr.C = static_cast<int>(carry_out);
        } else if (op == "CIR") {
            const us_32bint carry_out = rd_value & 1u;
            const us_32bint result = (rd_value >> 1u) | (carry_out << 23u);
            write_register(rd, result);
            update_nz_flags(result);
            psr.C = static_cast<int>(carry_out);
        } else if (op == "SHL") {
            const us_32bint carry_out = (rd_value >> 23u) & 1u;
            const us_32bint result = (rd_value << 1u) & WORD_MASK;
            write_register(rd, result);
            update_nz_flags(result);
            psr.C = static_cast<int>(carry_out);
        } else if (op == "SHR") {
            const us_32bint carry_out = rd_value & 1u;
            const us_32bint result = rd_value >> 1u;
            write_register(rd, result);
            update_nz_flags(result);
            psr.C = static_cast<int>(carry_out);
        } else if (op == "LOAD") {
            write_register(rd, load_operand(mode, address));
        } else if (op == "STORE") {
            store_operand(mode, address, rd_value);
        } else if (op == "JMP") {
            pc = address & 0xFFFu;
        } else if (op == "JZ") {
            if (psr.Z == 1) {
                pc = address & 0xFFFu;
            }
        } else if (op == "JN") {
            if (psr.N == 1) {
                pc = address & 0xFFFu;
            }
        } else if (op == "JC") {
            if (psr.C == 1) {
                pc = address & 0xFFFu;
            }
        } else if (op == "CALL") {
            const us_32bint return_address = pc;
            write_register(6, return_address);
            push(return_address);
            pc = address & 0xFFFu;
        } else if (op == "RET") {
            pc = pop() & 0xFFFu;
        } else if (op == "PUSH") {
            push(rd_value);
        } else if (op == "POP") {
            write_register(rd, pop());
        } else if (op == "IN") {
            us_32bint value = 0;
            if (!input_buffer.empty()) {
                value = input_buffer.front();
                input_buffer.erase(input_buffer.begin());
            }
            write_register(rd, value & 0xFFu);
        } else if (op == "OUT") {
            output_buffer.push_back(rd_value);
        } else if (op == "ION") {
            psr.I = 1;
        } else if (op == "IOF") {
            psr.I = 0;
        } else if (op == "HLT") {
            psr.I = 0;
            halted = true;
        } else {
            throw runtime_error("Unknown instruction: " + op);
        }

        registers[0] = 0;
    }

    string dump_state() const {
        ostringstream stream;
        stream << "PC=" << format_hex(pc, 3) << " AR=" << format_hex(ar, 3);
        for (int i = 0; i < 8; ++i) {
            stream << " R" << i << "=" << format_hex(read_register(i), 6);
        }
        stream << " Z=" << psr.Z
               << " N=" << psr.N
               << " C=" << psr.C
               << " V=" << psr.V
               << " I=" << psr.I
               << " M=" << psr.M;
        return stream.str();
    }

    struct ProcessorStatusRegister {
        int Z = 0;
        int N = 0;
        int C = 0;
        int V = 0;
        int I = 0;
        int M = 0;
    };

    vector<MemoryCell> memory = vector<MemoryCell>(MEMORY_SIZE);
    us_32bint registers[8] = {};
    us_32bint pc = 0;
    us_32bint ar = 0;
    Instruction ir;
    bool ir_valid = false;
    bool halted = false;
    ProcessorStatusRegister psr;
    vector<us_32bint> input_buffer;
    vector<us_32bint> output_buffer;
};

class TerminalSimulator {
public:
    TerminalSimulator() {
        status = "Load or enter a program, then assemble it.";
    }

    void load_file(const string& path) {
        ifstream file(path.c_str());
        if (!file) {
            throw runtime_error("Could not open file: " + path);
        }
        ostringstream stream;
        stream << file.rdbuf();
        current_source = stream.str();
        loaded_source_signature.clear();
        status = "Loaded source from " + path;
    }

    void set_input_text(const string& text) {
        current_input_text = trim(text);
        loaded_input_signature.clear();
        status = "Input buffer updated.";
    }

    void assemble_current() {
        const AssemblyResult result = assemble_source(current_source);
        cpu.load_memory_image(result.memory_image, result.entry_point);
        cpu.input_buffer = parse_input_buffer(current_input_text);
        source_map = result.source_map;
        labels = result.labels;
        loaded_source_signature = current_source;
        loaded_input_signature = current_input_text;
        status = "Program assembled successfully. Entry point = " + format_hex(result.entry_point, 3) + ".";
    }

    bool ensure_loaded() {
        if (loaded_source_signature != current_source || loaded_input_signature != current_input_text) {
            assemble_current();
        }
        return loaded_source_signature == current_source && loaded_input_signature == current_input_text;
    }

    void step_program() {
        if (!ensure_loaded()) {
            return;
        }
        if (cpu.halted) {
            status = "Processor is already halted. Use 'reset' to run again.";
            return;
        }
        cpu.step();
        status = cpu.halted ? "One step executed. Processor halted." : "One step executed.";
    }

    void run_program(int max_steps = 500) {
        if (!ensure_loaded()) {
            return;
        }
        int steps = 0;
        while (!cpu.halted && steps < max_steps) {
            cpu.step();
            ++steps;
        }
        if (cpu.halted) {
            status = "Program finished after " + to_string(steps) + " step(s).";
        } else {
            status = "Stopped after " + to_string(steps) + " step(s). Increase the limit and run again if needed.";
        }
    }

    void reset_program() {
        loaded_source_signature.clear();
        loaded_input_signature.clear();
        assemble_current();
    }

    void replace_source_from_stdin() {
        cout << "Enter assembly source. Finish with a line containing only .end\n";
        ostringstream stream;
        string line;
        while (getline(cin, line)) {
            if (trim(line) == ".end") {
                break;
            }
            stream << line << '\n';
        }
        current_source = stream.str();
        loaded_source_signature.clear();
        status = "Source updated from terminal input.";
    }

    void print_help() const {
        cout
            << "Commands:\n"
            << "  help                 Show this help text\n"
            << "  instructions         Show all supported assembly instructions\n"
            << "  load-file <path>     Load assembly source from a file\n"
            << "  source               Paste assembly source until .end\n"
            << "  show-source          Print the current source code\n"
            << "  set-input <values>   Set input bytes, e.g. 65 66 67 or 0x41,0x42\n"
            << "  assemble             Assemble the current source\n"
            << "  step                 Execute one instruction\n"
            << "  run [steps]          Run until halt or the step limit\n"
            << "  reset                Reassemble and reset CPU state\n"
            << "  state                Print CPU state\n"
            << "  memory               Print used memory\n"
            << "  output               Print output buffer\n"
            << "  labels               Print resolved labels\n"
            << "  status               Show the latest status message\n"
            << "  quit                 Exit the simulator\n";
    }

    void print_instructions() const {
        cout
            << "Supported assembly instructions:\n"
            << "  Two-register     : " << join_names(TWO_REGISTER_OPS, count_of(TWO_REGISTER_OPS)) << '\n'
            << "  One-register     : " << join_names(ONE_REGISTER_OPS, count_of(ONE_REGISTER_OPS)) << '\n'
            << "  Memory           : " << join_names(MEMORY_OPS, count_of(MEMORY_OPS)) << '\n'
            << "  Jumps / calls    : " << join_names(JUMP_OPS, count_of(JUMP_OPS)) << '\n'
            << "  No-argument      : " << join_names(NO_ARGUMENT_OPS, count_of(NO_ARGUMENT_OPS)) << "\n\n"
            << "Common formats:\n"
            << "  ADD R1, R2\n"
            << "  INC R1\n"
            << "  LOAD R1, NUM, DMA\n"
            << "  STORE R1, NUM, DMA\n"
            << "  JMP LOOP\n"
            << "  HLT\n\n"
            << "Addressing modes:\n"
            << "  DMA = direct memory access\n"
            << "  IMA = indirect memory access\n";
    }

    void print_status() const {
        cout << status << '\n';
    }

    void print_source() const {
        if (trim(current_source).empty()) {
            cout << "(source is empty)\n";
            return;
        }
        cout << current_source;
        if (!current_source.empty() && current_source[current_source.size() - 1] != '\n') {
            cout << '\n';
        }
    }

    void print_state() const {
        cout << build_state_text() << '\n';
    }

    void print_memory() const {
        cout << build_memory_text() << '\n';
    }

    void print_output() const {
        cout << build_output_text() << '\n';
    }

    void print_registers() const {
        cout << build_registers_text() << '\n';
    }

    void print_labels() const {
        if (labels.empty()) {
            cout << "No labels loaded.\n";
            return;
        }

        vector<LabelEntry> sorted_labels = labels;
        sort(sorted_labels.begin(), sorted_labels.end(), [](const LabelEntry& a, const LabelEntry& b) {
            return a.name < b.name;
        });

        for (size_t i = 0; i < sorted_labels.size(); ++i) {
            cout << left << setw(18) << sorted_labels[i].name << " " << format_hex(sorted_labels[i].address, 3) << '\n';
        }
    }

    bool is_halted() const {
        return cpu.halted;
    }

private:
    vector<us_32bint> parse_input_buffer(const string& text) const {
        string clean = trim(text);
        if (clean.empty()) {
            return vector<us_32bint>();
        }

        replace(clean.begin(), clean.end(), ',', ' ');
        stringstream stream(clean);
        string token;
        vector<us_32bint> values;
        const vector<LabelEntry> empty_labels;
        while (stream >> token) {
            values.push_back(static_cast<us_32bint>(parse_value(token, empty_labels, 0)) & 0xFFu);
        }
        return values;
    }

    string build_state_text() const {
        ostringstream stream;
        stream << "PC : " << format_hex(cpu.pc, 3) << '\n';
        stream << "AR : " << format_hex(cpu.ar, 3) << '\n';
        stream << "SP : " << format_hex(cpu.read_register(7), 3) << "\n\n";

        if (cpu.ir_valid) {
            stream << "Current IR : " << (!cpu.ir.source.empty() ? cpu.ir.source : instruction_to_text(cpu.ir)) << "\n\n";
        } else {
            stream << "Current IR : None\n\n";
        }

        stream << build_registers_text();

        stream << "\nFlags:\n";
        stream << "Z = " << cpu.psr.Z << '\n';
        stream << "N = " << cpu.psr.N << '\n';
        stream << "C = " << cpu.psr.C << '\n';
        stream << "V = " << cpu.psr.V << '\n';
        stream << "I = " << cpu.psr.I << '\n';
        stream << "M = " << cpu.psr.M;
        return stream.str();
    }

    string build_memory_text() const {
        vector<bool> used_addresses(MEMORY_SIZE, false);
        for (size_t i = 0; i < source_map.size(); ++i) {
            used_addresses[source_map[i].address & 0xFFFu] = true;
        }

        for (us_32bint address = 0; address < cpu.memory.size(); ++address) {
            const MemoryCell& cell = cpu.memory[address];
            if (cell.is_instruction || cell.data != 0) {
                used_addresses[address] = true;
            }
        }

        bool has_any = false;
        for (size_t i = 0; i < used_addresses.size(); ++i) {
            if (used_addresses[i]) {
                has_any = true;
                break;
            }
        }

        if (!has_any) {
            return "Memory is empty.";
        }

        ostringstream stream;
        bool first = true;
        for (us_32bint address = 0; address < used_addresses.size(); ++address) {
            if (!used_addresses[address]) {
                continue;
            }
            if (!first) {
                stream << '\n';
            }
            first = false;

            const MemoryCell& cell = cpu.memory[address];
            if (cell.is_instruction) {
                const string text = !cell.instruction.source.empty() ? cell.instruction.source : instruction_to_text(cell.instruction);
                stream << format_hex(address, 3) << ": " << text;
            } else {
                stream << format_hex(address, 3) << ": DATA " << format_hex(cell.data, 6) << " (" << cell.data << ")";
            }
        }
        return stream.str();
    }

    string build_registers_text() const {
        ostringstream stream;
        stream << "Registers:\n";
        for (int i = 0; i < 8; ++i) {
            const us_32bint value = cpu.read_register(i);
            stream << "R" << i << " = " << format_hex(value, 6) << " (" << value << ")\n";
        }
        return stream.str();
    }

    string build_output_text() const {
        if (cpu.output_buffer.empty()) {
            return "No output yet.";
        }

        ostringstream numbers;
        ostringstream chars;
        for (size_t i = 0; i < cpu.output_buffer.size(); ++i) {
            if (i != 0) {
                numbers << ' ';
            }
            const us_32bint value = cpu.output_buffer[i];
            numbers << value;

            const unsigned char ch = static_cast<unsigned char>(value & 0xFFu);
            chars << ((ch >= 32 && ch <= 126) ? static_cast<char>(ch) : '.');
        }

        return "Decimal: " + numbers.str() + "\nASCII  : " + chars.str();
    }

    Processor24Bit cpu;
    vector<SourceLineEntry> source_map;
    vector<LabelEntry> labels;
    string current_source;
    string current_input_text;
    string loaded_source_signature;
    string loaded_input_signature;
    string status;
};

CommandParts split_command(const string& line) {
    const string clean = trim(line);
    if (clean.empty()) {
        return CommandParts{};
    }

    stringstream stream(clean);
    CommandParts parts;
    stream >> parts.command;
    getline(stream, parts.rest);
    parts.command = to_upper(parts.command);
    parts.rest = trim(parts.rest);
    return parts;
}

} 

int main(int argc, char* argv[]) {
    TerminalSimulator simulator;

    try {
        if (argc >= 3 && string(argv[1]) == "--file") {
            simulator.load_file(argv[2]);
            simulator.assemble_current();
        }
    } catch (const exception& error) {
        cerr << "Startup error: " << error.what() << '\n';
    }

    cout << "24-Bit Processor Simulator (Terminal C++ Version)\n";
    cout << "Type 'help' to see available commands.\n\n";

    simulator.print_status();

    string line;
    while (true) {
        cout << "\nsim> ";
        if (!getline(cin, line)) {
            cout << '\n';
            break;
        }

        const CommandParts command_parts = split_command(line);
        const string& command = command_parts.command;
        const string& rest = command_parts.rest;
        if (command.empty()) {
            continue;
        }

        try {
            if (command == "HELP") {
                simulator.print_help();
            } else if (command == "INSTRUCTIONS") {
                simulator.print_instructions();
            } else if (command == "LOAD-FILE") {
                simulator.load_file(rest);
                simulator.print_status();
            } else if (command == "SOURCE") {
                simulator.replace_source_from_stdin();
                simulator.print_status();
            } else if (command == "SHOW-SOURCE") {
                simulator.print_source();
            } else if (command == "SET-INPUT") {
                simulator.set_input_text(rest);
                simulator.print_status();
            } else if (command == "ASSEMBLE") {
                simulator.assemble_current();
                simulator.print_status();
            } else if (command == "STEP") {
                simulator.step_program();
                simulator.print_status();
                simulator.print_state();
            } else if (command == "RUN") {
                const int max_steps = rest.empty() ? 500 : stoi(rest);
                simulator.run_program(max_steps);
                simulator.print_status();
                if (simulator.is_halted()) {
                    simulator.print_registers();
                }
            } else if (command == "RESET") {
                simulator.reset_program();
                simulator.print_status();
            } else if (command == "STATE") {
                simulator.print_state();
            } else if (command == "MEMORY") {
                simulator.print_memory();
            } else if (command == "OUTPUT") {
                simulator.print_output();
            } else if (command == "LABELS") {
                simulator.print_labels();
            } else if (command == "STATUS") {
                simulator.print_status();
            } else if (command == "QUIT" || command == "EXIT") {
                break;
            } else {
                cout << "Unknown command. Type 'help' to see the available commands.\n";
            }
        } catch (const exception& error) {
            cout << "Error: " << error.what() << '\n';
        }
    }

    return 0;
}
