// The typed-record workload: `id: u64, active: Bool, samples: [4]i32`,
// about ninety bytes per document, fields in two orders, an escaped key in
// every fourth document, integers at their bounds.
#include "bridge.h"

// Match Oak's required-field schema, including escaped keys and integer-only
// lexical forms. Consume every field and array element before accepting.
__attribute__((noinline)) bool simd_decode(simdjson::ondemand::parser &parser,
    const simdjson::padded_string &input, BenchOutput &out) {
  try {
    simdjson::ondemand::document doc = parser.iterate(input);
    unsigned seen = 0;
    for (auto field : doc.get_object()) {
      std::string_view key = field.unescaped_key();
      unsigned bit = key == "id" ? 1 : key == "active" ? 2 : key == "samples" ? 4 : 0;
      if (!bit || (seen & bit)) return false;
      seen |= bit;
      auto value = field.value();
      if (bit == 1) {
        // Oak rejects an unsigned minus sign, including -0.
        std::string_view raw = value.raw_json_token();
        if (raw.empty() || raw.front() == '-') return false;
        out.id = uint64_t(value.get_uint64());
      } else if (bit == 2) {
        out.active = bool(value.get_bool());
      } else {
        unsigned count = 0;
        for (auto item : value.get_array()) {
          if (count == 4) return false;
          int64_t n = item.get_int64();
          if (n < INT32_MIN || n > INT32_MAX) return false;
          out.samples[count++] = int32_t(n);
        }
        if (count != 4) return false;
      }
    }
    return seen == 7 && doc.at_end();
  } catch (const simdjson::simdjson_error &) {
    return false;
  }
}

bool equal(const BenchOutput &a, const BenchOutput &b) {
  if (a.id != b.id || a.active != b.active) return false;
  for (unsigned i = 0; i < 4; ++i) if (a.samples[i] != b.samples[i]) return false;
  return true;
}

uint64_t digest(const BenchOutput &value) {
  uint64_t hash = value.id ^ (uint64_t(value.active) << 63);
  for (int32_t n : value.samples) hash = (hash ^ uint32_t(n)) * UINT64_C(1099511628211);
  return hash;
}

struct Fixture {
  simdjson::padded_string input;
  BenchOutput expected;
};

std::vector<Fixture> corpus(size_t count) {
  std::vector<Fixture> fixtures;
  fixtures.reserve(count);
  for (size_t i = 0; i < count; ++i) {
    BenchOutput expected{};
    expected.id = i % 3 == 0 ? UINT64_MAX : uint64_t(i) * 9007199254740993ULL;
    expected.active = i % 2;
    expected.samples[0] = INT32_MIN;
    expected.samples[1] = INT32_MAX;
    expected.samples[2] = int32_t(i % 1000000);
    expected.samples[3] = -int32_t(i % 1000000);
    std::string id = "\"id\":" + std::to_string(expected.id);
    std::string active = std::string(i % 4 == 0 ? "\"\\u0061ctive\":" : "\"active\":") + (expected.active ? "true" : "false");
    std::string samples = "\"samples\":[-2147483648,2147483647," + std::to_string(expected.samples[2]) + "," + std::to_string(expected.samples[3]) + "]";
    std::string text = i % 2 ? "{" + id + "," + active + "," + samples + "}" : " { " + samples + ", " + active + ", " + id + " } ";
    fixtures.push_back({simdjson::padded_string(text), expected});
  }
  return fixtures;
}

std::vector<std::string> invalid_inputs() {
  std::vector<std::string> invalid = {
    "", "null", "[]", "{}", "{\"id\":-0}", "{\"id\":18446744073709551616}",
    "{\"id\":1.0}", "{\"id\":01}", "{\"id\":1,\"id\":2}",
    "{\"id\":1,\"\\u0069d\":2}", "{\"unknown\":0}", "{\"active\":1}",
    "{\"id\":1,\"active\":false,\"samples\":[0,1,2]}",
    "{\"id\":1,\"active\":false,\"samples\":[0,1,2,3,4]}",
    "{\"id\":1,\"active\":false,\"samples\":[0,1,2,2147483648]}",
    "{\"id\":1,\"active\":false,\"samples\":[0,1,2,3,]}",
    "{\"id\":1,\"active\":false,\"samples\":[0,1,2,3]} {}",
    "{\"id\":1,\"active\":false,\"samples\":[0,1,2,3]}x",
    std::string("{\"") + char(255) + "\":0}"
  };
  // Isolate lexical/type failures from missing-field failures.
  for (const std::string &id : {"-0", "-1", "18446744073709551616", "1.0", "1e0", "01", "true", "null"})
    invalid.push_back("{\"id\":" + id + ",\"active\":false,\"samples\":[0,1,2,3]}");
  for (const std::string &items : {"0,1,2,3.0", "0,1,2,3e0", "0,1,2,-2147483649", "0,1,2,true", "0,1,2 3"})
    invalid.push_back("{\"id\":0,\"active\":false,\"samples\":[" + items + "]}");
  invalid.push_back("{\"id\":0,\"active\":1,\"samples\":[0,1,2,3]}");
  invalid.push_back("{\"id\":0,\"active\":false,\"samples\":[0,1,2,3],\"\\u0069d\":1}");
  invalid.push_back("{\"id\":0,\"active\":false,\"samples\":[0,1,2,3],\"unknown\":0}");
  return invalid;
}
