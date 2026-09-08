#include "bridge.h"
#include "simdjson.h"
#include <algorithm>
#include <chrono>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

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

void preflight(simdjson::ondemand::parser &parser, const std::vector<Fixture> &fixtures) {
  for (const auto &fixture : fixtures) {
    BenchOutput oak{}, simd{};
    if (!oak_benchmark_decode(fixture.input.data(), uint32_t(fixture.input.size()), &oak) ||
        !simd_decode(parser, fixture.input, simd) || !equal(oak, fixture.expected) || !equal(simd, fixture.expected))
      throw std::runtime_error("valid fixture mismatch");
  }
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
  for (const auto &text : invalid) {
    simdjson::padded_string input(text);
    BenchOutput value{};
    if (oak_benchmark_decode(input.data(), uint32_t(input.size()), &value) || simd_decode(parser, input, value))
      throw std::runtime_error("invalid fixture accepted: " + text);
  }
}

template<bool Oak> void measure(simdjson::ondemand::parser &parser,
    const std::vector<Fixture> &fixtures, size_t rounds, size_t sample, uint64_t bytes) {
  uint64_t checksum = 0;
  auto start = std::chrono::steady_clock::now();
  for (size_t round = 0; round < rounds; ++round) {
    for (const auto &fixture : fixtures) {
      BenchOutput value;
      bool ok;
      if constexpr (Oak) ok = oak_benchmark_decode(fixture.input.data(), uint32_t(fixture.input.size()), &value);
      else ok = simd_decode(parser, fixture.input, value);
      if (!ok) throw std::runtime_error("timed decode failed");
      checksum += digest(value);
    }
  }
  auto ns = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now() - start).count();
  uint64_t expected = 0;
  for (const auto &fixture : fixtures) expected += digest(fixture.expected);
  if (checksum != expected * rounds) throw std::runtime_error("timed checksum mismatch");
  std::cout << "{\"backend\":\"" << (Oak ? "oak" : "simdjson_ondemand")
    << "\",\"sample\":" << sample << ",\"ns\":" << ns
    << ",\"documents\":" << fixtures.size() * rounds << ",\"bytes\":" << bytes * rounds
    << ",\"checksum\":" << checksum << "}\n";
}

int main(int argc, char **argv) {
  try {
    if (argc != 4) throw std::runtime_error("expected documents rounds samples");
    size_t documents = std::stoull(argv[1]), rounds = std::stoull(argv[2]), samples = std::stoull(argv[3]);
    if (!documents || !rounds || !samples || documents > 1000000 || rounds > 1000000 || samples > 100)
      throw std::runtime_error("arguments exceed supported bounds");
    auto fixtures = corpus(documents);
    size_t maximum = 1024;
    uint64_t bytes = 0;
    for (const auto &fixture : fixtures) { bytes += fixture.input.size(); maximum = std::max(maximum, fixture.input.size()); }
    simdjson::ondemand::parser parser;
    if (parser.allocate(maximum)) throw std::runtime_error("parser allocation failed");
    preflight(parser, fixtures);
    std::cout << "{\"simdjson_implementation\":\"" << simdjson::get_active_implementation()->name()
      << "\",\"corpus_bytes\":" << bytes << ",\"max_document_capacity\":" << maximum << "}\n";
    // Alternate backend order to reduce systematic thermal/order bias.
    for (size_t sample = 0; sample < samples; ++sample) {
      if (sample % 2 == 0) { measure<true>(parser, fixtures, rounds, sample, bytes); measure<false>(parser, fixtures, rounds, sample, bytes); }
      else { measure<false>(parser, fixtures, rounds, sample, bytes); measure<true>(parser, fixtures, rounds, sample, bytes); }
    }
  } catch (const std::exception &e) { std::cerr << e.what() << '\n'; return 1; }
}
