#include "simdjson.h"
#include <algorithm>
#include <chrono>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

// The workload header supplies BenchOutput (through its bridge header), the
// simdjson reader with Oak's acceptance rules, equality and digest of the
// output, the fixture corpus, and the invalid inputs both must reject.
#ifndef OAK_JSON_WORKLOAD_HEADER
#define OAK_JSON_WORKLOAD_HEADER "workload_record.h"
#endif
#include OAK_JSON_WORKLOAD_HEADER

void preflight(simdjson::ondemand::parser &parser, const std::vector<Fixture> &fixtures) {
  for (const auto &fixture : fixtures) {
    BenchOutput oak{}, simd{};
    if (!oak_benchmark_decode(fixture.input.data(), uint32_t(fixture.input.size()), &oak) ||
        !simd_decode(parser, fixture.input, simd) || !equal(oak, fixture.expected) || !equal(simd, fixture.expected))
      throw std::runtime_error("valid fixture mismatch");
  }
  std::vector<std::string> invalid = invalid_inputs();
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
