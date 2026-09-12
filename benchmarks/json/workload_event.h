// The large-document workload: an event record about 1.5 KB long — two
// borrowed strings (a short kind, a message of a few hundred bytes with an
// occasional escape), sixty-four unsigned latencies and eight signed deltas,
// fields in two orders, whitespace in half the documents. Both decoders
// hand the strings out as raw tokens (quotes included, not unescaped) and
// materialize the arrays; every field is required, duplicates and unknown
// keys rejected, integer ranges checked, trailing content rejected.
#include "bridge_event.h"
typedef EventOutput BenchOutput;

__attribute__((noinline)) bool simd_decode(simdjson::ondemand::parser &parser,
    const simdjson::padded_string &input, BenchOutput &out) {
  try {
    simdjson::ondemand::document doc = parser.iterate(input);
    unsigned seen = 0;
    for (auto field : doc.get_object()) {
      std::string_view key = field.unescaped_key();
      unsigned bit = key == "id" ? 1 : key == "kind" ? 2 : key == "message" ? 4 : key == "latencies" ? 8 : key == "deltas" ? 16 : 0;
      if (!bit || (seen & bit)) return false;
      seen |= bit;
      auto value = field.value();
      if (bit == 1) {
        std::string_view raw = value.raw_json_token();
        if (raw.empty() || raw.front() == '-') return false;
        out.id = uint64_t(value.get_uint64());
      } else if (bit == 2 || bit == 4) {
        if (value.type() != simdjson::ondemand::json_type::string) return false;
        std::string_view raw = value.raw_json_token();
        while (!raw.empty() && (raw.back() == ' ' || raw.back() == '\n' || raw.back() == '\t' || raw.back() == '\r')) raw.remove_suffix(1);
        // Consume the string so the iterator advances and escapes are validated.
        std::string_view text = value.get_string();
        (void)text;
        uint32_t offset = uint32_t(raw.data() - input.data()), length = uint32_t(raw.size());
        if (bit == 2) { out.kind_offset = offset; out.kind_length = length; }
        else { out.message_offset = offset; out.message_length = length; }
      } else if (bit == 8) {
        unsigned count = 0;
        for (auto item : value.get_array()) {
          if (count == 64) return false;
          std::string_view raw = item.raw_json_token();
          if (raw.empty() || raw.front() == '-') return false;
          uint64_t n = item.get_uint64();
          if (n > UINT32_MAX) return false;
          out.latencies[count++] = uint32_t(n);
        }
        if (count != 64) return false;
      } else {
        unsigned count = 0;
        for (auto item : value.get_array()) {
          if (count == 8) return false;
          int64_t n = item.get_int64();
          if (n < INT32_MIN || n > INT32_MAX) return false;
          out.deltas[count++] = int32_t(n);
        }
        if (count != 8) return false;
      }
    }
    return seen == 31 && doc.at_end();
  } catch (const simdjson::simdjson_error &) {
    return false;
  }
}

bool equal(const BenchOutput &a, const BenchOutput &b) {
  if (a.id != b.id || a.kind_offset != b.kind_offset || a.kind_length != b.kind_length ||
      a.message_offset != b.message_offset || a.message_length != b.message_length) return false;
  for (unsigned i = 0; i < 64; ++i) if (a.latencies[i] != b.latencies[i]) return false;
  for (unsigned i = 0; i < 8; ++i) if (a.deltas[i] != b.deltas[i]) return false;
  return true;
}

uint64_t digest(const BenchOutput &value) {
  uint64_t hash = value.id ^ (uint64_t(value.kind_offset) << 32) ^ value.kind_length ^ (uint64_t(value.message_offset) << 16) ^ value.message_length;
  for (uint32_t n : value.latencies) hash = (hash ^ n) * UINT64_C(1099511628211);
  for (int32_t n : value.deltas) hash = (hash ^ uint32_t(n)) * UINT64_C(1099511628211);
  return hash;
}

struct Fixture {
  simdjson::padded_string input;
  BenchOutput expected;
};

static const char *const kinds[] = {"click", "view", "purchase", "signup", "error"};
static const char *const words[] = {"request", "latency", "budget", "exceeded", "on", "the", "checkout", "path", "after", "retry",
  "storage", "engine", "compaction", "finished", "with", "pages", "written", "and", "index", "rebuilt", "user", "session",
  "renewed", "token", "rotated", "cache", "warm", "region", "failover", "completed"};

std::vector<Fixture> corpus(size_t count) {
  std::vector<Fixture> fixtures;
  fixtures.reserve(count);
  for (size_t i = 0; i < count; ++i) {
    BenchOutput expected{};
    expected.id = i % 5 == 0 ? UINT64_MAX : uint64_t(i) * 2862933555777941757ULL;
    std::string kind = std::string("\"") + kinds[i % 5] + "\"";
    std::string message = "\"";
    size_t length = 24 + (i * 7) % 40;
    for (size_t w = 0; w < length; ++w) {
      if (w) message += ' ';
      message += words[(i + w * 3) % 30];
      if (i % 8 == 0 && w == length / 2) message += "\\\"quoted\\\" \\n";
    }
    message += "\"";
    std::string latencies = "[";
    for (unsigned k = 0; k < 64; ++k) {
      expected.latencies[k] = k == 63 ? UINT32_MAX : uint32_t((i * 131 + k * 7919) % 1000000);
      if (k) latencies += ",";
      latencies += std::to_string(expected.latencies[k]);
    }
    latencies += "]";
    std::string deltas = "[";
    for (unsigned k = 0; k < 8; ++k) {
      expected.deltas[k] = k == 0 ? INT32_MIN : k == 7 ? INT32_MAX : int32_t(i % 1000) * (k % 2 ? 1 : -1) * int32_t(k);
      if (k) deltas += ",";
      deltas += std::to_string(expected.deltas[k]);
    }
    deltas += "]";
    std::string text;
    if (i % 2) {
      text = "{\"id\":" + std::to_string(expected.id) + ",\"kind\":" + kind + ",\"message\":" + message +
        ",\"latencies\":" + latencies + ",\"deltas\":" + deltas + "}";
    } else {
      text = "{ \"message\": " + message + ", \"latencies\": " + latencies + ", \"kind\": " + kind +
        ", \"deltas\": " + deltas + ", \"id\": " + std::to_string(expected.id) + " }";
    }
    expected.kind_offset = uint32_t(text.find(kind)); expected.kind_length = uint32_t(kind.size());
    expected.message_offset = uint32_t(text.find(message)); expected.message_length = uint32_t(message.size());
    fixtures.push_back({simdjson::padded_string(text), expected});
  }
  return fixtures;
}

std::vector<std::string> invalid_inputs() {
  std::vector<std::string> invalid = {
    "{\"id\":1,\"\\u0069d\":2}", "{\"unknown\":0}", "{\"kind\":1}", "{\"id\":-1}", "{\"id\":1.0}",
    "{\"id\":1,\"kind\":\"a\",\"message\":\"m\",\"latencies\":[1],\"deltas\":[1,2,3,4,5,6,7,8]}",
    "{\"id\":1,\"kind\":\"a\",\"message\":\"m\\x\",\"latencies\":[],\"deltas\":[]}",
    "{\"id\":1,\"kind\":\"a\",\"message\":\"m\",\"latencies\":[4294967296],\"deltas\":[1,2,3,4,5,6,7,8]}",
  };
  return invalid;
}
