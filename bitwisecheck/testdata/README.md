# Installation controls

The four `.fixture` files are one exact current-production AND bundle generated
from semantic baseline commit `698f6a7b013df508a831d391fe425f4f27cf4581` using the
public compiler APIs on 2026-10-19. Source is `bitwise: (x: u32, y: u32): u32 = x & y`
followed by LF. Sizes: source 39, Wasm 45, AArch64 ELF 688, RV64 ELF 720 bytes.

These are embedded installation self-test inputs. They are freshly proved and
audited on every Install; they cannot grant authority as cached receipts. The
negative installation control changes AND to OR while keeping all artifacts,
and requires a successful kernel proof that the tuple is refused.
