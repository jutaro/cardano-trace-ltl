Idris2 port of cardano-trace-ltl

Notes
- Trace messages are modeled in `Cardano.Logging.Types.TraceMessage` with a minimal decoder for JSON lines containing `"at"`, `"ns"`, and `"data"` fields.
- The decoder accepts ISO8601 timestamps (e.g. `2025-12-01T07:06:43.917452Z`) or numeric microseconds for `at`.
- JSON parsing is intentionally lightweight; `tmsgData` is preserved as a raw JSON object string and demo code extracts fields via simple string scanning.
- Temporal grouping uses microsecond timestamps directly; if your logs encode time differently, adjust `parseTimestamp` in `Cardano.Logging.Types.TraceMessage`.
