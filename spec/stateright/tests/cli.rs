use std::process::Command;

#[test]
fn unknown_options_cannot_emit_a_successful_report() {
    let output = Command::new(env!("CARGO_BIN_EXE_oak-remap-model"))
        .arg("--timeout=1")
        .output()
        .expect("run the model-checking CLI");
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("usage: oak-remap-model"));
}
