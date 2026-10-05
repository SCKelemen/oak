fn main() -> Result<(), Box<dyn std::error::Error>> {
    if std::env::args_os().len() != 1 {
        return Err("usage: oak-remap-model (writes validated JSON to stdout)".into());
    }
    let report = oak_remap_model::validation::verify_all()?;
    serde_json::to_writer_pretty(std::io::stdout().lock(), &report)?;
    println!();
    Ok(())
}
