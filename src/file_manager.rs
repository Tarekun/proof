use std::fs;
use std::io;
use std::path::Path;

const SOURCE_FILE_EXTENSION: &str = ".lof";

pub fn read_file(filepath: &str) -> Result<String, io::Error> {
    if !filepath.ends_with(SOURCE_FILE_EXTENSION) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "Unprocessable file format. Expected a '{}' file extension",
                SOURCE_FILE_EXTENSION
            ),
        ));
    }

    fs::read_to_string(filepath)
}

pub fn list_sources(workspace: &str) -> Vec<String> {
    let path = Path::new(workspace);
    if !path.is_dir() {
        panic!(
            "Workspace path does not point to an existing directory: {}",
            workspace
        );
    }
    let entries = fs::read_dir(path).expect("Failed to read directory");

    // Filter files with .lof extension and collect their full paths
    let lof_files: Vec<String> = entries
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| {
            path.is_file()
                && path.extension().and_then(|ext| ext.to_str())
                    == Some(&SOURCE_FILE_EXTENSION[1..])
        })
        .map(|path| path.display().to_string())
        .collect();

    lof_files
}
