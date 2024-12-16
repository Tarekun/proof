use std::fs;
use std::io;

const SOURCE_FILE_EXTENSION: &str = ".ns";

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
