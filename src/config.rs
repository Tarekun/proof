use crate::file_manager::read_file;

#[derive(Debug, PartialEq, Clone)]
pub enum TypeSystem {
    Cic(),
    Fol(),
}

pub fn id_to_system(system_id: &str) -> Result<TypeSystem, String> {
    match system_id {
        "cic" => Ok(TypeSystem::Cic()),
        "fol" => Ok(TypeSystem::Fol()),
        other => Err(format!("Unsupported type system id provided: {}", other)),
    }
}

#[derive(Debug, Clone)]
pub struct Config {
    pub system: TypeSystem,
    pub log_level: tracing::Level,
}
impl Default for Config {
    fn default() -> Self {
        Config {
            system: TypeSystem::Cic(),
            log_level: tracing::Level::INFO,
        }
    }
}
impl Config {
    pub fn new(type_system: TypeSystem) -> Self {
        Config {
            system: type_system,
            log_level: tracing::Level::INFO,
        }
    }
}

/// Loads configuration from a YAML file.
/// If left unspecified config defaults are
/// `system`: cic
/// `log_level`: INFO
pub fn load_config(config_path: &str) -> Result<Config, String> {
    let mut config = Config::default();

    let config_content = read_file(config_path)
        .map_err(|e| format!("Failed to read config file: {}", e))?;
    let overrides: serde_yaml::Value = serde_yaml::from_str(&config_content)
        .map_err(|e| format!("Failed to parse config file: {}", e))?;

    // Override type system if specified
    if let Some(system) = overrides.get("system") {
        if let Some(system_str) = system.as_str() {
            if !system_str.is_empty() {
                config.system = map_type_system(system_str)?;
            }
        }
    }

    // Override log level if specified
    if let Some(log_level) = overrides.get("log_level") {
        if let Some(level_str) = log_level.as_str() {
            config.log_level = map_log_level(level_str)?;
        }
    }

    Ok(config)
}

fn map_type_system(system: &str) -> Result<TypeSystem, String> {
    match system {
        "cic" => Ok(TypeSystem::Cic()),
        "fol" => Ok(TypeSystem::Fol()),
        _ => Err(format!("Unsupported type system {}", system)),
    }
}

fn map_log_level(log_level: &str) -> Result<tracing::Level, String> {
    match log_level.to_lowercase().as_str() {
        "info" => Ok(tracing::Level::INFO),
        "error" => Ok(tracing::Level::ERROR),
        "debug" => Ok(tracing::Level::DEBUG),
        "trace" => Ok(tracing::Level::TRACE),
        "warn" => Ok(tracing::Level::WARN),
        _ => return Err(format!(
            "Invalid log level: {}. Must be one of: info, error, debug, trace, warn",
            log_level
        )),
    }
}
