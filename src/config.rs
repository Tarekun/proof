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
}
impl Default for Config {
    fn default() -> Self {
        Config {
            system: TypeSystem::Cic(),
        }
    }
}
impl Config {
    pub fn new(type_system: TypeSystem) -> Self {
        Config {
            system: type_system,
        }
    }
}

pub fn load_config(config_path: &str) -> Result<Config, String> {
    let mut config = Config::default();

    let config_content = read_file(config_path)
        .map_err(|e| format!("Failed to read config file: {}", e))?;
    let overrides: serde_yaml::Value = serde_yaml::from_str(&config_content)
        .map_err(|e| format!("Failed to parse config file: {}", e))?;

    // default config overriding
    if let Some(system) = overrides.get("system") {
        if let Some(system_str) = system.as_str() {
            if !system_str.is_empty() {
                config.system = map_type_system(system_str)?;
            }
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
