// The machines jihoo compiles for.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    X86_64,
    Aarch64,
}

impl Target {
    pub fn host() -> Target {
        if cfg!(target_arch = "aarch64") {
            Target::Aarch64
        } else {
            Target::X86_64
        }
    }

    pub fn parse(s: &str) -> Option<Target> {
        match s {
            "x86_64" | "x86_64-linux" => Some(Target::X86_64),
            "aarch64" | "aarch64-linux" | "arm64" => Some(Target::Aarch64),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Target::X86_64 => "x86_64",
            Target::Aarch64 => "aarch64",
        }
    }

    pub fn triple(self) -> &'static str {
        match self {
            Target::X86_64 => "x86_64-unknown-linux-gnu",
            Target::Aarch64 => "aarch64-unknown-linux-gnu",
        }
    }
}
