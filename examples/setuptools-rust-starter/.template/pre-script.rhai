variable::set("PYO3_VERSION", "0.18.0");
file::rename(".template/Cargo.toml", "Cargo.toml");
file::rename(".template/setup.cfg", "setup.cfg");
file::rename(".template/tox.ini", "tox.ini");
file::delete(".template");
