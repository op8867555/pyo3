//! Runtime inspection of Python data structures.
//! This module provides APIs to access information on Python data structures (classes, builtins) at runtime from Rust.
//! These APIs can be used to generate documentation, interface files (.pyi), etc.
//!
//! Tracking issue: <https://github.com/PyO3/pyo3/issues/2454>.

pub mod types;
pub mod fields;
pub mod classes;
pub mod modules;
pub mod interface;
