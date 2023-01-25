#!/bin/bash
cargo fmt --check &&
cargo clippy --workspace --all-targets -- -D warnings -A clippy::new_without_default -W clippy::implicit_saturating_sub -W clippy::implicit_clone -W clippy::map_unwrap_or -W clippy::unnested_or_patterns -W clippy::manual_assert -W clippy::unused_async -W clippy::mut_mut &&
cargo clippy --workspace --lib --bins --examples -- -A clippy::all -W clippy::unwrap_used -W clippy::dbg_macro -W clippy::items_after_statements -W clippy::fallible_impl_from -W clippy::string_slice
