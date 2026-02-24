## PR: Add USDC balance invariants for release and redirect

### Summary
- Add tests to verify USDC balances after `release_funds` and `redirect_funds`.
- Ensure contract balance decreases while success/failure destination balances increase by the vault amount.
- Update test documentation to reflect ≥95% effective coverage and new security invariants.

### Testing
- `cargo test` (all 39 tests passing)

