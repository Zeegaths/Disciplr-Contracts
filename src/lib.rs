#![no_std]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, panic_with_error, token, Address, BytesN,
    Env, Symbol,
};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Contract-level errors returned via `panic_with_error!`.
#[contracterror]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    /// Requested vault does not exist in storage.
    VaultNotFound = 1,
    /// The vault is not in the required status for this operation.
    /// Used to prevent double-release and other invalid state transitions.
    InvalidStatus = 2,
    /// Caller is not permitted to perform this action (wrong auth or conditions not met).
    NotAuthorized = 3,
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// Status lifecycle for a `ProductivityVault`.
#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

/// Core vault record persisted in contract storage.
#[contracttype]
#[derive(Clone, Debug)]
pub struct ProductivityVault {
    /// Address that created (and funded) the vault.
    pub creator: Address,
    /// USDC amount locked in the vault (in stroops / smallest unit).
    pub amount: i128,
    /// Ledger timestamp when the commitment period starts.
    pub start_timestamp: u64,
    /// Ledger timestamp after which deadline-based release is allowed.
    pub end_timestamp: u64,
    /// Hash representing the milestone the creator commits to.
    pub milestone_hash: BytesN<32>,
    /// Optional designated verifier; if `None` any party may validate after deadline.
    pub verifier: Option<Address>,
    /// Funds go here on success.
    pub success_destination: Address,
    /// Funds go here on failure/redirect.
    pub failure_destination: Address,
    /// Current lifecycle status.
    pub status: VaultStatus,
    /// Set to `true` once the verifier (or authorised party) calls `validate_milestone`.
    /// Used by `release_funds` to allow early release before the deadline.
    pub milestone_validated: bool,
}

// ---------------------------------------------------------------------------
// Storage keys
// ---------------------------------------------------------------------------

#[contracttype]
pub enum DataKey {
    /// Monotonically increasing counter used to assign vault IDs.
    VaultCount,
    /// Per-vault storage keyed by numeric ID.
    Vault(u32),
}

// ---------------------------------------------------------------------------
// Contract
// ---------------------------------------------------------------------------

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    // -----------------------------------------------------------------------
    // create_vault
    // -----------------------------------------------------------------------

    /// Create a new productivity vault.
    ///
    /// The caller **must** have already approved a transfer of `amount` USDC
    /// tokens to this contract address before calling this function.
    /// The USDC pull is performed here via the token client.
    ///
    /// # Parameters
    /// - `usdc_token` – Address of the USDC token contract (SEP-41 compliant).
    /// - `creator`    – Address funding the vault (must sign).
    /// - `amount`     – USDC amount to lock (in token's smallest unit).
    ///
    /// # Returns
    /// The newly assigned `vault_id`.
    pub fn create_vault(
        env: Env,
        usdc_token: Address,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> u32 {
        creator.require_auth();

        // Pull USDC from creator into this contract.
        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(&creator, &env.current_contract_address(), &amount);

        // Allocate a new vault ID.
        let vault_id: u32 = env
            .storage()
            .instance()
            .get(&DataKey::VaultCount)
            .unwrap_or(0u32);

        let vault = ProductivityVault {
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
            milestone_validated: false,
        };

        // Persist vault and bump counter.
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);
        env.storage()
            .instance()
            .set(&DataKey::VaultCount, &(vault_id + 1));

        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault.clone(),
        );

        vault_id
    }

    // -----------------------------------------------------------------------
    // validate_milestone
    // -----------------------------------------------------------------------

    /// Mark the vault's milestone as validated.
    ///
    /// Only the designated verifier may call this (if one was set).
    /// Once validated the vault is eligible for early release via `release_funds`.
    ///
    /// # Returns
    /// `true` on success.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        let mut vault = Self::load_vault(&env, vault_id);

        // Vault must be Active.
        if vault.status != VaultStatus::Active {
            panic_with_error!(&env, Error::InvalidStatus);
        }

        // If a verifier is set, only they may validate.
        if let Some(ref v) = vault.verifier {
            v.require_auth();
        }

        vault.milestone_validated = true;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());

        true
    }

    // -----------------------------------------------------------------------
    // release_funds  ← CORE OF ISSUE #6
    // -----------------------------------------------------------------------

    /// Release vault funds to `success_destination`.
    ///
    /// **Release is permitted when either:**
    /// 1. The milestone has been validated via `validate_milestone`, **or**
    /// 2. The vault's `end_timestamp` has been reached (deadline-based release).
    ///
    /// This function is idempotent-safe: once a vault is `Completed` any
    /// subsequent call is rejected with `Error::InvalidStatus`, preventing
    /// double release.
    ///
    /// # Parameters
    /// - `vault_id`   – ID of the vault to release.
    /// - `usdc_token` – Address of the USDC token contract.
    ///
    /// # Returns
    /// `true` on successful release.
    ///
    /// # Errors
    /// - `Error::VaultNotFound`  – vault ID does not exist.
    /// - `Error::InvalidStatus`  – vault is not `Active` (already completed/failed/cancelled).
    /// - `Error::NotAuthorized`  – milestone not validated AND deadline not reached.
    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> bool {
        // 1. Load vault — panics VaultNotFound if absent.
        let mut vault = Self::load_vault(&env, vault_id);

        // 2. Require Active status — guard against double release.
        if vault.status != VaultStatus::Active {
            panic_with_error!(&env, Error::InvalidStatus);
        }

        // 3. Check release conditions.
        let now = env.ledger().timestamp();
        let deadline_reached = now >= vault.end_timestamp;
        let validated = vault.milestone_validated;

        if !validated && !deadline_reached {
            // Neither condition met — release not yet allowed.
            panic_with_error!(&env, Error::NotAuthorized);
        }

        // 4. Transfer USDC from this contract to success_destination.
        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.success_destination,
            &vault.amount,
        );

        // 5. Mark vault as Completed and persist.
        vault.status = VaultStatus::Completed;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        // 6. Emit event.
        env.events().publish(
            (Symbol::new(&env, "funds_released"), vault_id),
            vault.amount,
        );

        true
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

    /// Redirect funds to `failure_destination` (e.g. after deadline without validation).
    ///
    /// Release is permitted only if the vault is `Active` and past its `end_timestamp`
    /// without the milestone having been validated.
    ///
    /// # Parameters
    /// - `vault_id`   – ID of the vault to redirect.
    /// - `usdc_token` – Address of the USDC token contract.
    ///
    /// # Returns
    /// `true` on success.
    pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> bool {
        let mut vault = Self::load_vault(&env, vault_id);

        if vault.status != VaultStatus::Active {
            panic_with_error!(&env, Error::InvalidStatus);
        }

        let now = env.ledger().timestamp();
        if now < vault.end_timestamp {
            panic_with_error!(&env, Error::NotAuthorized);
        }

        // If milestone was validated the funds should go to success, not failure.
        if vault.milestone_validated {
            panic_with_error!(&env, Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.failure_destination,
            &vault.amount,
        );

        vault.status = VaultStatus::Failed;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        env.events().publish(
            (Symbol::new(&env, "funds_redirected"), vault_id),
            vault.amount,
        );

        true
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

    /// Cancel vault and return funds to creator.
    ///
    /// Only the creator can cancel, and only while the vault is `Active`.
    ///
    /// # Parameters
    /// - `vault_id`   – ID of the vault.
    /// - `usdc_token` – Address of the USDC token contract.
    pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> bool {
        let mut vault = Self::load_vault(&env, vault_id);

        vault.creator.require_auth();

        if vault.status != VaultStatus::Active {
            panic_with_error!(&env, Error::InvalidStatus);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.creator,
            &vault.amount,
        );

        vault.status = VaultStatus::Cancelled;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), ());

        true
    }

    // -----------------------------------------------------------------------
    // get_vault_state
    // -----------------------------------------------------------------------

    /// Return current vault state, or `None` if the vault does not exist.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    /// Load a vault from storage, panicking with `Error::VaultNotFound` if absent.
    fn load_vault(env: &Env, vault_id: u32) -> ProductivityVault {
        env.storage()
            .instance()
            .get(&DataKey::Vault(vault_id))
            .unwrap_or_else(|| panic_with_error!(env, Error::VaultNotFound))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, Ledger},
        token::{StellarAssetClient, TokenClient},
        Address, BytesN, Env,
    };

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    struct TestSetup {
        env: Env,
        contract_id: Address,
        usdc_token: Address,
        creator: Address,
        verifier: Address,
        success_dest: Address,
        failure_dest: Address,
        amount: i128,
        end_timestamp: u64,
    }

    impl TestSetup {
        fn new() -> Self {
            let env = Env::default();
            env.mock_all_auths();

            // Deploy USDC mock token.
            let usdc_admin = Address::generate(&env);
            let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
            let usdc_addr = usdc_token.address();
            let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

            // Actors.
            let creator = Address::generate(&env);
            let verifier = Address::generate(&env);
            let success_dest = Address::generate(&env);
            let failure_dest = Address::generate(&env);

            // Mint USDC to creator.
            let amount: i128 = 1_000_000; // 1 USDC (6 decimals)
            usdc_asset.mint(&creator, &amount);

            // Deploy contract.
            let contract_id = env.register(DisciplrVault, ());

            TestSetup {
                env,
                contract_id,
                usdc_token: usdc_addr,
                creator,
                verifier,
                success_dest,
                failure_dest,
                amount,
                end_timestamp: 1_000,
            }
        }

        fn client(&self) -> DisciplrVaultClient<'_> {
            DisciplrVaultClient::new(&self.env, &self.contract_id)
        }

        fn usdc_client(&self) -> TokenClient<'_> {
            TokenClient::new(&self.env, &self.usdc_token)
        }

        fn milestone_hash(&self) -> BytesN<32> {
            BytesN::from_array(&self.env, &[1u8; 32])
        }

        fn create_default_vault(&self) -> u32 {
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &self.amount,
                &0u64,
                &self.end_timestamp,
                &self.milestone_hash(),
                &Some(self.verifier.clone()),
                &self.success_dest,
                &self.failure_dest,
            )
        }
    }

    // -----------------------------------------------------------------------
    // create_vault / get_vault_state
    // -----------------------------------------------------------------------

    #[test]
    fn test_create_vault_and_get_state() {
        let setup = TestSetup::new();
        let client = setup.client();

        let vault_id = setup.create_default_vault();

        let vault = client
            .get_vault_state(&vault_id)
            .expect("vault should exist");

        assert_eq!(vault.status, VaultStatus::Active);
        assert_eq!(vault.amount, setup.amount);
        assert_eq!(vault.creator, setup.creator);
        assert!(!vault.milestone_validated);
    }

    #[test]
    fn test_create_vault_increments_id() {
        let setup = TestSetup::new();

        // Mint extra USDC for second vault.
        let usdc_asset = StellarAssetClient::new(&setup.env, &setup.usdc_token);
        usdc_asset.mint(&setup.creator, &setup.amount);

        let id_a = setup.create_default_vault();
        let id_b = setup.create_default_vault();
        assert_ne!(id_a, id_b, "vault IDs must be distinct");
        assert_eq!(id_b, id_a + 1);
    }

    // -----------------------------------------------------------------------
    // release_funds — happy paths
    // -----------------------------------------------------------------------

    /// Verifier validates milestone → release_funds succeeds before deadline.
    #[test]
    fn test_release_funds_after_validation() {
        let setup = TestSetup::new();
        let client = setup.client();

        // Set ledger time well BEFORE deadline.
        setup.env.ledger().set_timestamp(100);

        let vault_id = setup.create_default_vault();

        // Validate milestone.
        client.validate_milestone(&vault_id);

        // Record balances before release.
        let usdc = setup.usdc_client();
        let success_before = usdc.balance(&setup.success_dest);

        // Release.
        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        // Success destination received the funds.
        let success_after = usdc.balance(&setup.success_dest);
        assert_eq!(success_after - success_before, setup.amount);

        // Vault status is Completed.
        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// No validation, but deadline has passed → release_funds succeeds.
    #[test]
    fn test_release_funds_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(50); // before deadline for create
        let vault_id = setup.create_default_vault();

        // Advance ledger PAST end_timestamp.
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.success_dest);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        assert_eq!(usdc.balance(&setup.success_dest) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    // -----------------------------------------------------------------------
    // release_funds — error paths
    // -----------------------------------------------------------------------

    /// A second call to release_funds on an already-Completed vault must fail.
    #[test]
    #[should_panic(expected = "Error(Contract, #2)")]
    fn test_double_release_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        let vault_id = setup.create_default_vault();

        client.release_funds(&vault_id, &setup.usdc_token);
        // Second call — must panic.
        client.release_funds(&vault_id, &setup.usdc_token);
    }

    /// release_funds on a Cancelled vault must fail.
    #[test]
    #[should_panic(expected = "Error(Contract, #2)")]
    fn test_release_cancelled_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(50);
        let vault_id = setup.create_default_vault();

        client.cancel_vault(&vault_id, &setup.usdc_token);
        // Release after cancel — must panic.
        client.release_funds(&vault_id, &setup.usdc_token);
    }

    /// release_funds before deadline and without validation must fail.
    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_release_not_validated_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(50); // before deadline
        let vault_id = setup.create_default_vault();

        // Neither validated nor past deadline — must panic.
        client.release_funds(&vault_id, &setup.usdc_token);
    }

    // -----------------------------------------------------------------------
    // validate_milestone
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_milestone_sets_flag() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(50);
        let vault_id = setup.create_default_vault();

        client.validate_milestone(&vault_id);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(vault.milestone_validated);
        assert_eq!(
            vault.status,
            VaultStatus::Active,
            "status should still be Active after validation"
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #2)")]
    fn test_validate_milestone_on_completed_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        let vault_id = setup.create_default_vault();
        client.release_funds(&vault_id, &setup.usdc_token);

        // Validate after completion — must panic.
        client.validate_milestone(&vault_id);
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

    #[test]
    fn test_redirect_funds_after_deadline_without_validation() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(50);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.failure_dest);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.failure_dest) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Failed);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_redirect_funds_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(50);
        let vault_id = setup.create_default_vault();

        // Still before deadline — must panic.
        client.redirect_funds(&vault_id, &setup.usdc_token);
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

    #[test]
    fn test_cancel_vault_returns_funds_to_creator() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(50);
        let vault_id = setup.create_default_vault();

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.creator);

        let result = client.cancel_vault(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.creator) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Cancelled);
    }

    // -----------------------------------------------------------------------
    // get_vault_state
    // -----------------------------------------------------------------------

    #[test]
    fn test_get_vault_state_nonexistent_returns_none() {
        let setup = TestSetup::new();
        let client = setup.client();
        assert!(client.get_vault_state(&999u32).is_none());
    }
}
