#![no_std]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{contract, contractimpl, contracttype, Address, BytesN, Env, Symbol};

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
pub struct ProductivityVault {
    pub creator: Address,
    pub amount: i128,
    pub start_timestamp: u64,
    pub end_timestamp: u64,
    pub milestone_hash: BytesN<32>,
    pub verifier: Option<Address>,
    pub success_destination: Address,
    pub failure_destination: Address,
    pub status: VaultStatus,
}

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    pub fn create_vault(
        env: Env,
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
        // TODO: pull USDC from creator to this contract
        // For now, just store vault metadata (storage key pattern would be used in full impl)
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
        };
        let vault_id = 0u32; // placeholder; real impl would allocate id and persist
        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault);
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        true
    }

    /// Release funds to success destination (called after validation or by deadline logic).
    pub fn release_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active, transfer to success_destination, set Completed
        true
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active and past end_timestamp, transfer to failure_destination, set Failed
        true
    }

    /// Cancel vault and return funds to creator (if allowed by rules).
    pub fn cancel_vault(_env: Env, _vault_id: u32) -> bool {
        // TODO: require creator auth, return USDC to creator, set Cancelled
        true
    }

    /// Return current vault state for a given vault id.
    /// Placeholder: returns None; full impl would read from storage.
    pub fn get_vault_state(_env: Env, _vault_id: u32) -> Option<ProductivityVault> {
        None
    }

    // ===== USDC Balance Tests: cancel_vault =====

    /// Tests that after cancel_vault, the creator's USDC balance is fully restored
    /// by exactly the vault amount, and the contract's balance decreases by the same.
    #[test]
    fn test_usdc_balance_updates_after_cancel_vault() {
        let setup = TestSetup::new();
        let client = setup.client();
        let usdc = setup.usdc_client();

        let before_create = usdc.balance(&setup.creator);
        let vault_id = setup.create_default_vault();

        assert_eq!(
            usdc.balance(&setup.creator),
            before_create - setup.amount,
            "Creator balance should decrease by amount after creation"
        );

        client.cancel_vault(&vault_id, &setup.usdc_token);

        assert_eq!(
            usdc.balance(&setup.creator),
            before_create,
            "Creator balance should be fully restored after cancellation"
        );
        assert_eq!(
            usdc.balance(&setup.contract_id),
            0,
            "Contract balance should be zero after cancellation"
        );
    }

    /// Tests cancel_vault when the creator has exactly the vault amount.
    /// Guards against rounding errors and ensures full balance restoration.
    #[test]
    fn test_cancel_vault_exact_balance_no_remainder() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let usdc_admin = Address::generate(&env);
        let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
        let usdc_addr = usdc_token.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);
        let usdc_client = TokenClient::new(&env, &usdc_addr);

        let creator = Address::generate(&env);
        let amount = 1_000_000i128;

        // Mint EXACTLY vault_amount to creator
        usdc_asset.mint(&creator, &amount);
        assert_eq!(usdc_client.balance(&creator), amount);

        let vault_id = client.create_vault(
            &usdc_addr,
            &creator,
            &amount,
            &100,
            &200,
            &BytesN::from_array(&env, &[1u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        assert_eq!(usdc_client.balance(&creator), 0);

        client.cancel_vault(&vault_id, &usdc_addr);

        assert_eq!(usdc_client.balance(&creator), amount);
        assert_eq!(usdc_client.balance(&contract_id), 0);
    }
}
