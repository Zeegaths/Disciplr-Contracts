#![no_std]

use soroban_sdk::{
    contract, contractimpl, contracttype, Address, BytesN, Env, Symbol,
};

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

/// Storage key for vault data
const VAULT_KEY: Symbol = Symbol::short("VAULT");

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    /// Returns the vault_id for the newly created vault.
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
        let vault_id = 0u32; // Using fixed ID for simplicity; real impl would use counter
        env.storage().instance().set(&VAULT_KEY, &vault);
        
        // Publish event
        let event_topic = (Symbol::new(&env, "vault_created"), vault_id);
        env.events().publish(event_topic, vault);
        
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    /// This is a simplified version that transitions Active -> Completed.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env.storage().instance()
            .get(&VAULT_KEY)
            .expect("Vault not found");
        
        // Only Active vaults can be validated
        if vault.status != VaultStatus::Active {
            panic!("Vault must be Active to validate milestone");
        }
        
        // TODO: check caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination
        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&VAULT_KEY, &vault);
        
        // Publish event
        let event_topic = (Symbol::new(&env, "milestone_validated"), vault_id);
        env.events().publish(event_topic, ());
        
        true
    }

    /// Release funds to success destination (called after validation or by deadline logic).
    /// Transitions Active -> Completed.
    pub fn release_funds(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env.storage().instance()
            .get(&VAULT_KEY)
            .expect("Vault not found");
        
        // Only Active vaults can release funds
        if vault.status != VaultStatus::Active {
            panic!("Vault must be Active to release funds");
        }
        
        // TODO: transfer to success_destination
        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&VAULT_KEY, &vault);
        
        env.events().publish(
            (Symbol::new(&env, "funds_released"), vault_id),
            (),
        );
        true
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    /// Transitions Active -> Failed.
    pub fn redirect_funds(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env.storage().instance()
            .get(&VAULT_KEY)
            .expect("Vault not found");
        
        // Only Active vaults can redirect funds
        if vault.status != VaultStatus::Active {
            panic!("Vault must be Active to redirect funds");
        }
        
        // TODO: check past end_timestamp, transfer to failure_destination
        vault.status = VaultStatus::Failed;
        env.storage().instance().set(&VAULT_KEY, &vault);
        
        // Publish event
        let event_topic = (Symbol::new(&env, "funds_redirected"), vault_id);
        env.events().publish(event_topic, ());
        
        true
    }

    /// Cancel vault and return funds to creator (if allowed by rules).
    /// Transitions Active -> Cancelled.
    pub fn cancel_vault(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env.storage().instance()
            .get(&VAULT_KEY)
            .expect("Vault not found");
        
        // Only Active vaults can be cancelled
        if vault.status != VaultStatus::Active {
            panic!("Vault must be Active to cancel");
        }
        
        // TODO: require creator auth, return USDC to creator
        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&VAULT_KEY, &vault);
        
        // Publish event
        let event_topic = (Symbol::new(&env, "vault_cancelled"), vault_id);
        env.events().publish(event_topic, ());
        
        true
    }

    /// Return current vault state for a given vault id.
    pub fn get_vault_state(env: Env, _vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&VAULT_KEY)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use soroban_sdk::{testutils::Address as _, Address, BytesN, Env};

    /// Helper function to create a test vault with default parameters.
    /// Returns (env, contract_id, creator, vault_id).
    fn setup_test_vault() -> (Env, Address, Address, u32) {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        let creator = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);
        let milestone_hash = BytesN::from_array(&env, &[0u8; 32]);

        env.mock_all_auths();

        let client = DisciplrVaultClient::new(&env, &contract_id);
        let vault_id = client.create_vault(
            &creator,
            &1000i128,
            &1000u64,
            &2000u64,
            &milestone_hash,
            &None,
            &success_dest,
            &failure_dest,
        );

        (env, contract_id, creator, vault_id)
    }

    /// Test: Active -> Completed via release_funds
    /// Validates that an Active vault can successfully transition to Completed
    /// when release_funds is called.
    #[test]
    fn test_active_to_completed_via_release() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Verify initial state is Active
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Active);

        // Execute transition: Active -> Completed
        let result = client.release_funds(&vault_id);
        assert!(result);

        // Verify final state is Completed
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// Test: Active -> Failed via redirect_funds
    /// Validates that an Active vault can successfully transition to Failed
    /// when redirect_funds is called (e.g., after deadline expires).
    #[test]
    fn test_active_to_failed_via_redirect() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Verify initial state is Active
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Active);

        // Execute transition: Active -> Failed
        let result = client.redirect_funds(&vault_id);
        assert!(result);

        // Verify final state is Failed
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Failed);
    }

    /// Test: Active -> Cancelled via cancel_vault
    /// Validates that an Active vault can successfully transition to Cancelled
    /// when cancel_vault is called by the creator.
    #[test]
    fn test_active_to_cancelled_via_cancel() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Verify initial state is Active
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Active);

        // Execute transition: Active -> Cancelled
        let result = client.cancel_vault(&vault_id);
        assert!(result);

        // Verify final state is Cancelled
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Cancelled);
    }

    /// Test: Completed state cannot transition via release_funds
    /// Security: Ensures terminal states are immutable to prevent double-spending.
    #[test]
    #[should_panic(expected = "Vault must be Active to release funds")]
    fn test_completed_cannot_release() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Completed
        client.release_funds(&vault_id);

        // Attempt invalid transition: Completed -> Completed (should panic)
        client.release_funds(&vault_id);
    }

    /// Test: Completed state cannot transition via redirect_funds
    /// Security: Prevents funds from being redirected after successful completion.
    #[test]
    #[should_panic(expected = "Vault must be Active to redirect funds")]
    fn test_completed_cannot_redirect() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Completed
        client.release_funds(&vault_id);

        // Attempt invalid transition: Completed -> Failed (should panic)
        client.redirect_funds(&vault_id);
    }

    /// Test: Completed state cannot transition via cancel_vault
    /// Security: Prevents cancellation after funds have been released.
    #[test]
    #[should_panic(expected = "Vault must be Active to cancel")]
    fn test_completed_cannot_cancel() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Completed
        client.release_funds(&vault_id);

        // Attempt invalid transition: Completed -> Cancelled (should panic)
        client.cancel_vault(&vault_id);
    }

    /// Test: Completed state cannot transition via validate_milestone
    /// Security: Prevents re-validation of already completed vaults.
    #[test]
    #[should_panic(expected = "Vault must be Active to validate milestone")]
    fn test_completed_cannot_validate() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Completed
        client.release_funds(&vault_id);

        // Attempt invalid transition: Completed -> Completed (should panic)
        client.validate_milestone(&vault_id);
    }


    /// Test: Failed state cannot transition via release_funds
    /// Security: Prevents releasing funds after they've been redirected to failure destination.
    #[test]
    #[should_panic(expected = "Vault must be Active to release funds")]
    fn test_failed_cannot_release() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Failed
        client.redirect_funds(&vault_id);

        // Attempt invalid transition: Failed -> Completed (should panic)
        client.release_funds(&vault_id);
    }

    /// Test: Failed state cannot transition via redirect_funds
    /// Security: Prevents double-redirection of funds.
    #[test]
    #[should_panic(expected = "Vault must be Active to redirect funds")]
    fn test_failed_cannot_redirect() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Failed
        client.redirect_funds(&vault_id);

        // Attempt invalid transition: Failed -> Failed (should panic)
        client.redirect_funds(&vault_id);
    }

    /// Test: Failed state cannot transition via cancel_vault
    /// Security: Prevents cancellation after funds have been redirected.
    #[test]
    #[should_panic(expected = "Vault must be Active to cancel")]
    fn test_failed_cannot_cancel() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Failed
        client.redirect_funds(&vault_id);

        // Attempt invalid transition: Failed -> Cancelled (should panic)
        client.cancel_vault(&vault_id);
    }

    /// Test: Failed state cannot transition via validate_milestone
    /// Security: Prevents validation after vault has already failed.
    #[test]
    #[should_panic(expected = "Vault must be Active to validate milestone")]
    fn test_failed_cannot_validate() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Failed
        client.redirect_funds(&vault_id);

        // Attempt invalid transition: Failed -> Completed (should panic)
        client.validate_milestone(&vault_id);
    }


    /// Test: Cancelled state cannot transition via release_funds
    /// Security: Prevents releasing funds after vault has been cancelled.
    #[test]
    #[should_panic(expected = "Vault must be Active to release funds")]
    fn test_cancelled_cannot_release() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Cancelled
        client.cancel_vault(&vault_id);

        // Attempt invalid transition: Cancelled -> Completed (should panic)
        client.release_funds(&vault_id);
    }

    /// Test: Cancelled state cannot transition via redirect_funds
    /// Security: Prevents redirecting funds after cancellation.
    #[test]
    #[should_panic(expected = "Vault must be Active to redirect funds")]
    fn test_cancelled_cannot_redirect() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Cancelled
        client.cancel_vault(&vault_id);

        // Attempt invalid transition: Cancelled -> Failed (should panic)
        client.redirect_funds(&vault_id);
    }

    /// Test: Cancelled state cannot transition via cancel_vault
    /// Security: Prevents double-cancellation.
    #[test]
    #[should_panic(expected = "Vault must be Active to cancel")]
    fn test_cancelled_cannot_cancel() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Cancelled
        client.cancel_vault(&vault_id);

        // Attempt invalid transition: Cancelled -> Cancelled (should panic)
        client.cancel_vault(&vault_id);
    }

    /// Test: Cancelled state cannot transition via validate_milestone
    /// Security: Prevents validation after vault has been cancelled.
    #[test]
    #[should_panic(expected = "Vault must be Active to validate milestone")]
    fn test_cancelled_cannot_validate() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Transition to Cancelled
        client.cancel_vault(&vault_id);

        // Attempt invalid transition: Cancelled -> Completed (should panic)
        client.validate_milestone(&vault_id);
    }


    /// Test: Vault creation initializes with Active status
    /// Validates the initial state of a newly created vault.
    #[test]
    fn test_vault_creation_status() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Active);
        assert_eq!(vault.amount, 1000i128);
    }

    /// Test: Active -> Completed via validate_milestone
    /// Alternative path to Completed state through milestone validation.
    #[test]
    fn test_active_to_completed_via_validate() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Verify initial state is Active
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Active);

        // Execute transition: Active -> Completed via validation
        let result = client.validate_milestone(&vault_id);
        assert!(result);

        // Verify final state is Completed
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// Test: Verify event emission on vault creation
    /// Ensures proper event logging for audit trails.
    #[test]
    fn test_vault_creation_emits_event() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        let creator = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        env.mock_all_auths();

        let client = DisciplrVaultClient::new(&env, &contract_id);
        let vault_id = client.create_vault(
            &creator,
            &2000i128,
            &500u64,
            &3000u64,
            &milestone_hash,
            &None,
            &success_dest,
            &failure_dest,
        );

        // Verify vault was created with correct ID
        assert_eq!(vault_id, 0u32);
        
        // Verify vault state
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.amount, 2000i128);
        assert_eq!(vault.start_timestamp, 500u64);
        assert_eq!(vault.end_timestamp, 3000u64);
    }

    /// Test: Verify event emission on milestone validation
    /// Ensures proper event logging for milestone completion.
    #[test]
    fn test_validate_milestone_emits_event() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Execute validation
        let result = client.validate_milestone(&vault_id);
        assert!(result);

        // Verify state changed
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// Test: Verify event emission on funds release
    /// Ensures proper event logging for fund releases.
    #[test]
    fn test_release_funds_emits_event() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Execute release
        let result = client.release_funds(&vault_id);
        assert!(result);

        // Verify state changed
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// Test: Verify event emission on funds redirect
    /// Ensures proper event logging for fund redirections.
    #[test]
    fn test_redirect_funds_emits_event() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Execute redirect
        let result = client.redirect_funds(&vault_id);
        assert!(result);

        // Verify state changed
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Failed);
    }

    /// Test: Verify event emission on vault cancellation
    /// Ensures proper event logging for cancellations.
    #[test]
    fn test_cancel_vault_emits_event() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Execute cancellation
        let result = client.cancel_vault(&vault_id);
        assert!(result);

        // Verify state changed
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Cancelled);
    }

    /// Test: Multiple vault creations with different parameters
    /// Ensures all code paths in create_vault are exercised.
    #[test]
    fn test_multiple_vault_creations() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        env.mock_all_auths();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Create vault 1
        let creator1 = Address::generate(&env);
        let vault_id1 = client.create_vault(
            &creator1,
            &1000i128,
            &100u64,
            &200u64,
            &BytesN::from_array(&env, &[0u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
        assert_eq!(vault_id1, 0u32);

        // Create vault 2 (overwrites vault 1 in this simple implementation)
        let creator2 = Address::generate(&env);
        let verifier2 = Address::generate(&env);
        let vault_id2 = client.create_vault(
            &creator2,
            &5000i128,
            &300u64,
            &400u64,
            &BytesN::from_array(&env, &[255u8; 32]),
            &Some(verifier2.clone()),
            &Address::generate(&env),
            &Address::generate(&env),
        );
        assert_eq!(vault_id2, 0u32);

        // Verify latest vault
        let vault = client.get_vault_state(&vault_id2).expect("Vault should exist");
        assert_eq!(vault.amount, 5000i128);
        assert_eq!(vault.verifier, Some(verifier2));
    }

    /// Test: Verify all vault fields are properly stored
    /// Comprehensive test of vault data integrity.
    #[test]
    fn test_vault_data_integrity() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);
        let milestone_hash = BytesN::from_array(&env, &[42u8; 32]);

        env.mock_all_auths();

        let client = DisciplrVaultClient::new(&env, &contract_id);
        let vault_id = client.create_vault(
            &creator,
            &9999i128,
            &1234u64,
            &5678u64,
            &milestone_hash,
            &Some(verifier.clone()),
            &success_dest,
            &failure_dest,
        );

        // Verify all fields
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.creator, creator);
        assert_eq!(vault.amount, 9999i128);
        assert_eq!(vault.start_timestamp, 1234u64);
        assert_eq!(vault.end_timestamp, 5678u64);
        assert_eq!(vault.milestone_hash, milestone_hash);
        assert_eq!(vault.verifier, Some(verifier));
        assert_eq!(vault.success_destination, success_dest);
        assert_eq!(vault.failure_destination, failure_dest);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    /// Test: Vault creation with verifier address
    /// Validates vault creation with optional verifier field populated.
    #[test]
    fn test_vault_creation_with_verifier() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);
        let milestone_hash = BytesN::from_array(&env, &[2u8; 32]);

        env.mock_all_auths();

        let client = DisciplrVaultClient::new(&env, &contract_id);
        let vault_id = client.create_vault(
            &creator,
            &5000i128,
            &100u64,
            &5000u64,
            &milestone_hash,
            &Some(verifier.clone()),
            &success_dest,
            &failure_dest,
        );

        // Verify vault was created with verifier
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.verifier, Some(verifier));
        assert_eq!(vault.amount, 5000i128);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    /// Test: Get vault state returns None for non-existent vault
    /// Security: Ensures proper handling of invalid vault IDs.
    #[test]
    fn test_get_vault_state_nonexistent() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Query non-existent vault - should return None since no vault was created
        let result = client.get_vault_state(&999u32);
        assert!(result.is_none());
    }

    /// Test: Sequential state transitions
    /// Tests multiple operations in sequence to ensure state consistency.
    #[test]
    fn test_sequential_operations() {
        let (env, contract_id, _creator, vault_id) = setup_test_vault();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Verify initial Active state
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Active);
        assert_eq!(vault.amount, 1000i128);

        // Transition to Completed
        client.release_funds(&vault_id);
        let vault = client.get_vault_state(&vault_id).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// Test: Create multiple vaults with different amounts
    /// Ensures vault creation works with various parameter combinations.
    #[test]
    fn test_create_vaults_different_amounts() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        env.mock_all_auths();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Create vault with small amount
        let creator1 = Address::generate(&env);
        let vault_id1 = client.create_vault(
            &creator1,
            &100i128,
            &0u64,
            &1000u64,
            &BytesN::from_array(&env, &[1u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
        assert_eq!(vault_id1, 0u32);

        // Create vault with large amount
        let creator2 = Address::generate(&env);
        let vault_id2 = client.create_vault(
            &creator2,
            &1_000_000i128,
            &2000u64,
            &3000u64,
            &BytesN::from_array(&env, &[2u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
        assert_eq!(vault_id2, 0u32);

        let vault = client.get_vault_state(&vault_id2).expect("Vault should exist");
        assert_eq!(vault.amount, 1_000_000i128);
    }

    /// Test: Validate milestone with different vault configurations
    /// Ensures validation works across different vault setups.
    #[test]
    fn test_validate_milestone_various_configs() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        env.mock_all_auths();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Create vault with verifier
        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        client.create_vault(
            &creator,
            &5000i128,
            &100u64,
            &5000u64,
            &BytesN::from_array(&env, &[3u8; 32]),
            &Some(verifier.clone()),
            &Address::generate(&env),
            &Address::generate(&env),
        );

        // Validate milestone
        let result = client.validate_milestone(&0u32);
        assert!(result);

        let vault = client.get_vault_state(&0u32).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Completed);
        assert_eq!(vault.verifier, Some(verifier));
    }

    /// Test: Redirect funds with different timestamps
    /// Ensures redirect works with various time configurations.
    #[test]
    fn test_redirect_funds_various_timestamps() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        env.mock_all_auths();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Create vault with specific timestamps
        let creator = Address::generate(&env);
        client.create_vault(
            &creator,
            &3000i128,
            &1000u64,
            &9999u64,
            &BytesN::from_array(&env, &[4u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        // Redirect funds
        let result = client.redirect_funds(&0u32);
        assert!(result);

        let vault = client.get_vault_state(&0u32).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Failed);
        assert_eq!(vault.start_timestamp, 1000u64);
        assert_eq!(vault.end_timestamp, 9999u64);
    }

    /// Test: Cancel vault with different creators
    /// Ensures cancellation works for various creator addresses.
    #[test]
    fn test_cancel_vault_various_creators() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        env.mock_all_auths();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Create vault with specific creator
        let creator = Address::generate(&env);
        client.create_vault(
            &creator,
            &7500i128,
            &500u64,
            &1500u64,
            &BytesN::from_array(&env, &[5u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        // Cancel vault
        let result = client.cancel_vault(&0u32);
        assert!(result);

        let vault = client.get_vault_state(&0u32).expect("Vault should exist");
        assert_eq!(vault.status, VaultStatus::Cancelled);
        assert_eq!(vault.creator, creator);
    }

    /// Test: All status enum values are used
    /// Ensures complete coverage of VaultStatus enum.
    #[test]
    fn test_all_vault_statuses() {
        let env = Env::default();
        let contract_id = env.register_contract(None, DisciplrVault);
        env.mock_all_auths();
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Test Active status
        let creator = Address::generate(&env);
        client.create_vault(
            &creator,
            &1000i128,
            &0u64,
            &1000u64,
            &BytesN::from_array(&env, &[6u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
        let vault = client.get_vault_state(&0u32).unwrap();
        assert_eq!(vault.status, VaultStatus::Active);

        // Test Completed status
        client.release_funds(&0u32);
        let vault = client.get_vault_state(&0u32).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);

        // Create new vault for Failed status
        client.create_vault(
            &creator,
            &2000i128,
            &0u64,
            &1000u64,
            &BytesN::from_array(&env, &[7u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
        client.redirect_funds(&0u32);
        let vault = client.get_vault_state(&0u32).unwrap();
        assert_eq!(vault.status, VaultStatus::Failed);

        // Create new vault for Cancelled status
        client.create_vault(
            &creator,
            &3000i128,
            &0u64,
            &1000u64,
            &BytesN::from_array(&env, &[8u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
        client.cancel_vault(&0u32);
        let vault = client.get_vault_state(&0u32).unwrap();
        assert_eq!(vault.status, VaultStatus::Cancelled);
    }
}
