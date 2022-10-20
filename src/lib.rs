//! A NFT Rentable smart contract using the Concordium Token Standard CIS2.
//!
//! # Description
//! An instance of this smart contract can contain a number of different token
//! each identified by a token ID. A token is then globally identified by the
//! contract address together with the token ID.
//!
//! This contract is initialized with no tokens, and tokens can
//! be minted through a `mint` contract function, which will only succeed for
//! the contract owner. No functionality to burn token is defined.
//!
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! As follows from the CIS2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators. An operator of some address is allowed to transfer
//! any tokens owned by this address.
//!
//! This contract has a `user` role for renting tokens, which will only succeed
//! for the token owner. An Address and Expiration timestamp can be given.

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::*;

/// The baseurl for the token metadata, gets appended with the token ID as hex
/// encoding before emitted in the TokenMetadata event.
const TOKEN_METADATA_BASE_URL: &str = "https://some.example/token/";

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

// Events
/// Tag for the NFT UpdateUser event.
pub const UPDATE_USER_EVENT_TAG: u8 = u8::MAX - 5;

/// Trait for marking types as Address.
pub trait IsAddress: Serialize + schema::SchemaType {}

/// Trait for marking types as u64.
pub trait IsU64: Serialize + schema::SchemaType {}

impl IsU64 for u64 {}

/// An untagged event when the user of an NFT is changed or expires is changed.
/// For a tagged version, use `NftEvent`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct UpdateUserEvent<T: IsTokenId, A: IsAddress, U: IsU64> {
    /// The ID of the token being transferred.
    pub token_id: T,
    /// The address to whom, user role would be assigned.
    pub user: A,
    /// The timestamp when the user role expires.
    pub expires: U,
}

/// Tagged Nft event to be serialized for the event log.
#[derive(Debug)]
pub enum NftEvent<T: IsTokenId, A: IsAddress, U: IsU64> {
    /// Updates to a user for a specific token id, address and timestamp.
    UpdateUser(UpdateUserEvent<T, A, U>),
}

impl<T: IsTokenId, A: IsAddress, U: IsU64> Serial for NftEvent<T, A, U> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            NftEvent::UpdateUser(event) => {
                out.write_u8(UPDATE_USER_EVENT_TAG)?;
                event.serial(out)
            }
        }
    }
}

impl<T: IsTokenId, A: IsAddress, U: IsU64> Deserial for NftEvent<T, A, U> {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let tag = source.read_u8()?;
        match tag {
            UPDATE_USER_EVENT_TAG => {
                UpdateUserEvent::<T, A, U>::deserial(source)
                    .map(NftEvent::UpdateUser)
            }
            _ => Err(ParseError::default()),
        }
    }
}

// Errors

/// The custom errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Failing to mint new tokens because one of the token IDs already exists
    /// in this contract.
    TokenIdAlreadyExists,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failed to get user address.
    InvalidUserAddress,
}

/// Wrapping the custom errors in a type with CIS1 errors.
type ContractError = Cis2Error<CustomContractError>;

type ContractResult<A> = Result<A, ContractError>;

/// Mapping the logging errors to CustomContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Mapping errors related to contract invocations to CustomContractError.
impl<T> From<CallContractError<T>> for CustomContractError {
    fn from(_cce: CallContractError<T>) -> Self {
        Self::InvokeContractError
    }
}

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self {
        Cis2Error::Custom(c)
    }
}

// Types

/// The user address, similar to the Address type but with serialization.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the variants and the order of their fields
// cannot be changed.
#[derive(Debug, Serialize, Copy, Clone)]
pub enum User {
    /// The user is an account address.
    Account(AccountAddress),
    /// The user is a contract address.
    Contract(ContractAddress),
}

impl User {
    /// Construct a user from an account address.
    pub fn from_account(address: AccountAddress) -> Self {
        User::Account(address)
    }

    /// Construct a user from a contract address.
    pub fn from_contract(address: ContractAddress) -> Self {
        User::Contract(address)
    }

    /// Get the Address of the user.
    pub fn address(&self) -> Address {
        match self {
            User::Account(address) => Address::Account(*address),
            User::Contract(address, ..) => Address::Contract(*address),
        }
    }
}

impl schema::SchemaType for User {
    fn get_type() -> schema::Type {
        schema::Type::Enum(vec![
            (
                String::from("Account"),
                schema::Fields::Unnamed(vec![AccountAddress::get_type()]),
            ),
            (
                String::from("Contract"),
                schema::Fields::Unnamed(vec![
                    ContractAddress::get_type(),
                    // The below string represents the function entrypoint
                    schema::Type::String(schema::SizeLength::U16),
                ]),
            ),
        ])
    }
}

impl From<AccountAddress> for User {
    fn from(address: AccountAddress) -> Self {
        Self::from_account(address)
    }
}

impl IsAddress for User {}

/// Contract token ID type.
/// To save bytes we use a token ID type limited to a `u32`.
type ContractTokenId = TokenIdU32;

/// Contract token amount.
/// Since the tokens are non-fungible the total supply of any token will be at
/// most 1 and it is fine to use a small type for representing token amounts.
type ContractTokenAmount = TokenAmountU8;

#[derive(Serialize, SchemaType)]
struct ViewAddressState {
    owned_tokens: Vec<ContractTokenId>,
    operators: Vec<Address>,
}

#[derive(Serialize, SchemaType)]
struct ViewState {
    state: Vec<(Address, ViewAddressState)>,
    all_tokens: Vec<ContractTokenId>,
    user_infos: Vec<(ContractTokenId, UserInfo)>,
}

/// The parameter for the contract function `mint` which mints a number of
/// tokens to a given address.
#[derive(Serial, Deserial, SchemaType)]
struct MintParams {
    /// Owner of the newly minted tokens.
    owner: Address,
    /// A collection of tokens to mint.
    #[concordium(size_length = 1)]
    tokens: collections::BTreeSet<ContractTokenId>,
}

type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

/// Parameter type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;
/// Response type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenAmounts used by this contract.
type ContractBalanceOfQueryResponse =
    BalanceOfQueryResponse<ContractTokenAmount>;

/// Parameter type for the CIS-2 function `tokenMetadata` specialized to the
/// subset of TokenIDs used by this contract.
type ContractTokenMetadataQueryParams =
    TokenMetadataQueryParams<ContractTokenId>;

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct SetImplementorsParams {
    /// The identifier for the standard.
    id: StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    implementors: Vec<ContractAddress>,
}

/// The parameter type for the contract function `setUser`.
#[derive(Debug, Serialize, SchemaType)]
struct SetUserParams {
    /// The ID of the token being transferred.
    token_id: ContractTokenId,
    /// The address whom will become the user.
    user: User,
    /// The expiration timestamp.
    expires: u64,
}

/// A query for the user of a given address for a given token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize)]
pub struct UserOfQuery<T: IsTokenId> {
    /// The ID of the token for which to query the user of.
    pub token_id: T,
}

impl<T: IsTokenId> schema::SchemaType for UserOfQuery<T> {
    fn get_type() -> schema::Type {
        schema::Type::Struct(schema::Fields::Named(vec![(
            "token_id".to_string(),
            T::get_type(),
        )]))
    }
}

/// The parameter type for the contract function `userOf`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize)]
pub struct UserOfQueryParams<T: IsTokenId> {
    /// List of userOf queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<UserOfQuery<T>>,
}

impl<T: IsTokenId> schema::SchemaType for UserOfQueryParams<T> {
    fn get_type() -> schema::Type {
        schema::Type::List(
            schema::SizeLength::U16,
            Box::new(UserOfQuery::<T>::get_type()),
        )
    }
}

/// The response which is sent back when calling the contract function
/// `userOf`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Debug, Serialize)]
pub struct UserOfQueryResponse<A: IsAddress>(
    #[concordium(size_length = 2)] pub Vec<A>,
);

impl<A: IsAddress> schema::SchemaType for UserOfQueryResponse<A> {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U16, Box::new(A::get_type()))
    }
}

impl<A: IsAddress> From<Vec<A>> for UserOfQueryResponse<A> {
    fn from(results: Vec<A>) -> Self {
        UserOfQueryResponse(results)
    }
}

impl<A: IsAddress> AsRef<[A]> for UserOfQueryResponse<A> {
    fn as_ref(&self) -> &[A] {
        &self.0
    }
}

/// Parameter type for the function `userOf` specialized to the subset
/// of TokenIDs used by this contract.
type ContractUserOfQueryParams = UserOfQueryParams<ContractTokenId>;
/// Response type for the function `userOf` specialized to the subset
/// of Users used by this contract.
type ContractUserOfQueryResponse = UserOfQueryResponse<User>;

/// A query for the expires of a given user address for a given token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize)]
pub struct UserExpiresQuery<T: IsTokenId> {
    /// The ID of the token for which to query the user of.
    pub token_id: T,
}

impl<T: IsTokenId> schema::SchemaType for UserExpiresQuery<T> {
    fn get_type() -> schema::Type {
        schema::Type::Struct(schema::Fields::Named(vec![(
            "token_id".to_string(),
            T::get_type(),
        )]))
    }
}

#[derive(Debug, Serialize)]
pub struct UserExpiresQueryParams<T: IsTokenId> {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<UserExpiresQuery<T>>,
}

impl<T: IsTokenId> schema::SchemaType for UserExpiresQueryParams<T> {
    fn get_type() -> schema::Type {
        schema::Type::List(
            schema::SizeLength::U16,
            Box::new(UserExpiresQuery::<T>::get_type()),
        )
    }
}

/// The response which is sent back when calling the contract function
/// `balanceOf`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Debug, Serialize)]
pub struct UserExpiresQueryResponse<A: IsU64>(
    #[concordium(size_length = 2)] pub Vec<A>,
);

impl<A: IsU64> schema::SchemaType for UserExpiresQueryResponse<A> {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U16, Box::new(A::get_type()))
    }
}

impl<A: IsU64> From<Vec<A>> for UserExpiresQueryResponse<A> {
    fn from(results: Vec<A>) -> Self {
        UserExpiresQueryResponse(results)
    }
}

impl<A: IsU64> AsRef<[A]> for UserExpiresQueryResponse<A> {
    fn as_ref(&self) -> &[A] {
        &self.0
    }
}

/// Parameter type for the function `userExpires` specialized to the subset
/// of TokenIDs used by this contract.
type ContractUserExpiresQueryParams = UserExpiresQueryParams<ContractTokenId>;
/// Response type for the function `userExpires` specialized to the subset
/// of u64 used by this contract.
type ContractUserExpiresQueryResponse = UserExpiresQueryResponse<u64>;

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The tokens owned by this address.
    owned_tokens: StateSet<ContractTokenId, S>,
    /// The address which are currently enabled as operators for this address.
    operators: StateSet<Address, S>,
}

impl<S: HasStateApi> AddressState<S> {
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        AddressState {
            owned_tokens: state_builder.new_set(),
            operators: state_builder.new_set(),
        }
    }
}

/// The state of User role.
#[derive(Debug, Serialize, SchemaType)]
struct UserInfo {
    /// The address of user role.
    user: User,
    /// The user expires unix timestamp.
    expires: u64,
}

/// The contract state.
// Note: The specification does not specify how to structure the contract state
// and this could be structured in a more space efficient way depending on the
// use case.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// The state for each address.
    state: StateMap<Address, AddressState<S>, S>,
    /// All of the token IDs
    all_tokens: StateSet<ContractTokenId, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// The state of each user info of token ID.
    user_infos: StateMap<ContractTokenId, UserInfo, S>,
}

// Functions for creating, updating and querying the contract state.
impl<S: HasStateApi> State<S> {
    /// Creates a new state with no tokens.
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            state: state_builder.new_map(),
            all_tokens: state_builder.new_set(),
            implementors: state_builder.new_map(),
            user_infos: state_builder.new_map(),
        }
    }

    /// Mint a new token with a given address as the owner
    fn mint(
        &mut self,
        token: ContractTokenId,
        owner: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        ensure!(
            self.all_tokens.insert(token),
            CustomContractError::TokenIdAlreadyExists.into()
        );

        let mut owner_state = self
            .state
            .entry(*owner)
            .or_insert_with(|| AddressState::empty(state_builder));
        owner_state.owned_tokens.insert(token);
        Ok(())
    }

    /// Check that the token ID currently exists in this contract.
    #[inline(always)]
    fn contains_token(&self, token_id: &ContractTokenId) -> bool {
        self.all_tokens.contains(token_id)
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state.
    /// Since this contract only contains NFTs, the balance will always be
    /// either 1 or 0.
    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<ContractTokenAmount> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        let balance = self
            .state
            .get(address)
            .map(|address_state| {
                if address_state.owned_tokens.contains(token_id) {
                    1
                } else {
                    0
                }
            })
            .unwrap_or(0);
        Ok(balance.into())
    }

    /// Get the user address of a token id.
    fn user_of(&self, token_id: &ContractTokenId) -> ContractResult<User> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        let user = self
            .user_infos
            .get(token_id)
            .map(|user_info| user_info.user)
            .ok_or(ContractError::Custom(
                CustomContractError::InvalidUserAddress,
            ))?;
        Ok(user.into())
    }

    /// Get the user expires of a token id.
    fn user_expires(&self, token_id: &ContractTokenId) -> ContractResult<u64> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        let expires: u64 = self
            .user_infos
            .get(token_id)
            .map(|user_info| user_info.expires)
            .unwrap_or(0);
        Ok(expires.into())
    }

    /// Check if a given address is an operator of a given owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.state
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state with a transfer of some token.
    /// Results in an error if the token ID does not exist in the state or if
    /// the from address have insufficient tokens to do the transfer.
    fn transfer(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        // A zero transfer does not modify the state.
        if amount == 0.into() {
            return Ok(());
        }
        // Since this contract only contains NFTs, no one will have an amount
        // greater than 1. And since the amount cannot be the zero at
        // this point, the address must have insufficient funds for any
        // amount other than 1.
        ensure_eq!(amount, 1.into(), ContractError::InsufficientFunds);

        {
            let mut from_address_state = self
                .state
                .get_mut(from)
                .ok_or(ContractError::InsufficientFunds)?;
            // Find and remove the token from the owner, if nothing is removed,
            // we know the address did not own the token..
            let from_had_the_token =
                from_address_state.owned_tokens.remove(token_id);
            ensure!(from_had_the_token, ContractError::InsufficientFunds);
        }

        // Add the token to the new owner.
        let mut to_address_state = self
            .state
            .entry(*to)
            .or_insert_with(|| AddressState::empty(state_builder));
        to_address_state.owned_tokens.insert(*token_id);
        Ok(())
    }

    /// Update the state adding a new operator for a given address.
    /// Succeeds even if the `operator` is already an operator for the
    /// `address`.
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder<S>,
    ) {
        let mut owner_state = self
            .state
            .entry(*owner)
            .or_insert_with(|| AddressState::empty(state_builder));
        owner_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given address.
    /// Succeeds even if the `operator` is _not_ an operator for the `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.state.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
    }

    /// Check if state contains any implementors for a given standard.
    fn have_implementors(
        &self,
        std_id: &StandardIdentifierOwned,
    ) -> SupportResult {
        if let Some(addresses) = self.implementors.get(std_id) {
            SupportResult::SupportBy(addresses.to_vec())
        } else {
            SupportResult::NoSupport
        }
    }

    /// Set implementors for a given standard.
    fn set_implementors(
        &mut self,
        std_id: StandardIdentifierOwned,
        implementors: Vec<ContractAddress>,
    ) {
        self.implementors.insert(std_id, implementors);
    }

    /// Update the state removing the user for the given token id.
    fn remove_user(&mut self, token_id: &ContractTokenId) {
        self.user_infos.remove(token_id);
    }

    /// Update the state adding a new user for the given token id.
    fn set_user(
        &mut self,
        from: &Address,
        token_id: &ContractTokenId,
        user: &User,
        expires: &u64,
    ) -> ContractResult<()> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);

        let is_token_owner: bool = self
            .state
            .get(from)
            .map(|address_state| address_state.owned_tokens.contains(token_id))
            .unwrap_or(false);

        ensure!(is_token_owner, ContractError::Unauthorized);

        self.user_infos
            .insert(*token_id, UserInfo { user: *user, expires: *expires });

        Ok(())
    }
}

/// Build a string from TOKEN_METADATA_BASE_URL appended with the token ID
/// encoded as hex.
fn build_token_metadata_url(token_id: &ContractTokenId) -> String {
    let mut token_metadata_url = String::from(TOKEN_METADATA_BASE_URL);
    token_metadata_url.push_str(&token_id.to_string());
    token_metadata_url
}

// Contract functions

/// Initialize contract instance with no token types initially.
#[init(contract = "cis2_rentable_nft")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    // Construct the initial contract state.
    Ok(State::empty(state_builder))
}

/// View function that returns the entire contents of the state. Meant for
/// testing.
#[receive(
    contract = "cis2_rentable_nft",
    name = "view",
    return_value = "ViewState"
)]
fn contract_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<ViewState> {
    let state: &State<S> = host.state();

    let mut inner_state: Vec<(Address, ViewAddressState)> = Vec::new();
    for (k, a_state) in state.state.iter() {
        let owned_tokens: Vec<TokenIdU32> = a_state
            .owned_tokens
            .iter()
            .map(|x: StateRef<TokenIdU32>| *x)
            .collect();
        let operators: Vec<Address> =
            a_state.operators.iter().map(|x: StateRef<Address>| *x).collect();
        inner_state.push((*k, ViewAddressState { owned_tokens, operators }));
    }

    let all_tokens: Vec<TokenIdU32> =
        state.all_tokens.iter().map(|x: StateRef<TokenIdU32>| *x).collect();

    let mut user_infos_state: Vec<(ContractTokenId, UserInfo)> = Vec::new();
    for (k, a_state) in state.user_infos.iter() {
        let user: User = a_state.user;
        let expires: u64 = a_state.expires;
        user_infos_state.push((*k, UserInfo { user, expires }));
    }

    Ok(ViewState {
        state: inner_state,
        all_tokens,
        user_infos: user_infos_state,
    })
}

/// Mint new tokens with a given address as the owner of these tokens.
/// Can only be called by the contract owner.
/// Logs a `Mint` and a `TokenMetadata` event for each token.
/// The url for the token metadata is the token ID encoded in hex, appended on
/// the `TOKEN_METADATA_BASE_URL`.
///
/// It rejects if:
/// - The sender is not the contract instance owner.
/// - Fails to parse parameter.
/// - Any of the tokownerens fails to be minted, which could be if:
///     - The minted token ID already exists.
///     - Fails to log Mint event
///     - Fails to log TokenMetadata event
///
/// Note: Can at most mint 32 token types in one call due to the limit on the
/// number of logs a smart contract can produce on each function call.
#[receive(
    contract = "cis2_rentable_nft",
    name = "mint",
    parameter = "MintParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_mint<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Get the contract owner
    let owner = ctx.owner();
    // Get the sender of the transaction
    let sender = ctx.sender();

    ensure!(sender.matches_account(&owner), ContractError::Unauthorized);

    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;

    let (state, builder) = host.state_and_builder();

    for &token_id in params.tokens.iter() {
        // Mint the token in the state.
        state.mint(token_id, &params.owner, builder)?;

        // Event for minted NFT.
        logger.log(&Cis2Event::Mint(MintEvent {
            token_id,
            amount: ContractTokenAmount::from(1),
            owner: params.owner,
        }))?;

        // Metadata URL for the NFT.
        logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(
            TokenMetadataEvent {
                token_id,
                metadata_url: MetadataUrl {
                    url: build_token_metadata_url(&token_id),
                    hash: None,
                },
            },
        ))?;
    }
    Ok(())
}

/// Execute a list of token transfers, in the order of the list.
///
/// Logs a `Transfer` event and invokes a receive hook function for every
/// transfer in the list.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the transfers fail to be executed, which could be if:
///     - The `token_id` does not exist.
///     - The sender is not the owner of the token, or an operator for this
///       specific `token_id` and `from` address.
///     - The token is not owned by the `from`.
/// - Fails to log event.
/// - Any of the receive hook function calls rejects.
#[receive(
    contract = "cis2_rentable_nft",
    name = "transfer",
    parameter = "TransferParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let TransferParams(transfers): TransferParameter =
        ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    for Transfer { token_id, amount, from, to, data } in transfers {
        let (state, builder) = host.state_and_builder();
        // Authenticate the sender for this transfer
        ensure!(
            from == sender || state.is_operator(&sender, &from),
            ContractError::Unauthorized
        );

        let to_address = to.address();

        // Remove associated user
        if from != to_address && state.user_infos.get(&token_id).is_some() {
            let user: User = state.user_of(&token_id)?;
            state.remove_user(&token_id);

            // Log update user event
            logger.log(&NftEvent::UpdateUser(UpdateUserEvent {
                token_id,
                user, // concordium does not have zero address so set same user to expire 0
                expires: 0 as u64,
            }))?;
        }

        // Update the contract state
        state.transfer(&token_id, amount, &from, &to_address, builder)?;

        // Log transfer event
        logger.log(&Cis2Event::Transfer(TransferEvent {
            token_id,
            amount,
            from,
            to: to_address,
        }))?;

        // If the receiver is a contract: invoke the receive hook function.
        if let Receiver::Contract(address, function) = to {
            let parameter =
                OnReceivingCis2Params { token_id, amount, from, data };
            host.invoke_contract(
                &address,
                &parameter,
                function.as_entrypoint_name(),
                Amount::zero(),
            )?;
        }
    }
    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "cis2_rentable_nft",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    let (state, builder) = host.state_and_builder();
    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => {
                state.add_operator(&sender, &param.operator, builder)
            }
            OperatorUpdate::Remove => {
                state.remove_operator(&sender, &param.operator)
            }
        }

        // Log the appropriate event
        logger.log(
            &Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
                UpdateOperatorEvent {
                    owner: sender,
                    operator: param.operator,
                    update: param.update,
                },
            ),
        )?;
    }

    Ok(())
}

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_rentable_nft",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    return_value = "OperatorOfQueryResponse",
    error = "ContractError"
)]
fn contract_operator_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for address being an operator of owner.
        let is_operator =
            host.state().is_operator(&query.address, &query.owner);
        response.push(is_operator);
    }
    let result = OperatorOfQueryResponse::from(response);
    Ok(result)
}

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_rentable_nft",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
    error = "ContractError"
)]
fn contract_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ContractBalanceOfQueryResponse> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance(&query.token_id, &query.address)?;
        response.push(amount);
    }
    let result = ContractBalanceOfQueryResponse::from(response);
    Ok(result)
}

/// Get the token metadata URLs and checksums given a list of token IDs.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_rentable_nft",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams",
    return_value = "TokenMetadataQueryResponse",
    error = "ContractError"
)]
fn contract_token_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<TokenMetadataQueryResponse> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams =
        ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        // Check the token exists.
        ensure!(
            host.state().contains_token(&token_id),
            ContractError::InvalidTokenId
        );

        let metadata_url = MetadataUrl {
            url: build_token_metadata_url(&token_id),
            hash: None,
        };
        response.push(metadata_url);
    }
    let result = TokenMetadataQueryResponse::from(response);
    Ok(result)
}

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_rentable_nft",
    name = "supports",
    parameter = "SupportsQueryParams",
    return_value = "SupportsQueryResponse",
    error = "ContractError"
)]
fn contract_supports<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<SupportsQueryResponse> {
    // Parse the parameter.
    let params: SupportsQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for std_id in params.queries {
        if SUPPORTS_STANDARDS.contains(&std_id.as_standard_identifier()) {
            response.push(SupportResult::Support);
        } else {
            response.push(host.state().have_implementors(&std_id));
        }
    }
    let result = SupportsQueryResponse::from(response);
    Ok(result)
}

/// Set the addresses for an implementation given a standard identifier and a
/// list of contract addresses.
///
/// It rejects if:
/// - Sender is not the owner of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_rentable_nft",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_set_implementor<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Authorize the sender.
    ensure!(
        ctx.sender().matches_account(&ctx.owner()),
        ContractError::Unauthorized
    );
    // Parse the parameter.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;
    // Update the implementors in the state
    host.state_mut().set_implementors(params.id, params.implementors);
    Ok(())
}

/// Set the user address for the given token id.
///
/// Logs a `UpdateUserEvent` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - If fails if the sender is not the owner of the token.
/// - If the token is not owned by the `from`.
/// - Fails to log event.
#[receive(
    contract = "cis2_rentable_nft",
    name = "setUser",
    parameter = "SetUserParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_set_user<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let sender = ctx.sender();

    // Parse the parameter.
    let params: SetUserParams = ctx.parameter_cursor().get()?;
    // Update the user_infos in the state
    host.state_mut().set_user(
        &sender,
        &params.token_id,
        &params.user,
        &params.expires,
    )?;

    // Log update user event
    logger.log(&NftEvent::UpdateUser(UpdateUserEvent {
        token_id: params.token_id,
        user: params.user,
        expires: params.expires,
    }))?;

    Ok(())
}

/// Get the user address of a token ID.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_rentable_nft",
    name = "userOf",
    parameter = "ContractUserOfQueryParams",
    return_value = "ContractUserOfQueryResponse",
    error = "ContractError"
)]
fn contract_user_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ContractUserOfQueryResponse> {
    // Parse the parameter.
    let params: ContractUserOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<User> = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let user: User = host.state().user_of(&query.token_id)?;
        response.push(user);
    }
    let result = ContractUserOfQueryResponse::from(response);
    Ok(result)
}

/// Get the user expires of a token ID.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_rentable_nft",
    name = "userExpires",
    parameter = "ContractUserExpiresQueryParams",
    return_value = "ContractUserExpiresQueryResponse",
    error = "ContractError"
)]
fn contract_user_expires<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ContractUserExpiresQueryResponse> {
    // Parse the parameter.
    let params: ContractUserExpiresQueryParams =
        ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<u64> = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let expires: u64 = host.state().user_expires(&query.token_id)?;
        response.push(expires);
    }
    let result = ContractUserExpiresQueryResponse::from(response);
    Ok(result)
}

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_1: Address = Address::Account(ACCOUNT_1);
    const TOKEN_0: ContractTokenId = TokenIdU32(0);
    const TOKEN_1: ContractTokenId = TokenIdU32(42);
    const TOKEN_2: ContractTokenId = TokenIdU32(43);

    /// Test helper function which creates a contract state with two tokens with
    /// id `TOKEN_0` and id `TOKEN_1` owned by `ADDRESS_0`
    fn initial_state<S: HasStateApi>(
        state_builder: &mut StateBuilder<S>,
    ) -> State<S> {
        let mut state = State::empty(state_builder);
        state
            .mint(TOKEN_0, &ADDRESS_0, state_builder)
            .expect_report("Failed to mint TOKEN_0");
        state
            .mint(TOKEN_1, &ADDRESS_0, state_builder)
            .expect_report("Failed to mint TOKEN_1");
        state
    }

    /// Test initialization succeeds.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let ctx = TestInitContext::empty();
        let mut builder = TestStateBuilder::new();

        // Call the contract function.
        let result = contract_init(&ctx, &mut builder);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        // Note. This is rather expensive as an iterator is created and then
        // traversed - should be avoided when writing smart contracts.
        claim_eq!(
            state.all_tokens.iter().count(),
            0,
            "No token should be initialized"
        );
    }

    /// Test minting, ensuring the new tokens are owned by the given address and
    /// the appropriate events are logged.
    #[concordium_test]
    fn test_mint() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let mut tokens = collections::BTreeSet::new();
        tokens.insert(TOKEN_0);
        tokens.insert(TOKEN_1);
        tokens.insert(TOKEN_2);
        let parameter = MintParams { tokens, owner: ADDRESS_0 };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::empty(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_mint(&ctx, &mut host, &mut logger);

        // Check the result
        claim!(result.is_ok(), "Results in rejection");

        // Check the state
        // Note. This is rather expensive as an iterator is created and then
        // traversed - should be avoided when writing smart contracts.
        claim_eq!(
            host.state().all_tokens.iter().count(),
            3,
            "Expected three tokens in the state."
        );

        let balance0 = host
            .state()
            .balance(&TOKEN_0, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            1.into(),
            "Tokens should be owned by the given address 0"
        );

        let balance1 = host
            .state()
            .balance(&TOKEN_1, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance1,
            1.into(),
            "Tokens should be owned by the given address 0"
        );

        let balance2 = host
            .state()
            .balance(&TOKEN_2, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance2,
            1.into(),
            "Tokens should be owned by the given address 0"
        );

        // Check the logs
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner: ADDRESS_0,
                token_id: TOKEN_0,
                amount: ContractTokenAmount::from(1),
            }))),
            "Expected an event for minting TOKEN_0"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner: ADDRESS_0,
                token_id: TOKEN_1,
                amount: ContractTokenAmount::from(1),
            }))),
            "Expected an event for minting TOKEN_1"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::TokenMetadata::<
                _,
                ContractTokenAmount,
            >(
                TokenMetadataEvent {
                    token_id: TOKEN_0,
                    metadata_url: MetadataUrl {
                        url: format!("{}00000000", TOKEN_METADATA_BASE_URL),
                        hash: None
                    },
                }
            ))),
            "Expected an event for token metadata for TOKEN_0"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::TokenMetadata::<
                _,
                ContractTokenAmount,
            >(
                TokenMetadataEvent {
                    token_id: TOKEN_1,
                    metadata_url: MetadataUrl {
                        url: format!("{}2A000000", TOKEN_METADATA_BASE_URL),
                        hash: None
                    },
                }
            ))),
            "Expected an event for token metadata for TOKEN_1"
        );
    }

    /// Test set user, ensuring user role is only assigned by token owner.
    #[concordium_test]
    fn test_set_user() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let parameter = SetUserParams {
            token_id: TOKEN_0,
            user: User::from_account(ACCOUNT_1),
            expires: 232142342,
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_set_user(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let (user, expires) = host
            .state()
            .user_infos
            .get(&TOKEN_0)
            .map(|address_state| (address_state.user, address_state.expires))
            .unwrap();

        claim_eq!(user.address(), ADDRESS_1);
        claim_eq!(expires, 232142342);

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&NftEvent::UpdateUser(UpdateUserEvent {
                token_id: TOKEN_0,
                user: User::from_account(ACCOUNT_1),
                expires: 232142342 as u64
            })),
            "Incorrect event emitted"
        )
    }

    /// Test set user fails if sender is neither the owner or an operator of the owner.
    #[concordium_test]
    fn test_set_user_not_authorized() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);

        let parameter = SetUserParams {
            token_id: TOKEN_0,
            user: User::from_account(ACCOUNT_0),
            expires: 232142342,
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_set_user(&ctx, &mut host, &mut logger);
        // Check the result.
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(
            err,
            ContractError::Unauthorized,
            "Error is expected to be Unauthorized"
        );
    }

    /// Test transfer updates by removing the user role.
    #[concordium_test]
    fn test_transfer_update_user() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // SET USER
        let set_user_parameter = SetUserParams {
            token_id: TOKEN_0,
            user: User::from_account(ACCOUNT_1),
            expires: 232142342,
        };
        let set_user_parameter_bytes = to_bytes(&set_user_parameter);
        ctx.set_parameter(&set_user_parameter_bytes);

        // Call the contract function.
        let result_1: ContractResult<()> =
            contract_set_user(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result_1.is_ok(), "SetUser results in rejection");

        // Check the state.
        let (user, expires) = host
            .state()
            .user_infos
            .get(&TOKEN_0)
            .map(|address_state| (address_state.user, address_state.expires))
            .unwrap();

        claim_eq!(user.address(), ADDRESS_1);
        claim_eq!(expires, 232142342);

        let balance0 = host
            .state()
            .balance(&TOKEN_0, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        claim_eq!(balance0, 1.into(), "Incorrect amount");

        let user = host
            .state()
            .user_of(&TOKEN_0)
            .expect_report("Token is expected to exist");
        claim_eq!(user.address(), ADDRESS_1, "Incorrect account");

        // TRANSFER
        let transfer = Transfer {
            token_id: TOKEN_0,
            amount: ContractTokenAmount::from(1),
            from: ADDRESS_0,
            to: Receiver::from_account(ACCOUNT_1),
            data: AdditionalData::empty(),
        };
        let transfer_parameter = TransferParams::from(vec![transfer]);
        let transfer_parameter_bytes = to_bytes(&transfer_parameter);
        ctx.set_parameter(&transfer_parameter_bytes);

        // Call the contract function.
        let result_2: ContractResult<()> =
            contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result_2.is_ok(), "Transfer results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 3, "Three events should be logged");
        claim_eq!(
            logger.logs[1],
            to_bytes(&NftEvent::UpdateUser(UpdateUserEvent {
                token_id: TOKEN_0,
                user: User::from_account(ACCOUNT_1),
                expires: 0 as u64
            })),
            "Incorrect event emitted"
        );

        let err = host
            .state()
            .user_of(&TOKEN_0)
            .expect_err_report("Expected to fail");

        claim_eq!(
            err,
            ContractError::Custom(CustomContractError::InvalidUserAddress),
            "Error is expected to be InvalidUserAddress"
        )
    }

    /// Test transfer succeeds, when `from` is the sender.
    #[concordium_test]
    fn test_transfer_account() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        // and parameter.
        let transfer = Transfer {
            token_id: TOKEN_0,
            amount: ContractTokenAmount::from(1),
            from: ADDRESS_0,
            to: Receiver::from_account(ACCOUNT_1),
            data: AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_0, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        let balance1 = host
            .state()
            .balance(&TOKEN_0, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        let balance2 = host
            .state()
            .balance(&TOKEN_1, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            0.into(),
            "Token owner balance should be decreased by the transferred amount"
        );
        claim_eq!(balance1, 1.into(), "Token receiver balance should be increased by the transferred amount");
        claim_eq!(
            balance2,
            1.into(),
            "Token receiver balance for token 1 should be the same as before"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from: ADDRESS_0,
                to: ADDRESS_1,
                token_id: TOKEN_0,
                amount: ContractTokenAmount::from(1),
            })),
            "Incorrect event emitted"
        )
    }

    /// Test transfer token fails, when sender is neither the owner or an
    /// operator of the owner.
    #[concordium_test]
    fn test_transfer_not_authorized() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);

        // and parameter.
        let transfer = Transfer {
            from: ADDRESS_0,
            to: Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_0,
            amount: ContractTokenAmount::from(1),
            data: AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(
            err,
            ContractError::Unauthorized,
            "Error is expected to be Unauthorized"
        )
    }

    /// Test transfer succeeds when sender is not the owner, but is an operator
    /// of the owner.
    #[concordium_test]
    fn test_operator_transfer() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);

        // and parameter.
        let transfer = Transfer {
            from: ADDRESS_0,
            to: Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_0,
            amount: ContractTokenAmount::from(1),
            data: AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();

        let mut state_builder = TestStateBuilder::new();
        let mut state = initial_state(&mut state_builder);
        state.add_operator(&ADDRESS_0, &ADDRESS_1, &mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_transfer(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_0, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        let balance1 = host
            .state_mut()
            .balance(&TOKEN_0, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            0.into(),
            "Token owner balance should be decreased by the transferred amount"
        );
        claim_eq!(balance1, 1.into(), "Token receiver balance should be increased by the transferred amount");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from: ADDRESS_0,
                to: ADDRESS_1,
                token_id: TOKEN_0,
                amount: ContractTokenAmount::from(1),
            })),
            "Incorrect event emitted"
        )
    }

    /// Test adding an operator succeeds and the appropriate event is logged.
    #[concordium_test]
    fn test_add_operator() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        // and parameter.
        let update =
            UpdateOperator { update: OperatorUpdate::Add, operator: ADDRESS_1 };
        let parameter = UpdateOperatorParams(vec![update]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_update_operator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let is_operator = host.state().is_operator(&ADDRESS_1, &ADDRESS_0);
        claim!(is_operator, "Account should be an operator");

        // Checking that `ADDRESS_1` is an operator in the query response of the
        // `contract_operator_of` function as well.
        // Setup parameter.
        let operator_of_query =
            OperatorOfQuery { address: ADDRESS_1, owner: ADDRESS_0 };

        let operator_of_query_vector =
            OperatorOfQueryParams { queries: vec![operator_of_query] };
        let parameter_bytes = to_bytes(&operator_of_query_vector);

        ctx.set_parameter(&parameter_bytes);

        // Checking the return value of the `contract_operator_of` function
        let result: ContractResult<OperatorOfQueryResponse> =
            contract_operator_of(&ctx, &host);

        claim_eq!(
            result.expect_report("Failed getting result value").0,
            [true],
            "Account should be an operator in the query response"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(UpdateOperatorEvent {
                owner: ADDRESS_0,
                operator: ADDRESS_1,
                update: OperatorUpdate::Add,
            })),
            "Incorrect event emitted"
        )
    }
}
