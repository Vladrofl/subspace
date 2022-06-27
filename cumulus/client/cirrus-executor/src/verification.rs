use super::SignedExecutionReceiptFor;
use sp_api::ProvideRuntimeApi;
use sp_executor::{ExecutionReceipt, ExecutorApi, ExecutorId, SignedExecutionReceipt};
use sp_runtime::{generic::BlockId, traits::Block as BlockT, RuntimeAppPublic};
use std::{marker::PhantomData, sync::Arc};

/// Error type for execution receipt verification.
#[derive(Debug, thiserror::Error)]
pub enum ReceiptError {
	#[error("The signature of execution receipt is invalid")]
	BadSignature,
	#[error("Invalid execution receipt author, got: {got}, expected: {expected}")]
	InvalidAuthor { got: ExecutorId, expected: ExecutorId },
	#[error(transparent)]
	RuntimeApi(#[from] sp_api::ApiError),
}

pub(super) struct ReceiptVerifier<Block, PBlock, PClient> {
	primary_chain_client: Arc<PClient>,
	_phantom: PhantomData<(Block, PBlock)>,
}

impl<Block, PBlock, PClient> ReceiptVerifier<Block, PBlock, PClient>
where
	Block: BlockT,
	PBlock: BlockT,
	PClient: ProvideRuntimeApi<PBlock>,
	PClient::Api: ExecutorApi<PBlock, Block::Hash>,
{
	pub(super) fn new(primary_chain_client: Arc<PClient>) -> Self {
		Self { primary_chain_client, _phantom: Default::default() }
	}

	/// Verifies the signature and author of given receipt.
	pub(super) fn verify(
		&self,
		signed_execution_receipt: &SignedExecutionReceiptFor<PBlock, Block::Hash>,
	) -> Result<(), ReceiptError> {
		let SignedExecutionReceipt { execution_receipt, signature, signer } =
			signed_execution_receipt;

		if !signer.verify(&execution_receipt.hash(), signature) {
			return Err(ReceiptError::BadSignature)
		}

		let expected_executor_id = self
			.primary_chain_client
			.runtime_api()
			.executor_id(&BlockId::Hash(execution_receipt.primary_hash))?;
		if *signer != expected_executor_id {
			return Err(ReceiptError::InvalidAuthor {
				got: signer.clone(),
				expected: expected_executor_id,
			})
		}

		Ok(())
	}
}

/// Compares if the receipt `other` is the same with `local`, return a tuple of (local_index,
/// local_trace_root) if there is a mismatch.
pub(super) fn find_trace_mismatch<Number, Hash: Copy + Eq, PNumber, PHash>(
	local: &ExecutionReceipt<Number, PHash, Hash>,
	other: &ExecutionReceipt<PNumber, PHash, Hash>,
) -> Option<(usize, Hash)> {
	local.trace.iter().enumerate().zip(other.trace.iter().enumerate()).find_map(
		|((local_idx, local_root), (_, other_root))| {
			if local_root != other_root {
				Some((local_idx, *local_root))
			} else {
				None
			}
		},
	)
}
