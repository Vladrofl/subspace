//! Schema for executor in the aux-db.

use codec::{Decode, Encode};
use sc_client_api::backend::AuxStore;
use sp_blockchain::{Error as ClientError, Result as ClientResult};
use sp_core::H256;
use sp_executor::ExecutionReceipt;
use sp_runtime::traits::{Block as BlockT, NumberFor, One, SaturatedConversion};
use subspace_core_primitives::BlockNumber;

const EXECUTION_RECEIPT_KEY: &[u8] = b"execution_receipt";
const EXECUTION_RECEIPT_START: &[u8] = b"execution_receipt_start";
const EXECUTION_RECEIPT_BLOCK_NUMBER: &[u8] = b"execution_receipt_block_number";
const BAD_RECEIPT_KEY: &[u8] = b"bad_receipt";
const BAD_RECEIPT_BLOCK_NUMBER: &[u8] = b"bad_receipt_block_number";
const BAD_RECEIPT_NUMBERS: &[u8] = b"bad_receipt_numbers";
/// Prune the execution receipts when they reach this number.
const PRUNING_DEPTH: BlockNumber = 1000;

fn execution_receipt_key(block_hash: impl Encode) -> Vec<u8> {
	(EXECUTION_RECEIPT_KEY, block_hash).encode()
}

fn bad_receipt_key(signed_receipt_hash: impl Encode) -> Vec<u8> {
	(BAD_RECEIPT_KEY, signed_receipt_hash).encode()
}

fn load_decode<Backend: AuxStore, T: Decode>(
	backend: &Backend,
	key: &[u8],
) -> ClientResult<Option<T>> {
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..])
			.map_err(|e| {
				ClientError::Backend(format!("Executor DB is corrupted. Decode error: {}", e))
			})
			.map(Some),
	}
}

/// Write the execution receipt of a block to aux storage, optionally prune the receipts that are
/// too old.
pub(super) fn write_execution_receipt<Backend: AuxStore, Block: BlockT, PBlock: BlockT>(
	backend: &Backend,
	(block_hash, block_number): (Block::Hash, NumberFor<Block>),
	best_execution_chain_number: NumberFor<Block>,
	execution_receipt: &ExecutionReceipt<NumberFor<PBlock>, PBlock::Hash, Block::Hash>,
) -> Result<(), sp_blockchain::Error> {
	let block_number_key = (EXECUTION_RECEIPT_BLOCK_NUMBER, block_number).encode();
	let mut hashes_at_block_number =
		load_decode::<_, Vec<Block::Hash>>(backend, block_number_key.as_slice())?
			.unwrap_or_default();
	hashes_at_block_number.push(block_hash);

	let first_saved_receipt = load_decode::<_, NumberFor<Block>>(backend, EXECUTION_RECEIPT_START)?
		.unwrap_or(block_number);

	let mut new_first_saved_receipt = first_saved_receipt;

	let mut keys_to_delete = vec![];

	if let Some(delete_receipts_to) = best_execution_chain_number
		.saturated_into::<BlockNumber>()
		.checked_sub(PRUNING_DEPTH)
	{
		new_first_saved_receipt = Into::<NumberFor<Block>>::into(delete_receipts_to) + One::one();
		for receipt_to_delete in first_saved_receipt.saturated_into()..=delete_receipts_to {
			let delete_block_number_key =
				(EXECUTION_RECEIPT_BLOCK_NUMBER, receipt_to_delete).encode();

			if let Some(hashes_to_delete) =
				load_decode::<_, Vec<Block::Hash>>(backend, delete_block_number_key.as_slice())?
			{
				keys_to_delete.extend(
					hashes_to_delete.into_iter().map(|h| (EXECUTION_RECEIPT_KEY, h).encode()),
				);
				keys_to_delete.push(delete_block_number_key);
			}
		}
	}

	backend.insert_aux(
		&[
			(execution_receipt_key(block_hash).as_slice(), execution_receipt.encode().as_slice()),
			(block_number_key.as_slice(), hashes_at_block_number.encode().as_slice()),
			(EXECUTION_RECEIPT_START, new_first_saved_receipt.encode().as_slice()),
		],
		&keys_to_delete.iter().map(|k| &k[..]).collect::<Vec<&[u8]>>()[..],
	)
}

/// Load the execution receipt associated with a block.
pub(super) fn load_execution_receipt<Backend, Hash, Number, PHash>(
	backend: &Backend,
	block_hash: Hash,
) -> ClientResult<Option<ExecutionReceipt<Number, PHash, Hash>>>
where
	Backend: AuxStore,
	Hash: Encode + Decode,
	Number: Decode,
	PHash: Decode,
{
	load_decode(backend, execution_receipt_key(block_hash).as_slice())
}

pub(super) fn target_receipt_is_pruned(
	best_execution_chain_number: BlockNumber,
	target_block: BlockNumber,
) -> bool {
	best_execution_chain_number.saturating_sub(target_block) >= PRUNING_DEPTH
}

// Use `signed_receipt_hash` as key to avoid the potential collision that two dishonest
// executors produced a same invalid ER even it's very unlikely.
pub(super) fn write_bad_receipt<Backend: AuxStore, Block: BlockT, PBlock: BlockT>(
	backend: &Backend,
	bad_signed_receipt_hash: H256,
	bad_receipt: &ExecutionReceipt<NumberFor<PBlock>, PBlock::Hash, Block::Hash>,
) -> Result<(), sp_blockchain::Error> {
	let bad_receipt_number = bad_receipt.primary_number;

	let block_number_key = (BAD_RECEIPT_BLOCK_NUMBER, bad_receipt_number).encode();
	let mut hashes_at_block_number =
		load_decode::<_, Vec<H256>>(backend, block_number_key.as_slice())?.unwrap_or_default();
	hashes_at_block_number.push(bad_signed_receipt_hash);

	let mut to_insert = vec![
		(bad_receipt_key(bad_signed_receipt_hash), bad_receipt.encode()),
		(block_number_key, hashes_at_block_number.encode()),
	];

	let mut bad_receipt_numbers =
		load_decode::<_, Vec<NumberFor<PBlock>>>(backend, BAD_RECEIPT_NUMBERS.encode().as_slice())?
			.unwrap_or_default();

	if !bad_receipt_numbers.contains(&bad_receipt_number) {
		bad_receipt_numbers.push(bad_receipt_number);
		to_insert.push((BAD_RECEIPT_NUMBERS.encode(), bad_receipt_numbers.encode()));
	}

	backend.insert_aux(
		&to_insert.iter().map(|(k, v)| (&k[..], &v[..])).collect::<Vec<_>>()[..],
		vec![],
	)
}

pub(super) fn delete_bad_receipt<Backend: AuxStore>(
	backend: &Backend,
	block_number: BlockNumber,
	signed_receipt_hash: H256,
) -> Result<(), sp_blockchain::Error> {
	let block_number_key = (BAD_RECEIPT_BLOCK_NUMBER, block_number).encode();
	let hashes_at_block_number =
		load_decode::<_, Vec<H256>>(backend, block_number_key.as_slice())?.unwrap_or_default();
	let new_hashes = hashes_at_block_number
		.into_iter()
		.filter(|&x| x != signed_receipt_hash)
		.collect::<Vec<_>>();

	let mut keys_to_delete = vec![bad_receipt_key(signed_receipt_hash)];

	let to_insert = if new_hashes.is_empty() {
		keys_to_delete.push(block_number_key);

		let bad_receipt_numbers =
			load_decode::<_, Vec<BlockNumber>>(backend, BAD_RECEIPT_NUMBERS.encode().as_slice())?
				.expect("Set of bad receipt block number must not be empty; qed");
		let new_bad_receipt_numbers =
			bad_receipt_numbers.into_iter().map(|x| x != block_number).collect::<Vec<_>>();

		if new_bad_receipt_numbers.is_empty() {
			keys_to_delete.push(BAD_RECEIPT_NUMBERS.encode());
			vec![]
		} else {
			vec![(BAD_RECEIPT_NUMBERS.encode(), new_bad_receipt_numbers.encode())]
		}
	} else {
		vec![(block_number_key, new_hashes.encode())]
	};

	backend.insert_aux(
		&to_insert.iter().map(|(k, v)| (&k[..], &v[..])).collect::<Vec<_>>()[..],
		&keys_to_delete.iter().map(|k| &k[..]).collect::<Vec<_>>()[..],
	)
}

// (block_number_at_which_bad_receipt_was_generated, bad_signed_receipt_hash, bad_execution_receipt)
type BadReceiptInfo<Block, PBlock> = (
	NumberFor<PBlock>,
	H256,
	ExecutionReceipt<NumberFor<PBlock>, <PBlock as BlockT>::Hash, <Block as BlockT>::Hash>,
);

pub(super) fn load_first_bad_receipt_info<Backend: AuxStore, Block: BlockT, PBlock: BlockT>(
	backend: &Backend,
) -> Result<Option<BadReceiptInfo<Block, PBlock>>, sp_blockchain::Error> {
	let bad_receipt_numbers =
		load_decode::<_, Vec<NumberFor<PBlock>>>(backend, BAD_RECEIPT_NUMBERS.encode().as_slice())?
			.unwrap_or_default();

	// bad_receipt_block_number_set is sorted already.
	if let Some(bad_receipt_number) = bad_receipt_numbers.get(0).copied() {
		let block_number_key = (BAD_RECEIPT_BLOCK_NUMBER, bad_receipt_number).encode();
		let bad_signed_receipt_hashes =
			load_decode::<_, Vec<H256>>(backend, block_number_key.as_slice())?.unwrap_or_default();

		let first_bad_signed_receipt_hash = bad_signed_receipt_hashes[0];

		let first_bad_receipt = load_decode::<
			_,
			ExecutionReceipt<NumberFor<PBlock>, PBlock::Hash, Block::Hash>,
		>(backend, first_bad_signed_receipt_hash.encode().as_slice())?
		.expect("There must be at least one bad receipt as the set of bad receipt number is not empty; qed");

		Ok(Some((bad_receipt_number, first_bad_signed_receipt_hash, first_bad_receipt)))
	} else {
		Ok(None)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use cirrus_test_service::runtime::Block;
	use sp_core::hash::H256;
	use subspace_runtime_primitives::{BlockNumber, Hash};
	use subspace_test_runtime::Block as PBlock;

	type ExecutionReceipt = sp_executor::ExecutionReceipt<BlockNumber, Hash, Hash>;

	fn create_execution_receipt(primary_number: BlockNumber) -> ExecutionReceipt {
		ExecutionReceipt {
			primary_number,
			primary_hash: H256::random(),
			secondary_hash: H256::random(),
			trace: Default::default(),
			trace_root: Default::default(),
		}
	}

	#[test]
	fn normal_prune_execution_receipt_works() {
		let client = substrate_test_runtime_client::new();

		let receipt_start = || {
			load_decode::<_, BlockNumber>(&client, EXECUTION_RECEIPT_START.to_vec().as_slice())
				.unwrap()
		};

		let hashes_at = |number: BlockNumber| {
			load_decode::<_, Vec<Hash>>(
				&client,
				(EXECUTION_RECEIPT_BLOCK_NUMBER, number).encode().as_slice(),
			)
			.unwrap()
		};

		let receipt_at = |block_hash: Hash| load_execution_receipt(&client, block_hash).unwrap();

		let write_receipt_at = |hash: Hash, number: BlockNumber, receipt: &ExecutionReceipt| {
			write_execution_receipt::<_, Block, PBlock>(
				&client,
				(hash, number),
				number - 1, // Ideally, the receipt of previous block has been included when writing the receipt of current block.
				receipt,
			)
			.unwrap()
		};

		assert_eq!(receipt_start(), None);

		// Create PRUNING_DEPTH receipts.
		let block_hash_list = (1..=PRUNING_DEPTH)
			.map(|block_number| {
				let receipt = create_execution_receipt(block_number);
				let block_hash = Hash::random();
				write_receipt_at(block_hash, block_number, &receipt);
				assert_eq!(receipt_at(block_hash), Some(receipt));
				assert_eq!(hashes_at(block_number), Some(vec![block_hash]));
				assert_eq!(receipt_start(), Some(1));
				block_hash
			})
			.collect::<Vec<_>>();

		assert!(!target_receipt_is_pruned(PRUNING_DEPTH, 1));

		// Create PRUNING_DEPTH + 1 receipt, best_execution_chain_number is PRUNING_DEPTH.
		let block_hash = Hash::random();
		assert!(receipt_at(block_hash).is_none());
		write_receipt_at(
			block_hash,
			PRUNING_DEPTH + 1,
			&create_execution_receipt(PRUNING_DEPTH + 1),
		);
		assert!(receipt_at(block_hash).is_some());

		// Create PRUNING_DEPTH + 2 receipt, best_execution_chain_number is PRUNING_DEPTH + 1.
		let block_hash = Hash::random();
		write_receipt_at(
			block_hash,
			PRUNING_DEPTH + 2,
			&create_execution_receipt(PRUNING_DEPTH + 2),
		);
		assert!(receipt_at(block_hash).is_some());

		// ER of block #1 should be pruned.
		assert!(receipt_at(block_hash_list[0]).is_none());
		// block number mapping should be pruned as well.
		assert!(hashes_at(1).is_none());
		assert!(target_receipt_is_pruned(PRUNING_DEPTH + 1, 1));
		assert_eq!(receipt_start(), Some(2));

		// Create PRUNING_DEPTH + 3 receipt, best_execution_chain_number is PRUNING_DEPTH + 2.
		let block_hash = Hash::random();
		write_receipt_at(
			block_hash,
			PRUNING_DEPTH + 3,
			&create_execution_receipt(PRUNING_DEPTH + 3),
		);
		assert!(receipt_at(block_hash).is_some());
		// ER of block #2 should be pruned.
		assert!(receipt_at(block_hash_list[1]).is_none());
		assert!(target_receipt_is_pruned(PRUNING_DEPTH + 2, 2));
		assert!(!target_receipt_is_pruned(PRUNING_DEPTH + 2, 3));
		assert_eq!(receipt_start(), Some(3));

		// Multiple hashes attached to the block #(PRUNING_DEPTH + 3)
		let block_hash2 = Hash::random();
		write_receipt_at(
			block_hash2,
			PRUNING_DEPTH + 3,
			&create_execution_receipt(PRUNING_DEPTH + 3),
		);
		assert!(receipt_at(block_hash2).is_some());
		assert_eq!(hashes_at(PRUNING_DEPTH + 3), Some(vec![block_hash, block_hash2]));
	}

	#[test]
	fn execution_receipts_should_be_kept_against_best_execution_chain_number() {
		let client = substrate_test_runtime_client::new();

		let receipt_start = || {
			load_decode::<_, BlockNumber>(&client, EXECUTION_RECEIPT_START.to_vec().as_slice())
				.unwrap()
		};

		let hashes_at = |number: BlockNumber| {
			load_decode::<_, Vec<Hash>>(
				&client,
				(EXECUTION_RECEIPT_BLOCK_NUMBER, number).encode().as_slice(),
			)
			.unwrap()
		};

		let receipt_at = |block_hash: Hash| load_execution_receipt(&client, block_hash).unwrap();

		let write_receipt_at = |(hash, number): (Hash, BlockNumber),
		                        best_execution_chain_number: BlockNumber,
		                        receipt: &ExecutionReceipt| {
			write_execution_receipt::<_, Block, PBlock>(
				&client,
				(hash, number),
				best_execution_chain_number,
				receipt,
			)
			.unwrap()
		};

		assert_eq!(receipt_start(), None);

		// Create PRUNING_DEPTH receipts, best_execution_chain_number is 0, i.e., no receipt
		// has ever been included on primary chain.
		let block_hash_list = (1..=PRUNING_DEPTH)
			.map(|block_number| {
				let receipt = create_execution_receipt(block_number);
				let block_hash = Hash::random();
				write_receipt_at((block_hash, block_number), 0, &receipt);
				assert_eq!(receipt_at(block_hash), Some(receipt));
				assert_eq!(hashes_at(block_number), Some(vec![block_hash]));
				assert_eq!(receipt_start(), Some(1));
				block_hash
			})
			.collect::<Vec<_>>();

		assert!(!target_receipt_is_pruned(PRUNING_DEPTH, 1));

		// Create PRUNING_DEPTH + 1 receipt, best_execution_chain_number is 0.
		let block_hash = Hash::random();
		assert!(receipt_at(block_hash).is_none());
		write_receipt_at(
			(block_hash, PRUNING_DEPTH + 1),
			0,
			&create_execution_receipt(PRUNING_DEPTH + 1),
		);

		// Create PRUNING_DEPTH + 2 receipt, best_execution_chain_number is 0.
		let block_hash = Hash::random();
		write_receipt_at(
			(block_hash, PRUNING_DEPTH + 2),
			0,
			&create_execution_receipt(PRUNING_DEPTH + 2),
		);

		// ER of block #1 should not be pruned even the size of stored receipts exceeds the pruning depth.
		assert!(receipt_at(block_hash_list[0]).is_some());
		// block number mapping for #1 should not be pruned neither.
		assert!(hashes_at(1).is_some());
		assert!(!target_receipt_is_pruned(0, 1));
		assert_eq!(receipt_start(), Some(1));

		// Create PRUNING_DEPTH + 3 receipt, best_execution_chain_number is 0.
		let block_hash = Hash::random();
		write_receipt_at(
			(block_hash, PRUNING_DEPTH + 3),
			0,
			&create_execution_receipt(PRUNING_DEPTH + 3),
		);

		// Create PRUNING_DEPTH + 4 receipt, best_execution_chain_number is PRUNING_DEPTH + 3.
		let block_hash = Hash::random();
		write_receipt_at(
			(block_hash, PRUNING_DEPTH + 4),
			PRUNING_DEPTH + 3, // Now assuming all the missing receipts are included.
			&create_execution_receipt(PRUNING_DEPTH + 4),
		);
		assert!(receipt_at(block_hash_list[0]).is_none());
		// receipt and block number mapping for [1, 2, 3] should be pruned.
		(1..=3).for_each(|pruned| {
			assert!(hashes_at(pruned).is_none());
			assert!(target_receipt_is_pruned(PRUNING_DEPTH + 3, pruned));
		});
		assert_eq!(receipt_start(), Some(4));
	}
}
