module blockChain
/*
	Bitcoin nodes may in theory submit any sort of garbage or attack to the network. Thus the protocol itself has to be resilient to attack.

	In order to model this, we have a few restrictions on the entire blockchain (really "blocktree" counting orphan nodes), but next to none
	on what the blocks themselves look like. Instead we then define a predicate roughly corrosponding to how a block could be declared valid,
	and then show that a chain composed of blocks satisfying that predicate implies the properties we want.

	In reality, other non-canon block chains, called orphans, are fine. But it is easier to write the correctness properties
	if there is only one block chain, rather than a "block tree".
*/

open util/relation as rel

open transaction

-- every block contains a set of transactions
abstract sig Block {
	ledger: set Transaction,
}{
	one GenesisTransaction & ledger	-- every block spawns one coin
}
fact {
	all c : GenesisTransaction | one c.~ledger	-- every block spawns a unique coin
}


one sig GenesisBlock extends Block {}{
	-- no real transactions in a genesis block
	ledger in GenesisTransaction
}

sig ChildBlock extends Block {
	hash: one Block, -- hash points to the previous block
}

fact BlockChildren {
	acyclic[ChildBlock <: hash, Block]
	irreflexive[ChildBlock <: hash]
}

fact NoOrphanTransactions {
	Block.ledger = Transaction	-- no orphan transaction
}

check AsymmetricBlockChain {
	all disj a, b : Block | a.hash = b => b.hash != a
} for 8



pred AcyclicTransactionHistory {
	no ^(hash.old) & iden
}

-- no two different transactions share a previous the previous commit
pred NoDoubleSpend {
	no (hash.old).~(hash.old) - iden
}

 -- the number of coins in circulation at the end = number of coins spawned
pred NoMissingOrExtraCoins {
	#GenesisTransaction = #(Transaction - RealTransaction.hash.old)
}

pred OneGoodBlockChain {
	one Block - (ChildBlock.hash) -- one tip/leaf/chain
	all b : ChildBlock | GoodBlock[b]
}

-- this correspounds more closely to how the network actually verifies a block
pred GoodBlock[b : Block] {
	all t : b.ledger & RealTransaction |
		-- transactions work from current or older blocks
		some t.^(hash.old) & (b.(^hash).ledger + (b.ledger & GenesisTransaction))
}

pred GoodStuff {
	AcyclicTransactionHistory
	NoMissingOrExtraCoins
	NoDoubleSpend
}

-- make sure that criteria for a block to be accepted implies the properties we actually care about
check GoodBlockImpliesGoodStuff {
	OneGoodBlockChain => GoodStuff
}
-- make sure GoodStuff is even possible, as impposible => impossible is trivially satisfied
run { some RealTransaction and GoodStuff } for 5
