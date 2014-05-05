module blockChain

open util/relation as rel

open transaction[SpawnedCoin] -- each block introduces a bitcoin
//open util/ordering [Block]

sig SpawnedCoin{}

abstract sig Block {
	ledger: set Transaction + SpawnedCoin,
}{
	one SpawnedCoin & ledger //every block spawns one coin
}
fact {
	all c : SpawnedCoin | one c.~ledger // every block spawns a unique coin
}


one sig GenesisBlock extends Block {}{
	ledger in SpawnedCoin // no normal transaction in a genesis block
}

sig ChildBlock extends Block {
	hash: one Block,
}

fact HashCannonicity {
	all disj a, b : ChildBlock | a.hash != b.hash
}

fact BlockChildren {
	acyclic[ChildBlock <: hash, Block]
	irreflexive[ChildBlock <: hash]
}

fact BuildingLedger {
	Block.ledger = SpawnedCoin + Transaction // no orphan transaction

//	all disj a : Block | a.hash.ledger in a.ledger // all blocks contain previous' ledger

	all b : Block | // transactions work from old blocks
		b.ledger.hash.old in b.(^hash).ledger
}

check Assymetric{
	all disj a,b : Block | a.hash = b => b.hash != a 		// asymmetric
}

check NoWeirdTransactionHistory {
	acyclic[hash.old, Transaction]
	irreflexive[hash.old]
} for 8

run {}
