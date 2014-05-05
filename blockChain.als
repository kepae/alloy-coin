module blockChain

open util/relation as rel

open transaction
//open util/ordering [Block]

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
	Block.ledger = Transaction	-- no orphan transaction
	no ^(hash.old) & iden		-- acyclic transaction history

	all b : Block | b.ledger.hash.old in b.(^hash + iden).ledger
	-- transactions work from current or older blocks
}



check Asymmetric {
	all disj a, b : Block | a.hash = b => b.hash != a
} for 8

check NoWeirdTransactionHistory {
	acyclic[hash.old, Transaction]
	irreflexive[hash.old]
} for 5

run {} for 5
