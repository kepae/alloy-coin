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

fact NoOrphanTransactions {
	Block.ledger = Transaction	-- no orphan transaction
}

check AsymmetricBlockChain {
	all disj a, b : Block | a.hash = b => b.hash != a
} for 8




pred AcyclicTransactionHistory {
	no ^(hash.old) & iden
}

 -- the number of coins in circulation at the end = number of coins spawned
pred NoFraud {
	#GenesisTransaction = #(Transaction - RealTransaction.hash.old)
}

pred OneGoodBlockChain {
	one Block - (ChildBlock.hash) -- one tip/leaf/chain
	all b : ChildBlock | GoodBlock[b]
}

pred GoodBlock[b : Block] { -- transactions work from current or older blocks
	all t : b.ledger & RealTransaction |
		some t.^(hash.old) & (b.(^hash).ledger + (b.ledger & GenesisTransaction))
}

pred GoodStuff {
	AcyclicTransactionHistory
	NoFraud
}

check GoodBlockImpliesGoodStuff {
	OneGoodBlockChain => GoodStuff
}
-- make sure GoodStuff is even possible
run { some RealTransaction and GoodStuff } for 5
