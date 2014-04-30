module BlockChain

open util/relation as rel

//open transaction[Transaction]
//open util/ordering [Block]

sig Transaction {}

abstract sig Block {
	ledger: set Transaction,
}

one sig GenesisBlock extends Block {}

sig ChildBlock extends Block {
	hash: one Block
}

fact GenesisHash {
	--all g : GenesisBlock | g.hash =g
}

fact Children {
	irreflexive[hash] //all c : ChildBlock | c not in c.hash							// not self-looping
	all disj a,b : Block | a.hash = b => b.hash != a 		// asymmetric
	//all disj a,b,c : Block | a.hash = b => c.hash != b 	// exclusive, for the valid and longest block chain
	acyclic[hash, Block]
}

fact BuildingLedger {
	all disj a,b : Block | a.hash = b => b.ledger in a.ledger
	all t : Transaction | t in Block.ledger
}

fact Genesis {
--	all b : ChildBlock | GenesisBlock in ~hash[b]
}

run {} for 6

	

