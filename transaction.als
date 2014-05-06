module transaction

open asymmetricKey

/*
	we implement the exact data structure diagrammed in
	the original paper.
*/

-- the hash of the previous commit, and public key of the recipiant
sig Hash {
	old : one Transaction,
	pubKey : one PubKey
}

-- same imput, same hash
fact HashCannonicity {
	all disj a, b : Hash {
		a.old != b.old
		a.pubKey != b.pubKey
	}
}

-- the signiture of the hash
sig Signature {
	signee : one Hash,
	signer : one PrivKey
}
-- same imput, same key, same hash
fact SignatureCanonicity {
	all disj a, b : Signature {
		a.signee != b.signee
		a.signer != b.signer
	}
}

/*
	this is abstact because transactions can also
	hash a magic initial transaction (i.e. some sort of base case)
	instead of the previous commit in the history
*/
abstract sig Transaction {
	newOwner : one PubKey
}

/*
	This is the "magic base case"
	code that imports this module will associated it with mining
	as this is how new coins are created
*/
sig GenesisTransaction extends Transaction {}

/*
	this is the real transaction
*/
sig RealTransaction extends Transaction{
	hash : one Hash,
	oldOwner : one Signature
}{
	-- the invariants "internal" to each (well-formed) transaction
	-- the hashed public key is indeed the one specified as the destinsation address
	hash.pubKey = newOwner

	-- the signiture indeed is of the hash speficied as part of the transaction
	oldOwner.@signee = hash


	/*
		Crucial verifcation step!!

		transactions are verified by using the public key in the specified previous
		transaction to decrypt the signiture and ensure the result is the hash

		Only the holder of a private key associated with the public key given previously
		as the destination address can sign the hash satisfactarily.

		Since the hash is of the previous commit and destination, the signature
		authenticates the sender as the previous owner, and proves that the
		given destination address is the one intended
	*/
	hash.old.@newOwner = oldOwner.signer.pub
}

-- It isn't useful for alloy to give us unused hashes and signatures
fact NoExtraneousObjects {
	Hash in Transaction.hash
	Signature in Transaction.oldOwner
}

run {}
