module tansaction

open asymmetricKey

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

sig Signature {
	signee : one Hash,
	signer : one PrivKey
}
-- same imput, same key, same hash
fact HashCannonicity {
	all disj a, b : Signature {
		a.signee != b.signee
		a.signer != b.signer
	}
}

sig Transaction {
	newOwner : one PubKey,
	hash : one Hash,
	oldOwner : one Signature
}{
	hash.pubKey = newOwner
	oldOwner.@signee = hash

	hash.old.@newOwner = oldOwner.signer.pub -- crucial verifcation step !!
}

run {}
