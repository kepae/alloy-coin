module tansaction

open asymmetricKey

sig Hash {
	old : one Transaction,
	pubKey : one PubKey
}

sig Signature {
	signee : one Hash,
	signer : one PrivKey
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

pred Show {}
run Show for 3
