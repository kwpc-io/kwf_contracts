from email.mime import base
import tonos_ts4.ts4 as ts4


class SafeMultisig(ts4.BaseContract):
    def __init__(self, balance=None):
        keypair = ts4.make_keypair()
        super().__init__(
            'SafeMultisigWallet',
            dict(
                owners=[keypair[1]],
                reqConfirms=1,
            ),
            0, {}, keypair=keypair, balance=balance,
        )

    def send_transaction(self, dest, value):
        super().call_method(
            method='sendTransaction',
            params=dict(
                dest=dest,
                value=value,
                bounce=False,
                flags=1,
                payload=ts4.Cell(''),
            ),
            private_key=self.private_key_,
        )
