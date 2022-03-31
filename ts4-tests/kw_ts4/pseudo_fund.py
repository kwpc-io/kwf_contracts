import tonos_ts4.ts4 as ts4


class PseudoFund(ts4.BaseContract):
    def __init__(
        self,
        address,
        keypair,
    ):
        super().__init__(
            'PseudoFund',
            ctor_params={},
            address=address,
            keypair=keypair,
        )

    def getFromGiverFunds(self, from_giver_address):
        super().call_method(
            'getFromGiverFunds',
            params=dict(
                from_giver_address=from_giver_address,
            ),
            private_key=self.private_key_,
        )

    def transferFundsTo(self, kwdp_address, code):
        super().call_method(
            'transferFundsTo',
            params=dict(
                kwdp_address=kwdp_address,
                code=code,
            ),
            private_key=self.private_key_,
        )

    def killFund(self, address_to):
        super().call_method(
            method='killFund',
            params=dict(
                address_to=address_to,
            ),
            private_key=self.private_key_,
        )

    def sendParams(self):
        super().call_method(
            method='sendParams',
            params=dict(),
            private_key=self.private_key_,
        )
