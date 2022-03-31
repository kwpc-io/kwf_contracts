import tonos_ts4.ts4 as ts4


class KWDPool(ts4.BaseContract):
    def __init__(
        self,
        final_address,
        fund_address_,
        nonce_,
        keypair=None,
        balance=None,
        error_code=0,
    ):
        super().__init__(
            'KWDPool',
            initial_data=dict(
                fund_address_=fund_address_,
                nonce_=nonce_,
            ),
            ctor_params=None,
            keypair=keypair,
            balance=balance,
        )
        super().call_method(
            method='constructor',
            params=dict(
                final_address=final_address,
            ),
            private_key=self.private_key_,
            expect_ec=error_code,
        )

    def notify_participant(self, summa_investors, summa_givers):
        super().call_method(
            'notifyParticipant',
            params=dict(
                summa_investors=summa_investors,
                summa_givers=summa_givers,
            ),
            private_key=self.private_key_,
        )

    def send_funds(self, address_to):
        super().call_method(
            method='sendFunds',
            params=dict(
                address_to=address_to,
            ),
            private_key=self.private_key_,
        )

    def return_funds(self, address_to):
        super().call_method(
            method='returnFunds',
            params=dict(
                address_to=address_to,
            ),
            private_key=self.private_key_,
        )

    def vote(self, choice, voting_id, code_hash):
        super().call_method(
            method='vote',
            params=dict(
                choice=choice,
                voting_id=voting_id,
                code_hash=code_hash,
            ),
            private_key=self.private_key_,
        )
