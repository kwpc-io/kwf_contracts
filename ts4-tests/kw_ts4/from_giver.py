import tonos_ts4.ts4 as ts4


class FromGiver(ts4.BaseContract):
    def __init__(
        self,
        address,
    ):
        super().__init__(
            'FromGiver',
            ctor_params=None,
            address=address,
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

    def return_funds(self):
        super().call_method(
            method='returnFunds',
            params=dict(),
            private_key=self.private_key_,
        )
