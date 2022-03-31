import tonos_ts4.ts4 as ts4


class Blank(ts4.BaseContract):
    def __init__(
        self,

        min_summa,
        max_summa,

        lock_time_,
        unlock_time_,
        farm_rate_,
        kwf_lock_time_,
        quant_,
        nonce_,

        keypair=None,
        balance=None,

        error_code=0,
    ):
        super().__init__(
            'Blank',
            ctor_params=None,
            initial_data=dict(
                lock_time_=lock_time_,
                unlock_time_=unlock_time_,
                farm_rate_=farm_rate_,
                kwf_lock_time_=kwf_lock_time_,
                quant_=quant_,
                nonce_=nonce_,
            ),
            keypair=keypair,
            balance=balance,
        )

        super().call_method(
            method='constructor',
            params=dict(
                min_summa=min_summa,
                max_summa=max_summa,
            ),
            private_key=self.private_key_,
            expect_ec=error_code,
        )

    def setFromGiverCode(self, code_hash, code_depth, error_code=0):
        super().call_method(
            method='setFromGiverCodeHash',
            params=dict(
                code_hash=code_hash,
                code_depth=code_depth,
            ),
            private_key=self.private_key_,
            expect_ec=error_code,
        )

    def setKWDPoolCodeHash(self, code_hash, code_depth, error_code=0):
        super().call_method(
            method='setKWDPoolCodeHash',
            params=dict(
                code_hash=code_hash,
                code_depth=code_depth,
            ),
            private_key=self.private_key_,
            expect_ec=error_code,
        )

    def deployFromGiver(self, code, giver, nonce, error_code=0):
        return super().call_method(
            method='deployFromGiver',
            params=dict(
                code=code,
                giver=giver,
                nonce=nonce,
            ),
            private_key=self.private_key_,
            expect_ec=error_code,
        )

    def finalize(self, force_giveup, addr):
        super().call_method(
            method='finalize',
            params=dict(
                addr=addr,
                force_giveup=force_giveup,
            ),
            private_key=self.private_key_,
        )

    def startVoting(self, voting_time, code_hash):
        super().call_method(
            method='startVoting',
            params=dict(
                voting_time=voting_time,
                code_hash=code_hash,
            ),
            private_key=self.private_key_,
        )

    def setFundCode(self, code):
        super().call_method(
            method='setFundCode',
            params=dict(code=code),
            private_key=self.private_key_,
        )

    def killBlank(self, address_to):
        super().call_method(
            method='killBlank',
            params=dict(address_to=address_to),
            private_key=self.private_key_,
        )
