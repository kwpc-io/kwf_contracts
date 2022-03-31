from tonclient.client import TonClient
from tonclient.types import DecodedMessageBody, KeyPair
from .ton_contract import BasicContract


class Blank(BasicContract):
    async def create(self, base_dir: str, name: str, *args, keypair: KeyPair=None, client: TonClient, **kwargs) -> None:
        return await super().create(base_dir, name, *args, keypair=keypair, client=client, subscribe_event_messages=False, **kwargs)

    async def _process_event(self, event: DecodedMessageBody):
        raise NotImplementedError

    async def address(self):
        return await super().address(
            dict(
                min_summa=0,
                max_summa=0,
            )
        )

    async def deploy(self) -> None:
        return await super().deploy(
            args=dict(
                min_summa=0,
                max_summa=100,
            )
        )

    async def setFromGiverCode(self, code_hash):
        return await self._call_method(
            method='setFromGiverCodeHash',
            args={
                'code_hash': code_hash,
            }
        )

    async def setKWDPoolCodeHash(self, code_hash):
        return await self._call_method(
            method='setKWDPoolCodeHash',
            args={
                'code_hash': code_hash,
            }
        )

    async def deployFromGiver(self, code, giver):
        return await self._call_method(
            method='deployFromGiver',
            args={
                'code': code,
                'giver': giver,
            }
        )

    async def setFundCode(self, code):
        return await self._call_method(
            method='SetFundCode',
            args={
                'code': code,
            }
        )

    async def finalize(self, forse_giveup, addr):
        return await self._call_method(
            method='finalize',
            args={
                'forse_giveup': forse_giveup,
                'addr': addr,
            }
        )
