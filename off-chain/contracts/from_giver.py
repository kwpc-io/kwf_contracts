from tonclient.client import TonClient
from tonclient.types import DecodedMessageBody, KeyPair
from .ton_contract import BasicContract


class FromGiver(BasicContract):
    async def create(self, base_dir: str, name: str, *args, keypair: KeyPair=None, client: TonClient, **kwargs) -> None:
        return await super().create(base_dir, name, *args, keypair=keypair, client=client, subscribe_event_messages=False, **kwargs)

    async def _process_event(self, event: DecodedMessageBody):
        raise NotImplementedError

    async def address(self):
        return await super().address(None)
