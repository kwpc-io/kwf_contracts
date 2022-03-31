import aiohttp
import base64
import json
import os

from tonclient.types import Abi, AbiContract, CallSet, KeyPair, NetworkConfig,\
    Signer, ParamsOfEncodeMessage, ParamsOfProcessMessage, ParamsOfGetCodeFromTvc,\
    ParamsOfGetBocHash, ParamsOfDecodeAccountData, ParamsOfQueryCollection
from tonclient.types import ClientConfig
from tonclient.client import TonClient

from contracts import MultisigContract


GIVER_ADDRESS = '0:b5e9240fc2d2f1ff8cbb1d1dee7fb7cae155e5f6320e585fcc685698994a19a5'


# client = TonClient(
    
#     config=ClientConfig(
#         # network=NetworkConfig(server_address='https://net.ton.dev'),
#         network=NetworkConfig(server_address='http://localhost'),
#     ),
#     is_async=True,
# )


client = TonClient(
    config=ClientConfig(),
    is_async=True,
)


async def send_tons_with_se_giver(
    address: str,
    value: int,
    directory: str,
):
    print('send tonds to ', address)
    giver_abi = Abi.from_path(
        path=os.path.join(directory, 'GiverV2.abi.json')
    )
    call_set = CallSet(
        function_name='sendTransaction',
        input={"dest":address, "value": value, "bounce": False},
    )
    with open(os.path.join(directory, 'GiverV2.keys.json')) as json_file:
        keys = json.load(json_file)
    encode_params = ParamsOfEncodeMessage(
        abi=giver_abi, signer=Signer.Keys(KeyPair(**keys)), address=GIVER_ADDRESS,
        call_set=call_set)
    process_params = ParamsOfProcessMessage(
        message_encode_params=encode_params, send_events=False)
    return await client.processing.process_message(params=process_params)


async def send_tons_with_multisig(
    address: str,
    value: int,
    directory: str,
    file_name: str='SafeMultisigWallet'
):
    with open(os.path.join(directory, f'{file_name}.keys.json'), 'r') as json_file:
        keys = json.load(json_file)

    multisig = MultisigContract()
    await multisig.create(
        base_dir=directory,
        name=file_name,
        client=client,
        keypair=KeyPair(
            public=keys['public'],
            secret=keys['secret'],
        )
    )

    return await multisig.submit_transaction(
        dest=address,
        value=value,
    )


async def get_contract_code(file_path: str):
    tvc = ''
    with open(file_path, 'rb') as file:
        tvc = base64.b64encode(file.read()).decode()

    result = await client.boc.get_code_from_tvc(
        params=ParamsOfGetCodeFromTvc(tvc=tvc))
    return result.code


async def get_contract_code_hash(file_path: str) -> int:
    code = await get_contract_code(file_path)
    result = await client.boc.get_boc_hash(
        params=ParamsOfGetBocHash(boc=code))
    contract_hash = result.hash
    return contract_hash


async def decode_account_data(data: str, file_path: str):
    abi = Abi.from_path(file_path)
    params = ParamsOfDecodeAccountData(abi=abi, data=data)
    decoded = await client.abi.decode_account_data(params=params)
    return decoded.data


def load_filters_json(file_path: str):
    filters = dict()
    with open(file_path) as json_file:
        keys = json.load(json_file)


async def query_last_transactions(timestamp):
    query_params = ParamsOfQueryCollection(
        collection='transactions',
        result='compute {exit_code, success}',
        filter={
            'now': {
                'gt': timestamp,
            },
        },
    )
    result = await client.net.query_collection(params=query_params)
    return result.result
