import asyncio
import json
import os
import sys
import time

from tonclient.client import TonClient
from tonclient.client import ClientConfig
from tonclient.types import NetworkConfig
from tonclient.types import ParamsOfQueryCollection

from contracts import TestContract
from utils import get_contract_code_hash
from utils import send_tons_with_multisig
from utils import send_tons_with_se_giver
from utils import decode_account_data


client = TonClient(
    config=ClientConfig(
        network=NetworkConfig(server_address='https://net.ton.dev'),
        # network=NetworkConfig(server_address='http://localhost'),
    ),
    is_async=True,
)


async def init_test_data():
    test_contract1 = TestContract()
    test_contract2 = TestContract()


    keypair = await client.crypto.generate_random_sign_keys()     

    await test_contract1.create(
        './off-chain/test_fetch',
        'TestContract',
        client=client,
        keypair=keypair,
        initial_data={
            'payload': 8,
        }
    )

    await test_contract2.create(
        './off-chain/test_fetch',
        'TestContract',
        client=client,
        keypair=keypair,
        initial_data={
            'payload': 9,
        }
    )

    await send_tons_with_se_giver(
        await test_contract1.address(),
        10 ** 11,
        os.path.join(os.path.dirname(__file__), 'multisig_artifacts')
    )
    await send_tons_with_se_giver(
        await test_contract2.address(),
        10 ** 11,
        os.path.join(os.path.dirname(__file__), 'multisig_artifacts')
    )

    await test_contract1.deploy()
    await test_contract2.deploy()


async def query_accounts(code_hash: str):
    query_params = ParamsOfQueryCollection(
        collection='accounts',
        result='id,data',
        filter={
            'code_hash': {
                'eq': code_hash,
            },
        },
    )
    result = await client.net.query_collection(params=query_params)
    return result.result


def load_filters_json(file_path: str):
    filters = dict()
    with open(file_path) as json_file:
        filters = json.load(json_file)
    return filters


async def main():
    # await init_test_data()

    tvc_path = sys.argv[1]
    abi_path = sys.argv[2]
    filters_path = sys.argv[3]

    code_hash = await get_contract_code_hash(
        os.path.join(os.path.dirname(__file__), tvc_path)
    )

    query_res = await query_accounts(code_hash)

    filters = load_filters_json(filters_path)

    addresses = []

    for account in query_res:
        decoded_data = await decode_account_data(
            account['data'],
            os.path.join(os.path.dirname(__file__), abi_path),
        )

        filtered_field = None
        filtered_value = None

        for field, value in filters.items():
            if decoded_data.get(field) != value:
                filtered_field = field
                filtered_value = decoded_data.get(field)
                break

        if not filtered_field:
            addresses.append(account['id'])

    for addr in addresses:
        print(addr)


if __name__ == '__main__':
    asyncio.run(main())




# Нужен virtualenv:
# python3 -m venv .venv
# source .venv/bin/activate
# pip install ton-client-py
# pip install aiohttp
#
# Usage
# python3 fetch.py tvc_file_path abi_file_path filters_json_path
#
# Пример запуска
# python3 fetch.py ../Solidity/KWDPool.tvc ../Solidity/KWDPool.abi.json filters.json
# пути к файлам должны быть относительные
