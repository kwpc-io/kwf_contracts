import asyncio
import json
import os
import sys
import time

from utils import client
from utils import get_contract_code_hash
from utils import send_tons_with_multisig
from utils import send_tons_with_se_giver

from contracts import Blank


async def main():

    blank = Blank()

    now = int(time.time())  # seconds
    statics = {
        'lock_time_': now + 100,
        'unlock_time_': now + 1000,
        'farm_rate_': 1,
        'kwf_lock_time_': 1000,
        'quant_': 1,
        'nonce_': 0,
    }

    await blank.create(
        os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity'),
        'Blank',
        client=client,
        initial_data=statics
    )

    await send_tons_with_se_giver(
        await blank.address(),
        10 ** 11,
        os.path.join(os.path.dirname(__file__), 'multisig_artifacts')
    )

    await blank.deploy()


    from_giver_code_hash = await get_contract_code_hash(
        os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity/FromGiver.tvc'),
    )

    await blank.setFromGiverCode(from_giver_code_hash)

    kwd_pool_code_hash = await get_contract_code_hash(
        os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity/KWDPool.tvc'),
    )

    await blank.setKWDPoolCodeHash(from_giver_code_hash)



    # await blank.deployFromGiver()
    

if __name__ == '__main__':
    asyncio.run(main())
