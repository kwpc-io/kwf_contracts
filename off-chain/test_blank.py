import os
import time

import pytest

from contracts import Blank

from conftest import CONTRACTS_BASE_DIR
from conftest import ERRORS



@pytest.mark.asyncio
@pytest.mark.parametrize('lock_time_shift', [-10, 0, 10, 1000])
@pytest.mark.parametrize('unlock_time_shift', [0, 100, 1000])
@pytest.mark.parametrize('kwf_lock_time_shift', [100, 1000])
async def test_blank_deploy(
    create_and_deploy, fetch_recent_transactions, contract_code_hash,
    lock_time_shift, unlock_time_shift, kwf_lock_time_shift,
):
    now = int(time.time())  # seconds

    #  do this smarter
    expected_error = False
    expected_error_code = 0

    # TODO: add min and max summa, quant and farm_rate parameters
    # Maybe separate test?

    if lock_time_shift <= 0:
        expected_error = True
        expected_error_code = ERRORS.error_time_too_late
    elif lock_time_shift >= unlock_time_shift:
        expected_error = True
        expected_error_code = ERRORS.error_unlock_time_less_lock
    # only case is if variable not set (uint kwf_lock_time)
    elif now + kwf_lock_time_shift == 0:
        expected_error = True
        expected_error_code = ERRORS.error_kwf_lock_time_not_set
 
    blank = Blank()


    # need to generate classes for static variables from abi

    statics = {
        'lock_time_': now + lock_time_shift,
        'unlock_time_': now + unlock_time_shift,
        'farm_rate_': 1,
        'kwf_lock_time_': now + kwf_lock_time_shift,
        'quant_': 1,
        'nonce_': 0,
    }

    error, deploy_timestamp = await create_and_deploy(
        blank,
        os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity'),
        'Blank',
        statics=statics,
    )

    txs = await fetch_recent_transactions(deploy_timestamp)
    tx = txs[-1]
    if expected_error:
        assert tx['compute']['success'] == False
        assert tx['compute']['exit_code'] == expected_error_code
        return
    
    from_giver_code_hash = await contract_code_hash(CONTRACTS_BASE_DIR, 'FromGiver.tvc')
    kwd_pool_code_hash = await contract_code_hash(CONTRACTS_BASE_DIR, 'KWDPool.tvc')

    before_set_from_giver_code = int(time.time())

    await blank.setFromGiverCode(from_giver_code_hash)

    txs = await fetch_recent_transactions(before_set_from_giver_code)
    tx = txs[-1]
    assert tx['compute']['success'] == True

    before_set_kwd_pool_code_hash = int(time.time())

    await blank.setKWDPoolCodeHash(kwd_pool_code_hash)

    txs = await fetch_recent_transactions(before_set_from_giver_code)
    tx = txs[-1]
    assert tx['compute']['success'] == True


@pytest.mark.asyncio
@pytest.mark.parametrize('farm_rate', [0, 99, 100, 101])
@pytest.mark.parametrize('quant', [0, 10])
@pytest.mark.parametrize('nonce', [0, 10])
async def test_blank_deploy_correct_times(
    create_and_deploy, fetch_recent_transactions, contract_code_hash,
    farm_rate, quant, nonce,
):
    now = int(time.time())  # seconds

    expected_error = False
    expected_error_code = 0

    blank = Blank()

    if not quant > 0:
        expected_error = True
        expected_error_code = ERRORS.error_quant_not_set
    elif farm_rate <= 0 or farm_rate > 100:
        expected_error = True
        expected_error_code = ERRORS.error_rate_not_set

    # need to generate classes for static variables from abi

    statics = {
        'lock_time_': now + 10,
        'unlock_time_': now + 100,
        'farm_rate_': farm_rate,
        'kwf_lock_time_': now + 1000,
        'quant_': quant,
        'nonce_': nonce,
    }

    error, deploy_timestamp = await create_and_deploy(
        blank,
        os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity'),
        'Blank',
        statics=statics,
    )

    txs = await fetch_recent_transactions(deploy_timestamp)
    tx = txs[-1]
    if expected_error:
        assert tx['compute']['success'] == False
        assert tx['compute']['exit_code'] == expected_error_code
        return
    
    after_deploy = int(time.time())


@pytest.mark.asyncio
async def test_blank_setcode(create_and_deploy, contract_code_hash,
    contract_code, fetch_recent_transactions
):
    blank = Blank()

    now = int(time.time())  # seconds

    statics = {
        'lock_time_': now + 10,
        'unlock_time_': now + 100,
        'farm_rate_': 1,
        'kwf_lock_time_': now + 1000,
        'quant_': 1,
        'nonce_': 0,
    }

    error, deploy_timestamp = await create_and_deploy(
        blank,
        os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity'),
        'Blank',
        statics=statics,
    )
    assert not error

    from_giver_code_hash = await contract_code_hash(CONTRACTS_BASE_DIR, 'FromGiver.tvc')

    kwd_pool_code_hash = await contract_code_hash(CONTRACTS_BASE_DIR, 'KWDPool.tvc')

    fund_code = await contract_code(CONTRACTS_BASE_DIR, 'PseudoFund.tvc')

    before_set_from_giver_code = int(time.time())

    await blank.setFromGiverCode(from_giver_code_hash)

    txs = await fetch_recent_transactions(deploy_timestamp)
    tx = txs[-1]
    if expected_error:
        assert tx['compute']['success'] == True


@pytest.mark.asyncio
async def test_blank_finalize(
    create_and_deploy, fetch_recent_transactions, contract_code_hash,
):
    blank = Blank()

    now = int(time.time())  # seconds

    addresses = []

    statics = {
        'lock_time_': now + 10,
        'unlock_time_': now + 100,
        'farm_rate_': 1,
        'kwf_lock_time_': now + 1000,
        'quant_': 1,
        'nonce_': 0,
    }

    error, deploy_timestamp = await create_and_deploy(
        blank,
        os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity'),
        'Blank',
        statics=statics,
    )
    assert not error

    before_finalize = int(time.time())

    for addr in addresses:
        await blank.finalize(False, addr)

    txs = await fetch_recent_transactions(deploy_timestamp)
    for tx in txs:
        assert tx['compute']['success'] == True
