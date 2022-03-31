import contextlib
import os
import time

import pytest

from utils import client
from utils import get_contract_code
from utils import get_contract_code_hash
from utils import query_last_transactions
from utils import send_tons_with_se_giver


CONTRACTS_BASE_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), './Solidity')


class Errors:
    error_not_my_pubkey = 102
    error_not_external_message = 101
    error_balance_too_low = 103
    error_time_too_late = 104
    error_quant_not_set = 105
    error_farm_rate_not_set = 106
    error_msg_value_too_low = 107
    error_not_my_fund = 108
    error_time_not_inside = 109
    error_fund_ready_set = 110
    error_final_address_not_set = 111
    error_balance_not_positive = 112
    error_fund_ready_not_set = 113
    error_time_too_early = 114
    error_not_initialized = 115
    error_initialized = 116
    error_fund_not_set = 117
    error_return_address_is_mine = 118
    error_not_internal_message = 119
    error_cant_initialize = 120
    error_not_my_giver = 121
    error_unlock_time_less_lock = 122
    error_not_my_code = 123
    error_not_my_investor = 124
    error_not_all_ack = 125
    error_giver_not_set = 126
    error_cannot_change_code = 127
    error_sum_too_small = 128
    error_max_summa_less_min = 129
    error_rate_not_set = 130
    error_kwf_lock_time_not_set = 13
    error_already_all_ack = 132

ERRORS = Errors()


@pytest.fixture
def ever_client():
    return client


@pytest.fixture
def send_crystals_se():
    async def _send_crystals(contract, value):
        await send_tons_with_se_giver(
            await contract.address(),
            value,
            os.path.join(os.path.dirname(__file__), 'multisig_artifacts')
        )

    return _send_crystals


@pytest.fixture
def create_and_deploy(ever_client, send_crystals_se):
    async def _create_and_deploy(
        contract,
        base_dir,
        name,
        *args,
        statics=None,
        deploy_crystals=10 ** 11,
        **kwargs,
    ):
        error = None
        timestamp_before_deploy = None
        try:
            await contract.create(
                base_dir,
                name,
                *args,
                client=ever_client,
                initial_data=statics,
                **kwargs,
            )
            await send_crystals_se(contract, deploy_crystals)
            timestamp_before_deploy = int(time.time())
            await contract.deploy()
        except Exception as e:
            error = e
        return error, timestamp_before_deploy

    return _create_and_deploy


@pytest.fixture
def fetch_recent_transactions():
    async def _fetch_tx(timestamp):
        return await query_last_transactions(timestamp)

    return _fetch_tx



@pytest.fixture
def contract_code_hash():
    async def _get_contract_code_hash(dirname, file_name):
        return await get_contract_code_hash(
            os.path.join(dirname, file_name)
        )

    return _get_contract_code_hash


@pytest.fixture
def contract_code():
    async def _get_contract_code(dirname, file_name):
        return await get_contract_code(
            os.path.join(dirname, file_name)
        )
    return _get_contract_code
