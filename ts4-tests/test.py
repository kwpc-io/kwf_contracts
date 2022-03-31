import time
from typing import List, Tuple

import pytest
import tonos_ts4.ts4 as ts4

from kw_ts4 import Blank, KWDPool, PseudoFund, FromGiver
from common_contracts import SafeMultisig
from constants import *


HUGE_START_BALANCE = 2 ** 63 - 1


def call_all_getters(contract: ts4.BaseContract):
    return (
        contract.call_getter('kwdpool_code_hash_'),
        contract.call_getter('kwdpool_code_depth_'),
        contract.call_getter('fromgiver_code_hash_'),
        contract.call_getter('fromgiver_code_depth_'),

        contract.call_getter('givers_summa_'),
        contract.call_getter('investors_adj_summa_'),
        contract.call_getter('investors_summa_'),
        contract.call_getter('min_summa_'),
        contract.call_getter('max_summa_'),

        contract.call_getter('lock_time_'),
        contract.call_getter('unlock_time_'),
        contract.call_getter('farm_rate_'),
        contract.call_getter('kwf_lock_time_'),
        contract.call_getter('quant_'),
        contract.call_getter('nonce_'),
    )


@pytest.mark.parametrize(
    argnames=[
        'quant',
        'nonce',

        'lock_time',
        'unlock_time',
        'kwf_lock_time',

        'farm_rate',

        'number_of_kwdpools',
        'number_of_from_givers',
        'from_givers_balance',

        'min_summa',
        'max_summa',

        'required_amount_collected',
        'set_fund_code',

        'voting_time',
        'voting_successful',
        'more_than_50',
        'voted_for',
        'voted_against',
    ],
    argvalues=[
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            100,
            1,
            2000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            False,
            False,
            10,
            0,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            100,
            1,
            2000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            False,
            11,
            0,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            100,
            1,
            2000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            False,
            False,
            20,
            13,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            100,
            1,
            2000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            False,
            21,
            12,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            100,
            1,
            2000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            False,
            20,
            12,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            11,
            1,
            2000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            True,
            6,
            5,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            11,
            1,
            2000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            False,
            False,
            5,
            5,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            2,
            1,
            20 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            True,
            2,
            0,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            3,
            1,
            30 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            False,
            1,
            0,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            3,
            1,
            30 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            False,
            True,
            0,
            3,
        ),
        (
            10 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            80,

            3,
            1,
            30 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            False,
            False,
            0,
            0,
        ),
        (
            1000 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            1,

            1,
            1,
            2001 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            True,
            1,
            0,
        ),
        (
            1000 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            50,

            1,
            1,
            2001 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            True,
            1,
            0,
        ),
        (
            100 * 10**9,
            100500,

            100,
            604800 * 10,
            100,

            1,

            10,
            10,
            101 * 10**9,

            1000 * 10**9,
            1000000 * 10**9,

            True,
            True,

            604800 + 1,
            True,
            True,
            10,
            0,
        ),
        (
            1000 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            1,

            5,
            2,
            1000 * 10**9,

            10 * 10**9,
            1000000 * 10**9,

            True,
            False,
            604800 + 1,
            True,
            True,
            2,
            0,
        ),
        (
            1000 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            1,

            5,
            2,
            25 * 10**9,

            1000 * 10**9,
            1000000 * 10**9,

            False,
            True,

            604800 + 1,
            True,
            True,
            2,
            0,
        ),
        (
            1000 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            1,

            1,
            1,
            999 * 10**9,

            1000 * 10**9,
            1000000 * 10**9,

            False,
            True,
            604800 + 1,
            True,
            True,
            1,
            0,
        ),
        (
            1000 * 10**9,
            1,

            100,
            604800 * 10,
            100,

            1,

            1,
            1,
            999 * 10**9,

            1000 * 10**9,
            1000000 * 10**9,

            False,
            False,

            604800 + 1,
            True,
            True,
            1,
            0,
        ),
    ],
)
def test_basic_scenario(
        quant, nonce,
        lock_time, unlock_time, kwf_lock_time,
        farm_rate,
        number_of_kwdpools, number_of_from_givers, from_givers_balance,
        min_summa, max_summa,
        required_amount_collected, set_fund_code,
        voting_time, voting_successful, more_than_50, voted_for, voted_against,
        pytestconfig
    ):
    ts4.reset_all()
    rootpath = pytestconfig.rootpath
    ts4.init(rootpath.joinpath('../Solidity/'), verbose=False)

    now = int(time.time())
    lock_time += now
    unlock_time += now
    kwf_lock_time += now


    # Деплоим контракт(ы) Blank
    blank = Blank(
        min_summa=min_summa,
        max_summa=max_summa,
        lock_time_=lock_time,
        unlock_time_=unlock_time,
        farm_rate_=farm_rate,
        kwf_lock_time_=kwf_lock_time,
        quant_=quant,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE + (FG_MIN_BALANCE + 2*EPSILON_BALANCE + 10**9) * number_of_from_givers,
    )
    ts4.dispatch_messages()


    # пытаемся деплоить Blank с не корректными параметрами
    Blank(
        min_summa=min_summa,
        max_summa=max_summa,
        lock_time_=lock_time,
        unlock_time_=unlock_time,
        farm_rate_=farm_rate,
        kwf_lock_time_=kwf_lock_time,
        quant_=quant,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE - 10**9,
        error_code=error_balance_too_low,
    )
    ts4.dispatch_messages()

    Blank(
        min_summa=min_summa,
        max_summa=max_summa,
        lock_time_=now - 1,
        unlock_time_=unlock_time,
        farm_rate_=farm_rate,
        kwf_lock_time_=kwf_lock_time,
        quant_=quant,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE + 10**9,
        error_code=error_time_too_late,
    )
    ts4.dispatch_messages()

    Blank(
        min_summa=2,
        max_summa=1,
        lock_time_=lock_time,
        unlock_time_=unlock_time,
        farm_rate_=farm_rate,
        kwf_lock_time_=kwf_lock_time,
        quant_=quant,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE + 10**9,
        error_code=error_max_summa_less_min,
    )
    ts4.dispatch_messages()

    Blank(
        min_summa=min_summa,
        max_summa=max_summa,
        lock_time_=unlock_time,
        unlock_time_=lock_time,
        farm_rate_=farm_rate,
        kwf_lock_time_=kwf_lock_time,
        quant_=quant,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE + 10**9,
        error_code=error_unlock_time_less_lock,
    )
    ts4.dispatch_messages()

    Blank(
        min_summa=min_summa,
        max_summa=max_summa,
        lock_time_=lock_time,
        unlock_time_=unlock_time,
        farm_rate_=farm_rate,
        kwf_lock_time_=kwf_lock_time,
        quant_=0,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE + 10**9,
        error_code=error_quant_not_set,
    )
    ts4.dispatch_messages()

    Blank(
        min_summa=min_summa,
        max_summa=max_summa,
        lock_time_=lock_time,
        unlock_time_=unlock_time,
        farm_rate_=0,
        kwf_lock_time_=kwf_lock_time,
        quant_=quant,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE + 10**9,
        error_code=error_rate_not_set,
    )
    ts4.dispatch_messages()

    Blank(
        min_summa=min_summa,
        max_summa=max_summa,
        lock_time_=lock_time,
        unlock_time_=unlock_time,
        farm_rate_=farm_rate,
        kwf_lock_time_=0,
        quant_=quant,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=BLANK_MIN_BALANCE + 10**9,
        error_code=error_kwf_lock_time_not_set,
    )
    ts4.dispatch_messages()


    # задаем переменные контракта Blank (Blank.setFromGiverCode, Blank.setKWDPoolCodeHash)
    #сначала мусорные
    blank.setFromGiverCode('0x' + '0' * 64, 0)
    blank.setKWDPoolCodeHash('0x' + '0' * 64, 0)
    ts4.dispatch_messages()
    # потом корректные
    blank.setFromGiverCode(FROM_GIVER_CODE, FROM_GIVER_CODE_DEPTH)
    blank.setKWDPoolCodeHash(KWDPOOL_CODE_HASH, KWDPOOL_CODE_DEPTH)
    ts4.dispatch_messages()


    # Деплоим контракт(ы) FromGiver из Blank (Blank.deployFromGiver)
    from_giver_code = ts4.load_code_cell('FromGiver')
    wallet = SafeMultisig(HUGE_START_BALANCE)
    final_wallet = SafeMultisig(HUGE_START_BALANCE)
    givers = [SafeMultisig(HUGE_START_BALANCE) for _ in range(number_of_from_givers)]
    giver_pairs: List[Tuple[SafeMultisig, ts4.Address]] = [
        (
            giver,
            blank.deployFromGiver(
                code=from_giver_code,
                giver=giver.address,
                nonce=nonce,
            )
        ) for giver in givers
    ]
    ts4.dispatch_messages()

    # Деплоим контракт(ы) FromGiver не корректными способами
    blank.deployFromGiver(
        code=from_giver_code,
        giver=ts4.Address('0:' + '0'*64),
        nonce=nonce,
        error_code=error_giver_not_set,
    )
    ts4.dispatch_messages()

    blank.deployFromGiver(
        code=ts4.load_code_cell('SafeMultisigWallet'),
        giver=ts4.Address('0:' + '0'*63 + '1'),
        nonce=nonce,
        error_code=error_not_my_code,
    )
    ts4.dispatch_messages()


    # Пытаемся перезадать код FromGiver
    blank.setFromGiverCode('0x' + '0' * 64, 0, error_cannot_change_code)


    # Деплоим контракт(ы) KWDpool
    kwdpools = [
        KWDPool(
            final_address=final_wallet.address,
            fund_address_=blank.address,
            nonce_=nonce,
            keypair=ts4.make_keypair(),
            balance=KWD_MIN_BALANCE + GAS_FOR_FUND_MESSAGE + 10**9,
        ) for _ in range(number_of_kwdpools)
    ]
    ts4.dispatch_messages()

    # Деплоим контракт(ы) KWDpool c ошибками
    KWDPool(
        final_address=ts4.Address('0:' + '0' * 64),
        fund_address_=blank.address,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=KWD_MIN_BALANCE + GAS_FOR_FUND_MESSAGE - 1,
        error_code=error_balance_too_low,
    )
    ts4.dispatch_messages()

    KWDPool(
        final_address=ts4.Address('0:' + '0' * 64),
        fund_address_=ts4.Address('0:' + '0' * 64),
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=KWD_MIN_BALANCE + GAS_FOR_FUND_MESSAGE + 10 ** 9,
        error_code=error_fund_not_set,
    )
    ts4.dispatch_messages()


    # Пытаемся перезадать хеш KWDPool
    blank.setKWDPoolCodeHash('0x' + '0' * 64, 0, error_cannot_change_code)


    # Пересылаем деньги на задеплоенные KWDpool’ы
    for pool in kwdpools:
        # шлём слишком мало
        balance_before = pool.balance
        wallet.send_transaction(
            dest=pool.address,
            value=quant - 1,
        )
        ts4.dispatch_one_message(expect_ec=error_msg_value_too_low)
        delta = abs(balance_before - pool.balance)
        assert delta < EPSILON_BALANCE

        # шлём слишком много
        balance_before = pool.balance
        wallet.send_transaction(
            dest=pool.address,
            value=quant * 2,
        )
        ts4.dispatch_messages()
        delta = abs(balance_before - pool.balance)
        assert abs(delta - quant) < EPSILON_BALANCE

    # может отдать деньги если не инициализирован Blank'ом
    pool_ = KWDPool(
        final_address=ts4.Address('0:' + '0' * 64),
        fund_address_=blank.address,
        nonce_=nonce,
        keypair=ts4.make_keypair(),
        balance=KWD_MIN_BALANCE + 10**9,
    )
    pool_.return_funds(wallet.address)
    # не может отдать деньги до unlock_time (проверить что unlock_time_ совпадает с соответствующей переменной Blank) ✔
    # может отдать деньги после unlock_time (не верно если фонд запущен!) ✔
    # проверить что не переводит деньги самому себе перед уничтожением ✔

    ts4.dispatch_messages()


    # Пересылаем деньги на задеплоенные FromGiver’ы
    for giver_, from_giver_address_ in giver_pairs:
        # - принимает любые суммы (более min) несколькими транзакциями ✔
        # - не отдает деньги раньше unlock_time_ ✔
        # - отдает деньги после unlock_time_ (не верно если фонд запущен!) ✔
        giver_.send_transaction(from_giver_address_, from_givers_balance // 2 + 1)
        ts4.dispatch_messages()
        giver_.send_transaction(from_giver_address_, from_givers_balance // 2 + 1)
        ts4.dispatch_messages()

    ts4.core.set_now(lock_time + 1)
    # деплоим from_giver слишком поздно
    blank.deployFromGiver(
        code=from_giver_code,
        giver=ts4.Address('0:' + '0'*63 + '1'),
        nonce=nonce,
        error_code=error_time_too_late,
    )

    # запускаем “скрипт опроса” (запуск функции Blank.finalize по каждому адресу KWDPool и FromGiver “привязанных”* к этому Blank) //запуск будет успешен только при lock_time<now<unlock_time
    summa_givers = from_givers_balance * number_of_from_givers
    summa_investors = quant * number_of_kwdpools * farm_rate // 100

    GIVERS_EXTRA_EXPECTED = from_givers_balance * (summa_givers - summa_investors) // summa_givers
    if GIVERS_EXTRA_EXPECTED < 0:
        GIVERS_EXTRA_EXPECTED = 0
    for giver_, from_giver_address_ in giver_pairs:
        givers_balance_before_ = giver_.balance
        blank.finalize(False, from_giver_address_)
        ts4.dispatch_messages()
        if required_amount_collected:
            givers_extra = giver_.balance - givers_balance_before_
            assert abs(givers_extra - GIVERS_EXTRA_EXPECTED) < EPSILON_BALANCE
        else:
            assert ts4.get_balance(from_giver_address_) is None

    ts4.dispatch_messages()

    KWD_EXTRA = quant * (summa_investors - summa_givers) // summa_investors
    if KWD_EXTRA < 0:
        KWD_EXTRA = 0
    for pool in kwdpools:
        if required_amount_collected:
            kwd_balance_before_ = pool.balance
            blank.finalize(False, pool.address)
            ts4.dispatch_messages()
            assert abs(pool.balance - kwd_balance_before_ - KWD_EXTRA) < EPSILON_BALANCE
        else:
            final_balance_before_ = final_wallet.balance
            pool_balance_before = pool.balance
            blank.finalize(False, pool.address)
            ts4.dispatch_messages()
            assert abs(final_wallet.balance - final_balance_before_ - pool_balance_before) < EPSILON_BALANCE


    # ПРОГРАММИРОВАТЬ СЮДА
    if required_amount_collected:
        blank.startVoting(voting_time, PSEUDOFUND_CODE_HASH)
        voting_id = blank.call_getter('voting_id_')

        for i in range(voted_for):
            kwdpools[i].vote(True, voting_id, PSEUDOFUND_CODE_HASH)

        for i in range(voted_against):
            kwdpools[voted_for + i].vote(False, voting_id, PSEUDOFUND_CODE_HASH)

        # пополняем баланс Blank (следующий пункт требует значительной суммы на балансе контракта для успешного выполнения)
        for _, from_giver_address_ in giver_pairs:
            assert ts4.get_balance(from_giver_address_)
        wallet.send_transaction(blank.address, RESPAWN_BALANCE)
        ts4.dispatch_messages()


        # Модернизируем Blank в PseudoFund (Blank.setFundCode)
        if set_fund_code:
            vars = call_all_getters(blank)
            fund_code = ts4.load_code_cell('PseudoFund')
            blank.setFundCode(fund_code)
            ts4.dispatch_messages()
            if voting_successful and more_than_50:
                fund = PseudoFund(blank.address, blank.keypair)
                assert fund.call_getter('code_updated') is True
            else:
                assert blank.call_getter('code_updated') is False

            if voting_successful and not more_than_50:
                ts4.core.set_now(lock_time + voting_time + 2)
                assert blank.call_getter('code_updated') is False
                blank.setFundCode(fund_code)
                ts4.dispatch_messages()
                fund = PseudoFund(blank.address, blank.keypair)
                assert fund.call_getter('code_updated') is True

            if voting_successful:
                assert vars == call_all_getters(fund)

    if not voting_successful and required_amount_collected and set_fund_code:
        # ALL VOTE FOR
        if not more_than_50:
            ts4.core.set_now(lock_time + voting_time + 2)
        blank.startVoting(voting_time, PSEUDOFUND_CODE_HASH)
        voting_id = blank.call_getter('voting_id_')

        for kwdpool in kwdpools:
            kwdpool.vote(True, voting_id, PSEUDOFUND_CODE_HASH)

        # пополняем баланс Blank (следующий пункт требует значительной суммы на балансе контракта для успешного выполнения)
        for _, from_giver_address_ in giver_pairs:
            assert ts4.get_balance(from_giver_address_)
        wallet.send_transaction(blank.address, RESPAWN_BALANCE)
        ts4.dispatch_messages()


        # Модернизируем Blank в PseudoFund (Blank.setFundCode)
        fund_code = ts4.load_code_cell('PseudoFund')
        blank.setFundCode(fund_code)
        ts4.dispatch_messages()
        fund = PseudoFund(blank.address, blank.keypair)
        assert fund.call_getter('code_updated') is True


    if set_fund_code and required_amount_collected:

        # Собираем деньги со всех “привязанных”* к этому Blank контрактов KWDPool и FromGiver (PseudoFund.getFunds)(может быть использован скрипт из пункта g)
        fund_balance_before = fund.balance
        from_giver_balance = 0

        for _, from_giver_address_ in giver_pairs:
            from_giver_balance += ts4.get_balance(from_giver_address_)
            fund.getFromGiverFunds(from_giver_address_)
            ts4.dispatch_messages()

        for pool in kwdpools:
            fund.transferFundsTo(pool.address, from_giver_code)
            ts4.dispatch_messages()

        fund_balance_delta = fund.balance - fund_balance_before

        # Проверяем что все деньги собраны (если farm_rate*quant*(кол-во KWDPool) < суммы балансов FromGiver’ов, то собранная сумма равна (1+farm_rate)*quant*(кол-во KWDPool). Иначе если farm_rate*quant*(кол-во KWDPool) > суммы балансов FromGiver’ов, то собранная сумма равна (1+farm_rate)*(сумма балансов FromGiver’ов)
        assert fund_balance_delta - (1 + farm_rate / 100) * min(quant * len(kwdpools), from_giver_balance) >= 0


    # проверяем возврат в случае несоздания Fund
    ts4.core.set_now(unlock_time + 1)
    if not set_fund_code and required_amount_collected:
        for pool_ in kwdpools:
            pools_balance_before_refund = pool_.balance
            wallets_balance_before_refund = wallet.balance
            pool_.return_funds(wallet.address)
            ts4.dispatch_messages()

            assert pool_.balance is None
            assert wallet.balance - wallets_balance_before_refund - pools_balance_before_refund < EPSILON_BALANCE

        for giver_, from_giver_address_ in giver_pairs:
            from_giver_ = FromGiver(from_giver_address_)
            from_giver_.return_funds()
            ts4.dispatch_messages()
            assert from_giver_.balance is None
