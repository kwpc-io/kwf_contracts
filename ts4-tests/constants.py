import subprocess


bashCommand = 'bash ../Solidity/gethash.sh ../Solidity/FromGiver.tvc'
process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
output, _ = process.communicate()
FROM_GIVER_CODE = '0x' + output.decode('ascii')

bashCommand = 'bash ../Solidity/getdepth.sh ../Solidity/FromGiver.tvc'
process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
output, _ = process.communicate()
FROM_GIVER_CODE_DEPTH = int(output.decode('ascii'))

bashCommand = 'bash ../Solidity/gethash.sh ../Solidity/KWDPool.tvc'
process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
output, _ = process.communicate()
KWDPOOL_CODE_HASH = '0x' + output.decode('ascii')

bashCommand = 'bash ../Solidity/getdepth.sh ../Solidity/KWDPool.tvc'
process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
output, _ = process.communicate()
KWDPOOL_CODE_DEPTH = int(output.decode('ascii'))

bashCommand = 'bash ../Solidity/gethash.sh ../Solidity/PseudoFund.tvc'
process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
output, _ = process.communicate()
PSEUDOFUND_CODE_HASH = '0x' + output.decode('ascii')

# bashCommand = 'bash ../Solidity/getdepth.sh ../Solidity/PseudoFund.tvc'
# process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
# output, _ = process.communicate()
# PSEUDOFUND_CODE_DEPTH = int(output.decode('ascii'))

BLANK_MIN_BALANCE = 20 * 10**9
RESPAWN_BALANCE = 50 * 10**9
EPSILON_BALANCE = 5 * 10**8
GAS_FOR_PARTICIPANT_MESSAGE = 5 * 10**8

KWD_MIN_BALANCE = 5 * 10**9
GAS_FOR_FUND_MESSAGE = 5 * 10**8

FG_MIN_BALANCE = 5 * 10**9

ALL_BALANCE_MSG_FLAG = 128
DEFAULT_MSG_FLAGS = 0
MSG_VALUE_BUT_FEE_FLAGS = 64

error_not_external_message = 101
error_not_my_pubkey = 102
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
error_kwf_lock_time_not_set = 131
error_already_all_ack = 132
