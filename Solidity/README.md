<!-----

Yay, no errors, warnings, or alerts!

Conversion time: 0.917 seconds.


Using this Markdown file:

1. Paste this output into your source file.
2. See the notes and action items below regarding this conversion run.
3. Check the rendered output (headings, lists, code blocks, tables) for proper
   formatting and use a linkchecker before you publish this page.

Conversion notes:

* Docs to Markdown version 1.0β33
* Tue Apr 05 2022 11:45:16 GMT-0700 (PDT)
* Source doc: Translated copy of KW-project phase 1. Описание.
----->


*KW-project phase 1.*

*Description.*

**Section I. Blank**

The fund organizer can deploy and administer the Blank contract, which will enable other users to invest in the future fund.

One Blank contract allows you to collect investments from users with one `farm_rate` value (and `kwf_lock_time`  , - generally speaking, it is set independently, but for standard behavior it is connected to the `farm_rate` parameter through an external off-chain interface).

 
***Part 1. Fundraising***
1. The fund organizer starts the deployment of the Blank contract by setting the following parameters as static fields (plus automatically set  `uint256 pubkey` of the owner): 

```
uint32 lock_time_ - the time until investors can deposit funds
uint32 unlock_time_ - the time after which investors can withdraw their funds if the fund failed to start
uint16 farm_rate_ - farming rate from givers in %, no more than MAX_FRAM_RATE
uint32 kwf_lock_time_ - lock time of tokens issued in the second stage, the semantics of this parameter is determined later
uint128 quant_ - amount in Evers corresponding to investments from one KWDPool
uint256 nonce_ - additional contract id
```

and constructor parameters:

```
uint128 min_summa - minimum amount that participants contribute (categorically cumulatively for investors and givers) for the fund to be considered successful
max_summa - maximum amount, not used
```

and providing the contract with an amount of at least `BLANK_MIN_BALANCE` to maintain the contract's performance, at the deployment stage

2. Set the `hashCode` of contract `FromGiver` (function `setFromGiverCodeHash`), which will enable givers to participate in the fund performing farming role for the investors

3. Set the `hashCode` of `KWDPool` contracts (`setKWDPoolCodeHash` function) , which will enable ordinary users to participate in the fund 

4. Deploy `FromGiver` contracts (`deployFromGiver` function) for the givers to perform farming for the fund (see relevant section).

Step 3 must be completed to let investors deploy `KWDPool` contracts to themselves and invest (see KWDPool section part 1). Givers can invest in farming (see section FromGiver part 1), under similar circumstances of step 2. 

_Notes_:

* contributions are accepted until `lock_time`
* after the first deployment of `KWDPool` for this `Blank` changing the `hashCode` of `KWDPool` is not possible
* after the first deployment `FromGiver` for this `Blank` changing the `hashCode` `FromGiver` is not possible

***Part 2. Check of fundraising and voting for contract codes of the 2nd stage of the kw-project***

Given essential differences between the 1st and 2nd phases of the fund, it was decided to migrate by the `setCode` procedure to save the `Blank` address as a future richer contract. To comply with the principle of decentralized decision making, the `setCode` procedure is based on the vote of investors. The SMV (soft majority voting) scheme was adopted as the voting model. The hash of the code of the future contract is taken as the object of voting, the source codes of which must be available for analysis at the time of voting. Users' real funds will be collected from their accounts in the set-coded contract. The current series of contracts guarantees the safety of funds at the original addresses until the moment of `setCode`. 

1. Run the offline script (which calls the `Blank.finalize` for each address of `KWDPool` and `FromGiver` “attached`*`” to this `Blank`) 

    <em>// start will be successful only if <code>lock_time &lt; now &lt; unlock_time_ - TIME_FOR_FUNDS_COLLECTING - MIN_VOTING_TIME</code></em>

”`*`attached” to `Blank` is the `FromGiver` contract if it was deployed from this <code>Blank</code> and the <code>KWDPool</code> contract if it was initialized from it.</em>

Note: If there are not enough funds collected for farming, then at this stage, investors will be returned that part of the funds

2. Each vote is started by `Blank.startVoting` with parameters:

* `uint32 voting_time` - voting duration (when voting is completed  successfully <code>setFundCode<strong> </strong></code>is run or a new voting is launched)
* `uint256 code_hash` - code hash of the future <code>Fund<strong> </strong></code>contract<strong><code>, setFundCode</code></strong> will only happen with the corresponding code	

Launched votes are automatically numbered starting from 0. There can be no more than 255 votes (with indices from 0 to 254). 

_Notes:_

* it can be voted during the corresponding <code>voting_time</code></em>
* <em>voting can be completed positively/negatively until <code>voting_time</code> expires or if there are <code>50+%</code> of the votes for/against</em>

3. After voting is completed, a new voting can be started (function <code>startVoting</code>, which is only available if the previous vote was “No” , but in case of a “positive” voting result, the <code>startVoting</code> is not going to be executed).

4. If the vote is successful then `setFundCode` may be called which moves the project to phase 2.

Notes:

* if the previous vote was “no”, the `setFundCode` is not to be executed
* `setFundCode` must be started before the time `unlock_time_ - TIME_FOR_FUNDS_COLLECTING`
* Requires on the balance of at least `RESPAWN_BALANCE`
* can change the code only to the code voted for

5. If the item 4 has not been successfully completed by the time `unlock_time_ `the` killBlank `function can be called to finish the project and return the remaining funds of the organizer (funds from investors and givers can be freely taken away by original owners by calling the <code>returnFunds<strong> </strong></code>in their contracts).

**Section II. KWDPool**

***Part 1. Fundraising***

From the moment the `Blank` contract is ready (deployed and hash codes set) until `lock_time`, the corresponding `KWDPool` investor can participate in the fund according to the following instruction:

1. Select a `Blank` contract from the existing ones with the required parameters `farm_rate` (and `kwf_lock_time`)
2. Deploy the contract `KWDPool` by setting the following static fields:

* `address` `fund_address_ - Blank` address from p.1
* `uint256 nonce_ - `additional contract id

    and constructor parameters:

* `optional (address) final_address`  - 
can be set both during deployment and after the `setFinalAddress` function, it will be also set automatically upon the first successful deposit to the address when funds were sent


Note: the balance of the contact during deployment must be at least `KWD_MIN_BALANCE+GAS_FOR_FUND_MESSAGE`

3. Top up the balance of the contract for an amount not less than quant_ by a one-time transfer

_Note: excess (exceeding the amount <code>quant_+KWD_MIN_BALANCE</code>) funds can be withdrawn at any time by the</em> <code>returnExtraFunds</code>

***Part 2 Voting***

When the fund organizer opens the voting for a code of the second stage (see section 1 part 2) the investor can take part in it using the <code>vote</code> function with the parameters corresponding to the parameters of the launched voting.

Note:

* all investors’ KWDPools are homogeneous
* repeated vote in the same voting is not accepted
* contract balance should be not less than `quant_ + KWMessages.VOTING_FEE + 3*KWMessages.EPSILON_BALANCE`
* if no voting has a positive result, the project will not be migrated to the second phase and the investor will be able to withdraw their funds after the `unlock_time` expires using the `returnFunds` function 

***Part 3. Collecting of investors’ funds.***

The `KWDPool` and `FromGiver` contracts provide the `sendFunds `function, which may be  called only from the contract with the `Blank` address but not itself (this can be done by the contract in the case of the “correct” setCode) that allows you to transfer funds to the future `KWparticipant` contract to participate in the second stage.

The total amount from the `KWDPool` and `FromGiver` contracts which will be transferred to the `KWparticipant` contract finally is

```
summa_givers/investors_number*(1 + 100/farm_rate)
```

The excess investor funds, excluding funds for servicing future contracts, will be returned (see Section 1 Part 2 p 1 Note).

**Section III. FromGiver**

In order for the second stage of the fund to take place, “givers” must provide funds for farming. To do this, the project organizer must deploy the necessary `FromGiver` contracts (see section 1 part 1).

The giver must replenish the balance of the corresponding `FromGiver` contract, and the funds must be credited from the `giver_address_ `specified in the contract until the `lock_time_`.

If the launch of the second stage of the fund will not take place after the `unlock_time` expires, the funds can be returned to the appropriate address  `giver_address_` by running the `returnFunds` public function in the corresponding contract `FromGiver`.

_______________

**MANAGING FUNCTIONS**

***Blank***

```
constructor (uint128 min_summa , uint128 max_summa)
function setFromGiverCodeHash (uint256 code_hash, uint16 code_depth)
function setKWDPoolCodeHash (uint256 code_hash, uint16 code_depth)
function deployFromGiver (TvmCell code , address giver, uint256 nonce)
function finalize (bool force_giveup, address addr)
function setFundCode (TvmCell code)
function startVoting (uint32 voting_time, uint256 code_hash)
function killBlank (address address_to)
```


***KWDPool***

```
constructor (optional (address) final_address)
receive()
function setFinalAddress (address final_address)
function returnFunds (address address_to)
function returnExtraFunds (address address_to)
function vote (bool choice, uint8 voting_id, uint256 code_hash)
```

***FromGiver***

```
receive()
function returnFunds()
```


	
