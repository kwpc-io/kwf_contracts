
pragma ton-solidity >=0.54.0;

interface IBlank {

//constructor (uint128 x1 , uint128 x2) external ;
function notifyLeft (uint128 x1 , uint128 x2 , uint256 x3 , uint x4) external ;
function notifyRight (uint256 x1 , uint128 x2 , address x3) external ;
function acknowledgeFinalizeRight (address x1) external ;
function acknowledgeFinalizeLeft (uint128 x1 , uint256 x2 , uint x3) external ;
}
<<<<<<< HEAD

=======
>>>>>>> 2b696b229d23fd8db25d66b8fc12902960bb7d60
