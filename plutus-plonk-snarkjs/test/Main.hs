{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE OverloadedStrings  #-}

module Main (main) where

import qualified PlutusTx.Prelude as P
import qualified PlutusTx.Builtins as P
import Plutus.Crypto.BlsField ( Scalar (..), mkScalar, reverseByteString )
import Plutus.Crypto.Plonk (Proof (..), PreInputs (..), ProofFast (..)
                           , PreInputsFast (..), convertToFastProof
                           , convertToFastPreInputs, verifyPlonk, verifyPlonkSnarkjs)

import ReadSnarkjs ( ProofJSONSnarkjs(..), PreInputsJSONSnarkjs(..) )

import Data.Aeson ( FromJSON, ToJSON, decode )
import GHC.Generics ( Generic )

import qualified Data.ByteString.Lazy as BL
import Data.ByteString ( pack )
import Data.Word ()
import Bitwise (writeBitByteString)
import PlutusTx.Builtins (bls12_381_G1_zero)
import qualified PlutusCore as P

-- Create a quick type for importing a test vector Proof via JSON.
data ProofJSON = ProofJSON
    { commitment_a :: [Integer]
    , commitment_b :: [Integer]
    , commitment_c :: [Integer]
    , commitment_z :: [Integer]
    , t_low        :: [Integer]
    , t_mid        :: [Integer]
    , t_high       :: [Integer]
    , w_omega      :: [Integer]
    , w_omega_zeta :: [Integer]
    , a_eval       :: [Integer]
    , b_eval       :: [Integer]
    , c_eval       :: [Integer]
    , s_sig1       :: [Integer]
    , s_sig2       :: [Integer]
    , z_omega      :: [Integer]
} deriving (Show, Generic)

instance FromJSON ProofJSON
instance ToJSON ProofJSON

-- Create a quick type for importing a test vector PreInputs via JSON.
data PreInputsJSON = PreInputsJSON
    { n_public      :: Integer
    , pow           :: Integer
    , k_1           :: [Integer]
    , k_2           :: [Integer]
    , q_m           :: [Integer]
    , q_l           :: [Integer]
    , q_r           :: [Integer]
    , q_o           :: [Integer]
    , q_c           :: [Integer]
    , s_sig1_pre_in :: [Integer]
    , s_sig2_pre_in :: [Integer]
    , s_sig3_pre_in :: [Integer]
    , x_2           :: [Integer]
    , gen           :: [Integer]
} deriving (Show, Generic)

instance FromJSON PreInputsJSON
instance ToJSON PreInputsJSON

convertIntegersByteString :: [Integer] -> P.BuiltinByteString
convertIntegersByteString n =  P.toBuiltin . pack $ Prelude.map fromIntegral n

convertMontgomery :: [Integer] -> Integer
convertMontgomery [a, b, c, d] = a + b * 2^64 + c * 2^128 + d * 2^192
convertMontgomery _ = 0

convertProof :: ProofJSON -> Proof
convertProof proof = Proof
    { commitmentA = convertIntegersByteString $ commitment_a proof
    , commitmentB = convertIntegersByteString $ commitment_b proof
    , commitmentC = convertIntegersByteString $ commitment_c proof
    , commitmentZ = convertIntegersByteString $ commitment_z proof
    , tLow        = convertIntegersByteString $ t_low proof
    , tMid        = convertIntegersByteString $ t_mid proof
    , tHigh       = convertIntegersByteString $ t_high proof
    , wOmega      = convertIntegersByteString $ w_omega proof
    , wOmegaZeta  = convertIntegersByteString $ w_omega_zeta proof
    , aEval       = convertMontgomery $ a_eval proof
    , bEval       = convertMontgomery $ b_eval proof
    , cEval       = convertMontgomery $ c_eval proof
    , sSig1P      = convertMontgomery $ s_sig1 proof
    , sSig2P      = convertMontgomery $ s_sig2 proof
    , zOmega      = convertMontgomery $ z_omega proof
}

convertPreInputs :: PreInputsJSON -> PreInputs
convertPreInputs preIn = PreInputs
    { nPublic   = n_public preIn
    , power     = pow preIn
    , k1        = mkScalar . convertMontgomery $ k_1 preIn
    , k2        = mkScalar . convertMontgomery $ k_2 preIn
    , qM        = P.bls12_381_G1_uncompress . convertIntegersByteString $ q_m preIn
    , qL        = P.bls12_381_G1_uncompress . convertIntegersByteString $ q_l preIn
    , qR        = P.bls12_381_G1_uncompress . convertIntegersByteString $ q_r preIn
    , qO        = P.bls12_381_G1_uncompress . convertIntegersByteString $ q_o preIn
    , qC        = P.bls12_381_G1_uncompress . convertIntegersByteString $ q_c preIn
    , sSig1     = P.bls12_381_G1_uncompress . convertIntegersByteString $ s_sig1_pre_in preIn
    , sSig2     = P.bls12_381_G1_uncompress . convertIntegersByteString $ s_sig2_pre_in preIn
    , sSig3     = P.bls12_381_G1_uncompress . convertIntegersByteString $ s_sig3_pre_in preIn
    , x2        = P.bls12_381_G2_uncompress . convertIntegersByteString $ x_2 preIn
    , generator = mkScalar . convertMontgomery $ gen preIn
    }



convertIntG1ToBS :: (Integer, Integer) -> P.BuiltinByteString
convertIntG1ToBS (x,y)
    | x == 0 && y == 1                  = P.bls12_381_G1_compress P.bls12_381_G1_zero
    | P.lengthOfByteString xBs == 48    = go xBs y
    | otherwise                         = go (pad xBs) y
        where p = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
              xBs = P.integerToByteString x
              xBsG1 x = reverseByteString (P.writeBitByteString x 7 True)
              go :: P.BuiltinByteString -> Integer -> P.BuiltinByteString
              go x y
                | y < (p-y) `mod` p = P.bls12_381_G1_compress . P.bls12_381_G1_uncompress $ xBsG1 x
                | otherwise         = P.bls12_381_G1_compress . P.bls12_381_G1_neg . P.bls12_381_G1_uncompress $ xBsG1 x
              pad :: P.BuiltinByteString -> P.BuiltinByteString
              pad x = x <> P.consByteString 0 P.emptyByteString

-- this function is wrong (not sure yet how to handle the concatenation of two 384 bit integers) in the field F(q^2) of G2.
-- Maybe the metric is just quadratic addition?
convertIntG2ToBS :: (Integer, (Integer,Integer)) -> P.BuiltinByteString
convertIntG2ToBS (x,(y1,y2))
    | x == 0 && y == 1  = P.bls12_381_G2_compress P.bls12_381_G2_zero
    | otherwise         = if P.lengthOfByteString xBs == 96
                          then go xBs y
                          else go (pad xBs) y
        where y = y1 + y2 * 2^384
              p = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
              xBs = P.integerToByteString x
              xBsG1 x = reverseByteString (P.writeBitByteString x 7 True)
              go :: P.BuiltinByteString -> Integer -> P.BuiltinByteString
              go x y
              -- not sure if this will be correct as y > p (y is two concatenated ~384 bit integers)
              -- so y < (p-y) `mod` p will always be false
                | y < (p-y) `mod` p = xBsG1 x
                | otherwise         = xBsG1 x
              pad :: P.BuiltinByteString -> P.BuiltinByteString
              pad x = x <> P.consByteString 0 P.emptyByteString

convertPreInputsSnarkjs :: PreInputsJSONSnarkjs -> PreInputs
convertPreInputsSnarkjs preIn =
    let g :: [String] -> (Integer, Integer)
        g (x:y:xs) = (read x, read y)
        f = P.bls12_381_G1_uncompress . convertIntG1ToBS . g
        h x = read x :: Integer
        ((x1:x2:xs):(y1:y2:ys):xys) = x_2' preIn
        xInt :: Integer
        xInt = read x1 + read x2 * 2^384
        yInt :: (Integer, Integer)
        yInt = (read y1,read y2)
    in PreInputs
    { nPublic   = nPublic' preIn
    , power     = power' preIn
    , k1        = mkScalar . h $ k_1' preIn
    , k2        = mkScalar . h $ k_2' preIn
    , qM        = f $ qm preIn
    , qL        = f $ ql preIn
    , qR        = f $ qr preIn
    , qO        = f $ qo preIn
    , qC        = f $ qc preIn
    , sSig1     = f $ s1 preIn
    , sSig2     = f $ s2 preIn
    , sSig3     = f $ s3 preIn
    , x2        = P.bls12_381_G2_uncompress . convertIntG2ToBS $ (xInt, yInt)
    , generator = mkScalar . h $ w preIn
    }

convertProofSnarkjs :: ProofJSONSnarkjs -> Proof
convertProofSnarkjs proof =
    let g :: [String] -> (Integer, Integer)
        g (x:y:xs) = (read x, read y)
        f = convertIntG1ToBS . g
        h x = read x :: Integer
    in Proof
        { commitmentA = f $ a proof
        , commitmentB = f $ b proof
        , commitmentC = f $ c proof
        , commitmentZ = f $ z proof
        , tLow        = f $ t1 proof
        , tMid        = f $ t2 proof
        , tHigh       = f $ t3 proof
        , wOmega      = f $ wxi proof
        , wOmegaZeta  = f $ wxiw proof
        , aEval       = h $ eval_a proof
        , bEval       = h $ eval_b proof
        , cEval       = h $ eval_c proof
        , sSig1P      = h $ eval_s1 proof
        , sSig2P      = h $ eval_s2 proof
        , zOmega      = h $ eval_zw proof
        }

main :: IO ()
main = do
    jsonDataProof <- BL.readFile "test-vectors/proof-test-vector.json"
    jsonDataPreIn <- BL.readFile "test-vectors/pre-in-test-vector.json"
    jsonDataProofSnarkjs <- BL.readFile "snarkjs-test-vectors/proof.json"
    jsonDataPreInSnarkjs <- BL.readFile "snarkjs-test-vectors/verification_key.json"
    let maybeProof = decode jsonDataProof :: Maybe ProofJSON
    let maybePreIn = decode jsonDataPreIn :: Maybe PreInputsJSON
    let maybeProofSnarkjs = decode jsonDataProofSnarkjs :: Maybe ProofJSONSnarkjs
    let maybePreInSnarkjs = decode jsonDataPreInSnarkjs :: Maybe PreInputsJSONSnarkjs
    case maybeProof of
        Just proof  -> case maybePreIn of
            Just preIn -> do let p = convertProof proof
                             let i = convertPreInputs preIn
                             let iFast = convertToFastPreInputs i
                             let pFast = convertToFastProof iFast p
                             print $ verifyPlonk iFast [9] pFast
            Nothing -> print "Could not deserialize PreInputs test vector"
        Nothing -> print "Could not deserialize Proof test vector"
    case maybeProofSnarkjs of
        Just proofSnarkjs -> case maybePreInSnarkjs of
            Just preInSnarkjs -> do let i = convertPreInputsSnarkjs preInSnarkjs
                                    let p = convertProofSnarkjs proofSnarkjs
                                    let iFastSnarkjs = convertToFastPreInputs i
                                    let pFastSnarkjs = convertToFastProof iFastSnarkjs p
                                    -- print $ qL i
                                    -- print $ verifyPlonkFast iFastSnarkjs [20] pFastSnarkjs
                                    print $ verifyPlonkSnarkjs i [20] p
            Nothing -> print "Could not deserialize PreInputs test vector snarkjs"
        Nothing -> print "Could not deserialize Proof test vector snarkjs"

                                    -- let f = (\x -> P.writeBitByteString x 7 False ) . reverseByteString . P.bls12_381_G1_compress
                                    -- let betaBs = P.keccak_256 $ f (qM' iFastSnarkjs)
                                    --                                     <> f (qL' iFastSnarkjs)
                                    --                                     <> f (qR' iFastSnarkjs)
                                    --                                     <> f (qO' iFastSnarkjs)
                                    --                                     <> f (qC' iFastSnarkjs)
                                    --                                     <> f (sSig1' iFastSnarkjs)
                                    --                                     <> f (sSig2' iFastSnarkjs)
                                    --                                     <> f (sSig3' iFastSnarkjs)
                                    --                                     <> reverseByteString (P.integerToByteString (unScalar (head (generators iFastSnarkjs))))
                                    --                                     <> (f . P.bls12_381_G1_uncompress) (commitmentA' pFastSnarkjs)
                                    --                                     <> (f . P.bls12_381_G1_uncompress) (commitmentB' pFastSnarkjs)
                                    --                                     <> (f . P.bls12_381_G1_uncompress) (commitmentC' pFastSnarkjs)
                                    -- print $ mkScalar $ (P.byteStringToInteger . reverseByteString) betaBs `P.modulo` 52435875175126190479447740508185965837690552500527637822603658699938581184513