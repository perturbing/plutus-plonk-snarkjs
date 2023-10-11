{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE OverloadedStrings  #-}

module Main (main) where

import qualified PlutusTx.Prelude as P
import qualified PlutusTx.Builtins as P
import Plutus.Crypto.BlsField ( Scalar, mkScalar, reverseByteString ) 
import Plutus.Crypto.Plonk (Proof (..), PreInputs (..), ProofFast (..)
                           , PreInputsFast (..), convertToFastProof
                           , convertToFastPreInputs, verifyPlonk )

import ReadSnarkjs ( ProofJSONSnarkjs(..), PreInputsJSONSnarkjs(..) )

import Data.Aeson ( FromJSON, ToJSON, decode )
import GHC.Generics ( Generic )

import qualified Data.ByteString.Lazy as BL
import Data.ByteString ( pack )
import Data.Word ()

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

convertProofSnarkjs :: ProofJSONSnarkjs -> Proof
convertProofSnarkjs proof =
    let f x = reverseByteString (P.writeBitByteString (P.integerToByteString x) 7 True)
        f' x = reverseByteString (P.writeBitByteString (P.integerToByteString x <> P.consByteString 0 P.emptyByteString ) 7 True)
        g x = read . head $ x :: Integer
        h x = read x :: Integer
    in Proof
        { commitmentA = f . g $ a proof
        , commitmentB = f . g $ b proof
        , commitmentC = f . g $ c proof
        , commitmentZ = f . g $ z proof
        , tLow        = f . g $ t1 proof
        , tMid        = f . g $ t2 proof
        , tHigh       = f . g $ t3 proof
        , wOmega      = f' . g $ wxi proof
        , wOmegaZeta  = f . g $ wxiw proof
        , aEval       = h $ eval_a proof
        , bEval       = h $ eval_b proof
        , cEval       = h $ eval_c proof
        , sSig1P      = h $ eval_s1 proof
        , sSig2P      = h $ eval_s2 proof
        , zOmega      = h $ eval_zw proof
        }

convertPreInputsSnarkjs :: PreInputsJSONSnarkjs -> PreInputs
convertPreInputsSnarkjs preIn = 
    let f x = P.bls12_381_G1_uncompress (reverseByteString (P.writeBitByteString (P.integerToByteString x) 7 True))
        f' x = P.bls12_381_G1_uncompress (reverseByteString (P.writeBitByteString (P.integerToByteString x <> P.consByteString 0 P.emptyByteString ) 7 True))
        fG2 x = P.bls12_381_G2_uncompress (reverseByteString (P.writeBitByteString (P.integerToByteString x) 7 True))
        g x = read . head $ x :: Integer
        h x = read x :: Integer
        (x2a: x2b: xs) = head $ x_2' preIn
    in PreInputs
    { nPublic   = nPublic' preIn
    , power     = power' preIn
    , k1        = mkScalar . h $ k_1' preIn
    , k2        = mkScalar . h $ k_2' preIn
    , qM        = f . g $ qm preIn
    , qL        = f' . g $ ql preIn
    , qR        = f . g $ qr preIn
    , qO        = f . g $ qo preIn
    , qC        = P.bls12_381_G1_zero
    , sSig1     = f . g $ s1 preIn
    , sSig2     = f . g $ s2 preIn
    , sSig3     = f . g $ s3 preIn
    , x2        = fG2 $ h x2a + h  x2b * 2^384
    , generator = mkScalar . h $ w preIn
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
                                    print $ verifyPlonk iFastSnarkjs [20] pFastSnarkjs
            Nothing -> print "Could not deserialize PreInputs test vector snarkjs"
        Nothing -> print "Could not deserialize Proof test vector snarkjs"
