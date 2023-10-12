{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE BinaryLiterals    #-}

module Plutus.Crypto.Plonk.Verifier
( verifyPlonk
, verifyPlonkSnarkjs
-- , verifyPlonkFast
) where

import Plutus.Crypto.Plonk.Inputs (PreInputs (..), Proof (..), PreInputsFast (..), ProofFast (..))
import Plutus.Crypto.BlsField (mkScalar, Scalar (..), MultiplicativeGroup (..), powerOfTwoExponentiation, reverseByteString)
import PlutusTx.Prelude (Integer, Bool (..), bls12_381_G1_uncompress, bls12_381_G1_scalarMul, bls12_381_G1_generator
                        ,BuiltinBLS12_381_G1_Element, sum, BuiltinBLS12_381_G2_Element, bls12_381_finalVerify
                        ,bls12_381_G2_generator, bls12_381_millerLoop, (>), otherwise, enumFromTo, (.), (&&), divide, error, (<), (||), even, (<>), takeByteString, ($), integerToByteString, bls12_381_G1_compress, keccak_256, modulo, writeBitByteString, bls12_381_G2_neg)
import PlutusTx.Eq (Eq (..))
import PlutusTx.List (map, zipWith, foldr, head, and)
import PlutusTx.Numeric
    ( AdditiveGroup(..),
      AdditiveMonoid(..),
      AdditiveSemigroup(..),
      Module(..),
      MultiplicativeMonoid(one),
      MultiplicativeSemigroup((*)),
      negate )
import PlutusTx.Builtins (blake2b_256, byteStringToInteger)
import PlutusCore (DefaultFun(IntegerToByteString))

-- a general vanilla plonk verifier optimised. 
{-# INLINEABLE verifyPlonk #-}
verifyPlonk :: PreInputsFast -> [Integer] -> ProofFast -> Bool
verifyPlonk preInputsFast@(PreInputsFast n p k1 k2 qM qL qR qO qC sSig1 sSig2 sSig3 x2 gens)
            pubInputs
            proofFast@(ProofFast ca cb cc cz ctl ctm cth cwo cwz ea eb ec es1 es2 ez lagInv)
    | (bls12_381_G1_uncompress -> commA) <- ca
    , (bls12_381_G1_uncompress -> commB) <- cb
    , (bls12_381_G1_uncompress -> commC) <- cc
    , (bls12_381_G1_uncompress -> commZ) <- cz
    , (bls12_381_G1_uncompress -> commTLow) <- ctl
    , (bls12_381_G1_uncompress -> commTMid) <- ctm
    , (bls12_381_G1_uncompress -> commTHigh) <- cth
    , (bls12_381_G1_uncompress -> commWOmega) <- cwo
    , (bls12_381_G1_uncompress -> commWOmegaZeta) <- cwz
    , (mkScalar -> evalA) <- ea
    , (mkScalar -> evalB) <- eb
    , (mkScalar -> evalC) <- ec
    , (mkScalar -> evalS1) <- es1
    , (mkScalar -> evalS2) <- es2
    , (mkScalar -> evalZOmega) <- ez
    , let (w1 : wxs) = map (negate . mkScalar) pubInputs
    , let lagsInv = map mkScalar lagInv
    = let transcript0 = "FS transcriptdom-septesting the provercommitment a" <> ca <> "commitment b"
                                                                             <> cb <> "commitment c"
                                                                             <> cc <> "beta"
          beta = Scalar . byteStringToInteger . takeByteString 31 . blake2b_256 $ transcript0
          transcript1 = transcript0 <> "gamma"
          gamma = Scalar . byteStringToInteger . takeByteString 31 . blake2b_256 $ transcript1
          transcript2 = transcript1 <> "Permutation polynomial" <> cz <> "alpha"
          alpha = Scalar . byteStringToInteger . takeByteString 31 . blake2b_256 $ transcript2
          transcript3 = transcript2 <> "Quotient low polynomial" <> ctl
                                    <> "Quotient mid polynomial" <> ctm
                                    <> "Quotient high polynomial" <> cth
                                    <> "zeta"
          zeta = Scalar . byteStringToInteger . takeByteString 31 . blake2b_256 $ transcript3
          transcript4 = transcript3 <> "Append a_eval." <> integerToByteString ea
                                    <> "Append b_eval." <> integerToByteString eb
                                    <> "Append c_eval." <> integerToByteString ec
                                    <> "Append s_sig1." <> integerToByteString es1
                                    <> "Append s_sig2." <> integerToByteString es2
                                    <> "Append z_omega." <> integerToByteString ez
                                    <> "v"
          v = Scalar . byteStringToInteger . takeByteString 31 . blake2b_256 $ transcript4
          transcript5 = transcript4 <> "w_omega comm" <> cwo
                                    <> "w_omega_zeta comm" <> cwz
                                    <> "u"
          u = Scalar . byteStringToInteger . takeByteString 31 . blake2b_256 $ transcript5
          (lagrangePoly1 : lagrangePolyXs) = zipWith (\x y -> x * (powerOfTwoExponentiation zeta p - one) * y) gens lagsInv
          piZeta = w1 * lagrangePoly1 + sum (zipWith (*) wxs lagrangePolyXs)
          r0 = piZeta - lagrangePoly1*alpha*alpha - alpha*(evalA + beta*evalS1 + gamma)*(evalB + beta*evalS2 + gamma)*(evalC + gamma)*evalZOmega
          batchPolyCommitG1 = scale (evalA*evalB) qM
                            + scale evalA qL
                            + scale evalB qR
                            + scale evalC qO
                            + qC
                            + scale ((evalA + beta*zeta + gamma)*(evalB +beta*k1*zeta + gamma)*(evalC + beta*k2*zeta + gamma)*alpha + lagrangePoly1*alpha*alpha + u) commZ
                            - scale ((evalA +beta*evalS1+gamma)*(evalB + beta*evalS2 + gamma)*alpha*beta*evalZOmega) sSig3
                            - scale (powerOfTwoExponentiation zeta p - one) (commTLow + scale (powerOfTwoExponentiation zeta p) commTMid + scale (powerOfTwoExponentiation (powerOfTwoExponentiation zeta p) 1) commTHigh)
          batchPolyCommitFull = batchPolyCommitG1 + scale v (commA + scale v (commB + scale v (commC + scale v (sSig1 + scale v sSig2))))
          groupEncodedBatchEval = scale (negate r0 + v * (evalA + v * (evalB + v * (evalC + v * (evalS1 + v * evalS2)))) + u*evalZOmega ) bls12_381_G1_generator
    in bls12_381_finalVerify
        (bls12_381_millerLoop (commWOmega + scale u commWOmegaZeta) x2)
        (bls12_381_millerLoop (scale zeta commWOmega + scale (u*zeta*head gens) commWOmegaZeta + batchPolyCommitFull - groupEncodedBatchEval) bls12_381_G2_generator)
       && and (zipWith (\x y -> x * Scalar n * (zeta - y) == one) lagsInv gens)

{-# INLINABLE exponentiate #-}
exponentiate :: Integer -> Integer -> Integer
exponentiate x n
    | n < 0 || x < 0    = error ()
    | n == 0            = 1
    | x == 0            = 0
    | even n            = exponentiate x (n `divide` 2) * exponentiate x (n `divide` 2)
    | otherwise         = x * exponentiate x ((n - 1) `divide` 2) * exponentiate x ((n - 1) `divide` 2)

{-# INLINEABLE verifyPlonkSnarkjs #-}
verifyPlonkSnarkjs :: PreInputs -> [Integer] -> Proof -> Bool
verifyPlonkSnarkjs preInputs@(PreInputs nPub p k1 k2 qM qL qR qO qC sSig1 sSig2 sSig3 x2 gen)
            pubInputs
            proof@(Proof ca cb cc cz ctl ctm cth cwo cwz ea eb ec es1 es2 ez)
    | (bls12_381_G1_uncompress -> commA) <- ca
    , (bls12_381_G1_uncompress -> commB) <- cb
    , (bls12_381_G1_uncompress -> commC) <- cc
    , (bls12_381_G1_uncompress -> commZ) <- cz
    , (bls12_381_G1_uncompress -> commTLow) <- ctl
    , (bls12_381_G1_uncompress -> commTMid) <- ctm
    , (bls12_381_G1_uncompress -> commTHigh) <- cth
    , (bls12_381_G1_uncompress -> commWOmega) <- cwo
    , (bls12_381_G1_uncompress -> commWOmegaZeta) <- cwz
    , (mkScalar -> evalA) <- ea
    , (mkScalar -> evalB) <- eb
    , (mkScalar -> evalC) <- ec
    , (mkScalar -> evalS1) <- es1
    , (mkScalar -> evalS2) <- es2
    , (mkScalar -> evalZOmega) <- ez
    , let (w1 : wxs) = map (negate . mkScalar) pubInputs
    =
        -- this step could be done offchain?
    let n = exponentiate 2 p
        -- get the transcript variables
        beta = Scalar 0xfeb7cbc91fc23ca4aba24fd22d3b4fc391c449a5b09d7acf5e551e09b0622bd
        gamma = Scalar 0x2341d97b49ce6a0e361cf027a78bb90c7f1173bac0dbeb1d972e4a15bee1f4b2
        alpha = Scalar 0x56ef2e8d9e2aa572d70f2a07506ce1b7796df1c69d0593b39fa36951ba5eccdc
        zeta = Scalar 0x7360927c96dd2116de356670c44c7158e8f08e73d310938e2b53f0a2b0b4b28e
        v = Scalar 0x13bb32119ee07d883f0767991af44581bca319de8a92cd92210f74f90614994a
        u = Scalar 0x175a7e907fea7238c13a11a5a5ab7c2d6c8c780a53fda5bfd5aa409b728c4bd7
        -- this is Z_H(zeta) in the plonk paper
        zeroPoly = scale n zeta - one
        -- set gen to one for snarkjs
        -- this is L_1(zeta) and the higher order L_i
        (lagrangePoly1 : lagrangePolyXs) = map (\i -> (scale i gen * zeroPoly) * recip (mkScalar n * (zeta - scale i gen))) (enumFromTo 0 nPub)
      --   lagPol1 = w * zeroPoly * recip (mkScalar n * (zeta - w))
        -- this is PI(zeta) in the plonk paper
        piZeta = w1 * lagrangePoly1 + sum (zipWith (*) wxs lagrangePolyXs)
        -- this is r_0 in the plonk paper
        r0 = piZeta - lagrangePoly1 * alpha * alpha - alpha * (evalA + beta*evalS1 + gamma) * (evalB + beta*evalS2 + gamma) * (evalC + gamma) * evalZOmega
        -- this is [D]_1 in the plonk paper
        batchPolyCommitG1 = scale (evalA*evalB) qM
                          + scale evalA qL
                          + scale evalB qR
                          + scale evalC qO 
                          + qC
                          + scale ((evalA + beta*zeta + gamma)*(evalB +beta*k1*zeta + gamma)*(evalC + beta*k2*zeta + gamma)*alpha + lagrangePoly1*alpha * alpha + u) commZ
                          - scale ((evalA +beta*evalS1+gamma)*(evalB + beta*evalS2+gamma)*alpha*beta*evalZOmega) sSig3
                          - scale zeroPoly (commTLow + scale (scale n zeta) commTMid + scale (scale (2*n) zeta) commTHigh)
        -- this is [F]_1 in the plonk paper
        batchPolyCommitFull = batchPolyCommitG1 + scale v (commA + scale v (commB + scale v (commC + scale v (sSig1 + scale v sSig2))))
        -- this is [E]_1 in the plonk paper
        groupEncodedBatchEval = scale (negate r0 + v * (evalA + v * (evalB + v * (evalC + v * (evalS1 + v * evalS2)))) + u*evalZOmega ) bls12_381_G1_generator
    in
    -- the final check that under the pairing.
    bls12_381_finalVerify 
      (bls12_381_millerLoop (commWOmega + scale u commWOmegaZeta) x2) 
      (bls12_381_millerLoop (scale zeta commWOmega + scale (u*zeta*gen) commWOmegaZeta + batchPolyCommitFull - groupEncodedBatchEval) bls12_381_G2_generator)