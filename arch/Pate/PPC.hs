{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC
  ( PPC.PPC64 )
where

import           Data.Type.Equality
import qualified Pate.Binary as PB
import qualified Pate.Monad as PM
import qualified Data.Macaw.PPC as PPC
import qualified Dismantle.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()


instance PB.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info


instance PM.ValidArch PPC.PPC64 where
  funCallStable reg = case reg of
    PPC.PPC_GP (PPC.GPR i) -> i == 2 || (14 <= i && i <= 31)
    PPC.PPC_FR (PPC.VSReg i) -> 14 <= i && i <= 31
    -- PPC.PPC_LNK -> True
    _ -> False
  funCallArg reg = case reg of
    PPC.PPC_GP (PPC.GPR i) -> 3 <= i && i <= 10
    PPC.PPC_FR (PPC.VSReg i) -> 1 <= i && i <= 13
    _ -> False
  funCallRet reg = case reg of
    PPC.PPC_GP (PPC.GPR i) -> i == 3 || i == 4
    PPC.PPC_FR (PPC.VSReg i) -> 1 <= i && i <= 4
    _ -> False
  funCallIP reg = case reg of
    PPC.PPC_LNK -> Just Refl
    _ -> Nothing
