{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC
  ( PPC.PPC64 )
where

import qualified Pate.Binary as PB
import qualified Data.Macaw.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()

instance PB.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info
