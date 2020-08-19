{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Control.Applicative
import           Control.Lens hiding ( pre )
import           Control.Monad.Except
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import           Data.Foldable
import           Data.Functor.Const ( Const(..) )
import qualified Options.Applicative as OA
import           System.Exit

import qualified Data.ElfEdit as E
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Memory.ElfLoader as MM
import           Data.Macaw.PPC () -- type instance ArchReg PPC64
import           Data.Macaw.PPC.PPCReg ()
import qualified Dismantle.PPC as DP
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Renovate as R
import qualified Renovate.Arch.PPC as RP
import qualified Pate.Verification as V
import           Pate.Utils ( (<>|) )

import           ELF ( parseElfOrDie )

main :: IO ()
main = do
  opts <- OA.execParser cliOptions
  bs <- BS.readFile (sourceBinary opts)
  e64 <- parseElfOrDie (error "32") return bs
  mem <- MBL.loadBinary MM.defaultLoadOptions e64
  hdlAlloc <- CFH.newHandleAllocator
  (e64', Const (), ri, _env) <- R.rewriteElf (config (breakTheRewrite opts)) hdlAlloc e64 mem layout
  for_ (targetBinary opts) $ \fp -> LBS.writeFile fp (E.renderElf e64')
  mem' <- MBL.loadBinary MM.defaultLoadOptions e64'
  v <- runExceptT (V.verifyPairs mem mem' (ri ^. R.riBackwardBlockMapping) (ri ^. R.riRewritePairs))
  case v of
    Left err -> die (show err)
    Right _ -> pure ()

data CLIOptions = CLIOptions
  { sourceBinary :: FilePath
  , targetBinary :: Maybe FilePath
  , breakTheRewrite :: Bool
  } deriving (Eq, Ord, Read, Show)

cliOptions :: OA.ParserInfo CLIOptions
cliOptions = OA.info (OA.helper <*> parser)
  (  OA.fullDesc
  <> OA.progDesc "Run a quick test of rewrite verification"
  ) where
  parser = pure CLIOptions
    <*> OA.argument OA.str
      (  OA.metavar "EXE"
      <> OA.help "A binary to rewrite"
      )
    <*> optional (OA.strOption
      (  OA.long "output"
      <> OA.short 'o'
      <> OA.metavar "FILE"
      <> OA.help "Dump the rewritten binary to this file"
      ))
    <*> OA.switch
      (  OA.long "break"
      <> OA.short 'b'
      <> OA.help "Intentionally insert wrong instructions into the rewritten binary"
      )

layout :: R.LayoutStrategy
layout = R.LayoutStrategy R.Parallel R.BlockGrouping R.WholeFunctionTrampoline

config :: Bool -> R.RenovateConfig RP.PPC64 (E.Elf 64) (R.AnalyzeAndRewrite ()) (Const ())
config = RP.config64 . analysis

analysis :: Bool -> R.AnalyzeAndRewrite () RP.PPC64 binFmt (Const ())
analysis broken = R.AnalyzeAndRewrite
  { R.arPreAnalyze = \_ -> return (Const ())
  , R.arAnalyze = \_ _ -> return (Const ())
  , R.arPreRewrite = \_ _ -> return (Const ())
  , R.arRewrite = \_ _ _ b ->
      R.withSymbolicInstructions b $ \repr insns ->
        return (Just (R.ModifiedInstructions repr ([i | broken] <>| insns)))
  }
  where
  (4, Just i0) = DP.disassembleInstruction (LBS.pack [0x38, 0x21, 0x00, 0x01])
  i1 = R.fromGenericInstruction @RP.PPC64 i0
  i :: R.TaggedInstruction RP.PPC64 tp (R.InstructionAnnotation RP.PPC64)
  i = R.tagInstruction Nothing $ RP.NoAddress <$ i1
