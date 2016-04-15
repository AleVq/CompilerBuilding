{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts -cpp #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParC where
import AbsC qualified AbsC
import LexC
import ErrM
import qualified Data.Array as Happy_Data_Array
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn8 :: (Integer) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> (Integer)
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: (Char) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> (Char)
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: (Double) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> (Double)
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: (Ident) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> (Ident)
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: (Boolean) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> (Boolean)
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: (RExpr) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (RExpr)
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: ([RExpr]) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> ([RExpr])
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: (LExpr) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> (LExpr)
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: (LExpr) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> (LExpr)
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: (LExpr) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> (LExpr)
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: (Program) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> (Program)
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: ([Decl]) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> ([Decl])
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Decl) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Decl)
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: ([VarDeclar]) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> ([VarDeclar])
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (Type) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (Type)
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: (VarDeclar) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> (VarDeclar)
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: (ComplexRExpr) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (ComplexRExpr)
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: ([ComplexRExpr]) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> ([ComplexRExpr])
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: ([Parameter]) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> ([Parameter])
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: (Parameter) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> (Parameter)
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: (Modality) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> (Modality)
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (Stmt) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (Stmt)
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: (Assignment_op) -> (HappyAbsSyn )
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> (Assignment_op)
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: (List_Stmt_Decl) -> (HappyAbsSyn )
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> (List_Stmt_Decl)
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x00\x00\x48\x00\x54\x00\x3e\x00\x94\x00\x7d\x00\x00\x00\x00\x00\x9b\x00\x00\x00\x15\x00\x7f\x00\x3e\x00\x54\x00\x3e\x00\x3e\x00\x00\x00\x00\x00\x94\x00\xac\x00\xaa\x00\x1b\x00\xa9\x00\x61\x00\x6d\x00\x00\x00\xf2\xff\x00\x00\x00\x00\xff\xff\x00\x00\x21\x00\x90\x00\x54\x00\x54\x00\x54\x00\x00\x00\x00\x00\x00\x00\x6a\x00\x11\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6a\x00\x48\x00\x00\x00\x14\x00\x95\x00\x99\x00\x00\x00\x6c\x00\x00\x00\x9a\x01\x03\x00\x30\x02\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x54\x00\x00\x00\x8f\x00\x8e\x00\x67\x00\x54\x00\x54\x00\x00\x00\x54\x00\x94\x00\x69\x00\x7b\x00\x7a\x00\x74\x00\x77\x00\x03\x00\x00\x00\x00\x00\x54\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x81\x01\x00\x00\x86\x00\x75\x00\x68\x01\x4f\x01\x36\x01\x00\x00\x61\x00\x61\x00\x1d\x01\x80\x00\xcc\x01\x5e\x00\x17\x02\x17\x02\x17\x02\x17\x02\x17\x02\x5e\x00\x3f\x00\x3f\x00\x5e\x00\xfe\x01\x5e\x00\xe5\x01\xfe\x00\x00\x00\x60\x00\x47\x00\x00\x00\x20\x02\x3d\x00\xb3\x01\x00\x00\x3d\x00\x6e\x00\x51\x00\x48\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x62\x00\x00\x00\x00\x00\x00\x00\x00\x00\x54\x00\x00\x00\x00\x00\x94\x00\x42\x00\x94\x00\x54\x00\x54\x00\x00\x00\xe5\x00\xcc\x00\x24\x00\x00\x00\x00\x00\x00\x00\x11\x00\x20\x02\x61\x00\x4e\x00\x32\x00\x00\x00\x3d\x00\x00\x00\x00\x00\x00\x00\x94\x00\x94\x00\x29\x00\x00\x00\x34\x00\x00\x00\x00\x00\x94\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x1d\x00\x66\x00\xfb\x03\xb8\x01\xa8\x02\x00\x00\x00\x00\x00\x00\x22\x00\x00\x00\x00\x00\x00\x00\x86\x01\xf1\x03\x03\x01\xb9\x00\x00\x00\x00\x00\xa5\x02\x00\x00\x00\x00\x00\x00\x00\x00\x73\x02\x2e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe7\x03\xdd\x03\xd3\x03\x00\x00\x00\x00\x00\x00\x00\x00\x72\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x35\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2d\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc9\x03\xbf\x03\xb5\x03\xab\x03\xa1\x03\x97\x03\x8d\x03\x83\x03\x79\x03\x6f\x03\x65\x03\x5b\x03\x51\x03\x47\x03\x3d\x03\xf7\x02\x00\x00\x00\x00\x00\x00\x00\x00\x33\x03\x29\x03\x00\x00\x1f\x03\x9e\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6b\x02\x5a\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x5f\x00\x00\x00\x53\x00\xdf\x02\x00\x00\x00\x00\xcd\x02\x00\x00\x00\x00\xf5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xed\x02\x00\x00\x00\x00\x95\x02\x00\x00\x8e\x02\x0b\x03\x01\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x26\x00\x40\x00\x52\x02\x00\x00\x00\x00\x00\x00\xbb\x02\x00\x00\x00\x00\x00\x00\x8b\x02\x84\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc3\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xcf\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfa\xff\xd9\xff\x00\x00\xda\xff\xd5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb1\xff\xb0\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9d\xff\x00\x00\xf7\xff\x00\x00\xe1\xff\xe0\xff\xd9\xff\xde\xff\x00\x00\xe3\xff\x00\x00\x00\x00\x00\x00\xf5\xff\xf6\xff\xf9\xff\x00\x00\x00\x00\xc7\xff\xc4\xff\xc6\xff\xc3\xff\xc5\xff\x00\x00\xd0\xff\xce\xff\x00\x00\x00\x00\xcb\xff\xc8\xff\x00\x00\xe4\xff\x00\x00\xe3\xff\xe5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdd\xff\xa6\xff\x9c\xff\x9b\xff\x00\x00\x00\x00\x00\x00\xae\xff\x00\x00\x00\x00\x00\x00\x00\x00\xd6\xff\xd7\xff\xd8\xff\x00\x00\xd4\xff\xd3\xff\x00\x00\x9f\xff\xa4\xff\xa3\xff\xa1\xff\xa2\xff\xac\xff\xa5\xff\xa0\xff\x9e\xff\x00\x00\xd2\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb2\xff\x9d\xff\x9d\xff\xdc\xff\x00\x00\xf3\xff\xe6\xff\xec\xff\xed\xff\xf1\xff\xee\xff\xef\xff\xe8\xff\xea\xff\xeb\xff\xe9\xff\xf2\xff\xe7\xff\xf0\xff\x00\x00\xf4\xff\x00\x00\x00\x00\xcd\xff\xbd\xff\x00\x00\xc1\xff\xc2\xff\x00\x00\x00\x00\xbc\xff\x00\x00\xb6\xff\xb3\xff\xb7\xff\xb5\xff\xb8\xff\xb4\xff\x00\x00\xca\xff\xc9\xff\xd1\xff\xe2\xff\xdd\xff\x99\xff\x9a\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xad\xff\x00\x00\x00\x00\xab\xff\xaf\xff\xa9\xff\xdb\xff\x00\x00\xbd\xff\x9d\xff\xbf\xff\x00\x00\xc0\xff\x00\x00\xcc\xff\xbb\xff\xba\xff\x00\x00\x00\x00\x00\x00\xa8\xff\x00\x00\xaa\xff\xbe\xff\x00\x00\xa7\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x02\x00\x03\x00\x0e\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x08\x00\x0d\x00\x0e\x00\x0f\x00\x1d\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x09\x00\x07\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x1d\x00\x0c\x00\x07\x00\x02\x00\x03\x00\x10\x00\x05\x00\x0a\x00\x0b\x00\x03\x00\x09\x00\x17\x00\x0b\x00\x00\x00\x1d\x00\x14\x00\x0f\x00\x03\x00\x40\x00\x12\x00\x35\x00\x36\x00\x15\x00\x16\x00\x16\x00\x18\x00\x19\x00\x1a\x00\x08\x00\x14\x00\x01\x00\x40\x00\x1f\x00\x0c\x00\x03\x00\x0e\x00\x07\x00\x07\x00\x09\x00\x09\x00\x09\x00\x0c\x00\x0c\x00\x27\x00\x0f\x00\x10\x00\x10\x00\x3e\x00\x1e\x00\x12\x00\x12\x00\x13\x00\x14\x00\x01\x00\x14\x00\x36\x00\x1b\x00\x1c\x00\x1d\x00\x07\x00\x0e\x00\x09\x00\x1f\x00\x0e\x00\x0c\x00\x40\x00\x03\x00\x0f\x00\x10\x00\x12\x00\x13\x00\x14\x00\x07\x00\x21\x00\x09\x00\x23\x00\x0d\x00\x0c\x00\x0f\x00\x1b\x00\x1c\x00\x10\x00\x0c\x00\x2b\x00\x0e\x00\x03\x00\x08\x00\x3a\x00\x3b\x00\x17\x00\x32\x00\x3e\x00\x3e\x00\x1f\x00\x1e\x00\x0d\x00\x38\x00\x0f\x00\x21\x00\x22\x00\x23\x00\x3e\x00\x25\x00\x26\x00\x08\x00\x14\x00\x29\x00\x2a\x00\x2b\x00\x07\x00\x3a\x00\x3b\x00\x2f\x00\x1d\x00\x3e\x00\x32\x00\x33\x00\x34\x00\x1f\x00\x1d\x00\x1d\x00\x38\x00\x39\x00\x07\x00\x33\x00\x09\x00\x37\x00\x3e\x00\x0c\x00\x06\x00\x14\x00\x14\x00\x10\x00\x0a\x00\x3a\x00\x0e\x00\x0d\x00\x14\x00\x40\x00\x3e\x00\x11\x00\x1d\x00\x13\x00\x14\x00\x07\x00\x07\x00\x17\x00\x07\x00\xff\xff\xff\xff\x22\x00\x3a\x00\x1d\x00\x25\x00\x26\x00\x20\x00\x03\x00\x29\x00\x2a\x00\x40\x00\x07\x00\x08\x00\x09\x00\x2f\x00\xff\xff\xff\xff\x03\x00\x33\x00\x34\x00\xff\xff\x07\x00\x08\x00\x09\x00\x39\x00\x02\x00\x03\x00\x35\x00\x05\x00\x3e\x00\xff\xff\xff\xff\x09\x00\xff\xff\x0b\x00\x15\x00\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\x14\x00\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\xff\xff\x05\x00\x1f\x00\xff\xff\x08\x00\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\x05\x00\x1f\x00\xff\xff\x03\x00\x09\x00\xff\xff\x0b\x00\x07\x00\x08\x00\x09\x00\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\x36\x00\x1e\x00\x1f\x00\xff\xff\x02\x00\x03\x00\xff\xff\x05\x00\xff\xff\xff\xff\xff\xff\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\x0e\x00\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\x36\x00\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\xff\xff\x05\x00\x1f\x00\xff\xff\x08\x00\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\x05\x00\x1f\x00\xff\xff\x08\x00\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\x05\x00\x1f\x00\xff\xff\x08\x00\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\x05\x00\x1f\x00\xff\xff\x03\x00\x09\x00\xff\xff\x0b\x00\x07\x00\x08\x00\x09\x00\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\x14\x00\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\x05\x00\x1f\x00\xff\xff\x08\x00\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\x05\x00\x1f\x00\xff\xff\x03\x00\x09\x00\xff\xff\x0b\x00\x07\x00\x08\x00\x09\x00\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\x05\x00\x1f\x00\xff\xff\xff\xff\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\x36\x00\xff\xff\x1f\x00\xff\xff\xff\xff\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\xff\xff\xff\xff\x1f\x00\xff\xff\xff\xff\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\xff\xff\xff\xff\x1f\x00\xff\xff\xff\xff\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x02\x00\x03\x00\xff\xff\xff\xff\x1f\x00\xff\xff\xff\xff\x09\x00\xff\xff\x0b\x00\xff\xff\xff\xff\xff\xff\x0f\x00\xff\xff\x21\x00\x12\x00\x23\x00\x24\x00\x15\x00\x16\x00\xff\xff\x18\x00\x19\x00\x1a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x1f\x00\x30\x00\x31\x00\x32\x00\xff\xff\xff\xff\x03\x00\xff\xff\xff\xff\x38\x00\x07\x00\x08\x00\x09\x00\xff\xff\x03\x00\x0c\x00\xff\xff\x0e\x00\x07\x00\x08\x00\x09\x00\xff\xff\xff\xff\x0c\x00\x15\x00\x0e\x00\x17\x00\xff\xff\xff\xff\xff\xff\xff\xff\x03\x00\x15\x00\xff\xff\x17\x00\x07\x00\x08\x00\x09\x00\xff\xff\x03\x00\x0c\x00\xff\xff\x0e\x00\x07\x00\x08\x00\x09\x00\xff\xff\xff\xff\x0c\x00\x15\x00\x0e\x00\x17\x00\xff\xff\xff\xff\xff\xff\xff\xff\x03\x00\x15\x00\xff\xff\x17\x00\x07\x00\x08\x00\x09\x00\x03\x00\xff\xff\xff\xff\x03\x00\x07\x00\x08\x00\x09\x00\x07\x00\x08\x00\x09\x00\x03\x00\x15\x00\xff\xff\xff\xff\x07\x00\x08\x00\x09\x00\xff\xff\x15\x00\x03\x00\xff\xff\x15\x00\xff\xff\x07\x00\x08\x00\x09\x00\x03\x00\xff\xff\x15\x00\x03\x00\x07\x00\x08\x00\x09\x00\x07\x00\x08\x00\x09\x00\xff\xff\x15\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\x00\x00\x01\x00\x15\x00\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\x11\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\x11\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x10\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\xff\xff\x03\x00\x04\x00\x05\x00\xff\xff\x07\x00\x08\x00\x09\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\xd9\xff\xd9\xff\xa6\x00\xd9\xff\xd9\xff\x4a\x00\xd9\xff\xd9\xff\xd9\xff\xd9\xff\x67\x00\xd9\xff\xd9\xff\xd9\xff\x3b\x00\xd9\xff\xd9\xff\xd9\xff\xd9\xff\xd9\xff\xd9\xff\xd9\xff\xd9\xff\xd9\xff\xd9\xff\x35\x00\x85\x00\xd9\xff\xd9\xff\xd9\xff\xd9\xff\x3b\x00\x5a\x00\x50\x00\x3c\x00\x3d\x00\x5b\x00\x3e\x00\x2e\x00\x2f\x00\xaf\x00\x3f\x00\x86\x00\x40\x00\x81\x00\x36\x00\x51\x00\x41\x00\x4a\x00\xff\xff\x42\x00\xd9\xff\xd9\xff\x43\x00\x44\x00\x5b\x00\x45\x00\x46\x00\x47\x00\xb8\x00\xb4\x00\x22\x00\xd9\xff\x48\x00\x30\x00\x3d\x00\x28\x00\x23\x00\x0d\x00\x0e\x00\x0e\x00\x3f\x00\x0f\x00\x0f\x00\xb1\x00\x24\x00\x10\x00\x10\x00\x1a\x00\xac\x00\x42\x00\xae\x00\x8a\x00\x8b\x00\x22\x00\xa4\x00\x49\x00\x25\x00\x26\x00\x89\x00\x23\x00\xad\x00\x0e\x00\x48\x00\xa8\x00\x0f\x00\xff\xff\x92\x00\x24\x00\x10\x00\x89\x00\x8a\x00\x8b\x00\x0d\x00\x2a\x00\x0e\x00\x2b\x00\x93\x00\x0f\x00\x33\x00\x25\x00\x26\x00\x10\x00\x27\x00\x2c\x00\x28\x00\x31\x00\xa9\x00\x07\x00\x27\x00\x86\x00\x2d\x00\x1a\x00\x1a\x00\x48\x00\x95\x00\x32\x00\x2e\x00\x33\x00\x2a\x00\x11\x00\x2b\x00\x1a\x00\x12\x00\x13\x00\x97\x00\x9e\x00\x14\x00\x15\x00\x2c\x00\x9f\x00\x07\x00\x27\x00\x16\x00\xd7\xff\x1a\x00\x2d\x00\x17\x00\x18\x00\x48\x00\xd6\xff\x3b\x00\x2e\x00\x19\x00\x0d\x00\x68\x00\x0e\x00\x6d\x00\x1a\x00\x0f\x00\x5d\x00\x6e\x00\x6f\x00\x10\x00\x5e\x00\x07\x00\x83\x00\x5f\x00\x84\x00\xff\xff\x1a\x00\x60\x00\x3b\x00\x61\x00\x62\x00\x4f\x00\x52\x00\x63\x00\x53\x00\x00\x00\x00\x00\x11\x00\x07\x00\x3b\x00\x12\x00\x13\x00\x64\x00\x07\x00\x14\x00\x15\x00\xff\xff\x54\x00\x55\x00\x0a\x00\x16\x00\x00\x00\x00\x00\x07\x00\x17\x00\x18\x00\x00\x00\x08\x00\x09\x00\x0a\x00\x19\x00\x3c\x00\x3d\x00\x65\x00\x3e\x00\x1a\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x40\x00\xb8\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\xb2\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x00\x00\x3e\x00\x48\x00\x00\x00\xb3\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x49\x00\x3e\x00\x48\x00\x00\x00\x07\x00\x3f\x00\x00\x00\x40\x00\x54\x00\x56\x00\x0a\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x00\x00\x00\x00\x49\x00\x96\x00\x48\x00\x00\x00\x3c\x00\x3d\x00\x00\x00\x3e\x00\x00\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x98\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x49\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x00\x00\x3e\x00\x48\x00\x00\x00\x9b\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x49\x00\x3e\x00\x48\x00\x00\x00\x9c\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x49\x00\x3e\x00\x48\x00\x00\x00\x9d\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x49\x00\x3e\x00\x48\x00\x00\x00\x07\x00\x3f\x00\x00\x00\x40\x00\x58\x00\x09\x00\x0a\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\xa0\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x49\x00\x3e\x00\x48\x00\x00\x00\x81\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x49\x00\x3e\x00\x48\x00\x00\x00\x07\x00\x3f\x00\x00\x00\x40\x00\x1a\x00\x09\x00\x0a\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x3c\x00\x3d\x00\x49\x00\x3e\x00\x48\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x00\x00\x3d\x00\x49\x00\x00\x00\x48\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3c\x00\x3d\x00\x00\x00\x00\x00\x48\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\x00\x00\x3d\x00\x00\x00\x00\x00\x48\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3c\x00\x3d\x00\x00\x00\x00\x00\x48\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x41\x00\x00\x00\xb9\xff\x42\x00\xb9\xff\x8d\x00\x43\x00\x44\x00\x00\x00\x45\x00\x46\x00\x47\x00\xb9\xff\x8e\x00\x8f\x00\x90\x00\x48\x00\x91\x00\x92\x00\xb9\xff\x00\x00\x00\x00\x07\x00\x00\x00\x00\x00\xb9\xff\x08\x00\x09\x00\x0a\x00\x00\x00\x07\x00\x4b\x00\x00\x00\x28\x00\x08\x00\x09\x00\x0a\x00\x00\x00\x00\x00\x4b\x00\x4c\x00\x28\x00\xad\x00\x00\x00\x00\x00\x00\x00\x00\x00\x07\x00\x4c\x00\x00\x00\x98\x00\x08\x00\x09\x00\x0a\x00\x00\x00\x07\x00\x4b\x00\x00\x00\x28\x00\x08\x00\x09\x00\x0a\x00\x00\x00\x00\x00\x4b\x00\x4c\x00\x28\x00\x99\x00\x00\x00\x00\x00\x00\x00\x00\x00\x07\x00\x4c\x00\x00\x00\x4d\x00\x08\x00\x09\x00\x0a\x00\x07\x00\x00\x00\x00\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x08\x00\x09\x00\x0a\x00\x07\x00\xb4\x00\x00\x00\x00\x00\x08\x00\x09\x00\x0a\x00\x00\x00\xb5\x00\x07\x00\x00\x00\xa2\x00\x00\x00\x08\x00\x09\x00\x0a\x00\x07\x00\x00\x00\xa4\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x08\x00\x09\x00\x0a\x00\x00\x00\x68\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x53\x00\x1b\x00\x1c\x00\x0b\x00\x1d\x00\x1e\x00\x86\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa9\x00\xb6\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x86\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa9\x00\xaa\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x86\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x1c\x00\x87\x00\x1d\x00\x1e\x00\x6f\x00\xa5\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x6f\x00\x70\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\xa0\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\xa1\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x65\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x69\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x6a\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x6b\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x71\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x72\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x73\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x74\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x75\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x76\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x77\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x78\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x79\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x7a\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x7b\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x7c\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x7d\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x7e\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x7f\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x36\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x37\x00\x00\x00\x38\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x39\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x57\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x1b\x00\x1c\x00\x00\x00\x1d\x00\x1e\x00\x1f\x00\x00\x00\x20\x00\x09\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (5, 102) [
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91),
	(92 , happyReduce_92),
	(93 , happyReduce_93),
	(94 , happyReduce_94),
	(95 , happyReduce_95),
	(96 , happyReduce_96),
	(97 , happyReduce_97),
	(98 , happyReduce_98),
	(99 , happyReduce_99),
	(100 , happyReduce_100),
	(101 , happyReduce_101),
	(102 , happyReduce_102)
	]

happy_n_terms = 65 :: Int
happy_n_nonterms = 24 :: Int

happyReduce_5 = happySpecReduce_1  0# happyReduction_5
happyReduction_5 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn8
		 ((read ( happy_var_1)) :: Integer
	)}

happyReduce_6 = happySpecReduce_1  1# happyReduction_6
happyReduction_6 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TC happy_var_1)) -> 
	happyIn9
		 ((read ( happy_var_1)) :: Char
	)}

happyReduce_7 = happySpecReduce_1  2# happyReduction_7
happyReduction_7 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TD happy_var_1)) -> 
	happyIn10
		 ((read ( happy_var_1)) :: Double
	)}

happyReduce_8 = happySpecReduce_1  3# happyReduction_8
happyReduction_8 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn11
		 (Ident happy_var_1
	)}

happyReduce_9 = happySpecReduce_1  4# happyReduction_9
happyReduction_9 happy_x_1
	 =  happyIn12
		 (AbsC.Boolean_True
	)

happyReduce_10 = happySpecReduce_1  4# happyReduction_10
happyReduction_10 happy_x_1
	 =  happyIn12
		 (AbsC.Boolean_False
	)

happyReduce_11 = happySpecReduce_3  5# happyReduction_11
happyReduction_11 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (happy_var_2
	)}

happyReduce_12 = happySpecReduce_3  5# happyReduction_12
happyReduction_12 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (BoolOp Or ) happy_var_1 happy_var_3
	)}}

happyReduce_13 = happySpecReduce_3  5# happyReduction_13
happyReduction_13 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (BoolOp And) happy_var_1 happy_var_3
	)}}

happyReduce_14 = happySpecReduce_3  5# happyReduction_14
happyReduction_14 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Eq ) happy_var_1 happy_var_3
	)}}

happyReduce_15 = happySpecReduce_3  5# happyReduction_15
happyReduction_15 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Neq) happy_var_1 happy_var_3
	)}}

happyReduce_16 = happySpecReduce_3  5# happyReduction_16
happyReduction_16 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Lt ) happy_var_1 happy_var_3
	)}}

happyReduce_17 = happySpecReduce_3  5# happyReduction_17
happyReduction_17 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp LtE) happy_var_1 happy_var_3
	)}}

happyReduce_18 = happySpecReduce_3  5# happyReduction_18
happyReduction_18 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Gt ) happy_var_1 happy_var_3
	)}}

happyReduce_19 = happySpecReduce_3  5# happyReduction_19
happyReduction_19 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp GtE) happy_var_1 happy_var_3
	)}}

happyReduce_20 = happySpecReduce_3  5# happyReduction_20
happyReduction_20 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Add) happy_var_1 happy_var_3
	)}}

happyReduce_21 = happySpecReduce_3  5# happyReduction_21
happyReduction_21 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Sub) happy_var_1 happy_var_3
	)}}

happyReduce_22 = happySpecReduce_3  5# happyReduction_22
happyReduction_22 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Mul) happy_var_1 happy_var_3
	)}}

happyReduce_23 = happySpecReduce_3  5# happyReduction_23
happyReduction_23 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Div) happy_var_1 happy_var_3
	)}}

happyReduce_24 = happySpecReduce_3  5# happyReduction_24
happyReduction_24 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Mod) happy_var_1 happy_var_3
	)}}

happyReduce_25 = happySpecReduce_3  5# happyReduction_25
happyReduction_25 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Pow) happy_var_1 happy_var_3
	)}}

happyReduce_26 = happySpecReduce_2  5# happyReduction_26
happyReduction_26 happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (UnaryOp Not happy_var_2
	)}

happyReduce_27 = happySpecReduce_2  5# happyReduction_27
happyReduction_27 happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (UnaryOp Neg happy_var_2
	)}

happyReduce_28 = happySpecReduce_1  5# happyReduction_28
happyReduction_28 happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (LExpr happy_var_1
	)}

happyReduce_29 = happyReduce 4# 5# happyReduction_29
happyReduction_29 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_1 of { happy_var_1 -> 
	case happyOut14 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (FCall happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_30 = happySpecReduce_1  5# happyReduction_30
happyReduction_30 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (Const $ Int happy_var_1
	)}

happyReduce_31 = happySpecReduce_1  5# happyReduction_31
happyReduction_31 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (Const $ Char happy_var_1
	)}

happyReduce_32 = happySpecReduce_1  5# happyReduction_32
happyReduction_32 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (Const $ Ident happy_var_1
	)}

happyReduce_33 = happySpecReduce_1  5# happyReduction_33
happyReduction_33 happy_x_1
	 =  happyIn13
		 (Const $ Bool
	)

happyReduce_34 = happySpecReduce_0  6# happyReduction_34
happyReduction_34  =  happyIn14
		 ([]
	)

happyReduce_35 = happySpecReduce_1  6# happyReduction_35
happyReduction_35 happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	happyIn14
		 ((:[]) happy_var_1
	)}

happyReduce_36 = happySpecReduce_3  6# happyReduction_36
happyReduction_36 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut14 happy_x_3 of { happy_var_3 -> 
	happyIn14
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_37 = happySpecReduce_1  7# happyReduction_37
happyReduction_37 happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	happyIn15
		 (happy_var_1
	)}

happyReduce_38 = happySpecReduce_1  7# happyReduction_38
happyReduction_38 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn15
		 (AbsC.Id happy_var_1
	)}

happyReduce_39 = happySpecReduce_2  7# happyReduction_39
happyReduction_39 happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn15
		 (AbsC.Deref happy_var_2
	)}

happyReduce_40 = happySpecReduce_2  7# happyReduction_40
happyReduction_40 happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn15
		 (PrePostIncDecr Pre Inc happy_var_2
	)}

happyReduce_41 = happySpecReduce_2  7# happyReduction_41
happyReduction_41 happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn15
		 (PrePostIncDecr Pre Decr happy_var_2
	)}

happyReduce_42 = happySpecReduce_1  8# happyReduction_42
happyReduction_42 happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

happyReduce_43 = happySpecReduce_2  8# happyReduction_43
happyReduction_43 happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (PrePostIncDecr Post Inc happy_var_1
	)}

happyReduce_44 = happySpecReduce_2  8# happyReduction_44
happyReduction_44 happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (PrePostIncDecr Post Decr happy_var_1
	)}

happyReduce_45 = happySpecReduce_3  9# happyReduction_45
happyReduction_45 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut15 happy_x_2 of { happy_var_2 -> 
	happyIn17
		 (happy_var_2
	)}

happyReduce_46 = happyReduce 4# 9# happyReduction_46
happyReduction_46 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut15 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn17
		 (AbsC.BasLExpr happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_47 = happySpecReduce_1  10# happyReduction_47
happyReduction_47 happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	happyIn18
		 (AbsC.Prog  happy_var_1
	)}

happyReduce_48 = happySpecReduce_0  11# happyReduction_48
happyReduction_48  =  happyIn19
		 ([]
	)

happyReduce_49 = happySpecReduce_2  11# happyReduction_49
happyReduction_49 happy_x_2
	happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut20 happy_x_2 of { happy_var_2 -> 
	happyIn19
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_50 = happySpecReduce_3  12# happyReduction_50
happyReduction_50 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_2 of { happy_var_2 -> 
	happyIn20
		 (AbsC.Dvar happy_var_1 happy_var_2
	)}}

happyReduce_51 = happyReduce 6# 12# happyReduction_51
happyReduction_51 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut22 happy_x_1 of { happy_var_1 -> 
	case happyOut11 happy_x_2 of { happy_var_2 -> 
	case happyOut26 happy_x_4 of { happy_var_4 -> 
	case happyOut31 happy_x_6 of { happy_var_6 -> 
	happyIn20
		 (AbsC.Dfun happy_var_1 happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}}

happyReduce_52 = happySpecReduce_1  13# happyReduction_52
happyReduction_52 happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((:[]) happy_var_1
	)}

happyReduce_53 = happySpecReduce_3  13# happyReduction_53
happyReduction_53 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_3 of { happy_var_3 -> 
	happyIn21
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_54 = happyReduce 4# 14# happyReduction_54
happyReduction_54 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut22 happy_x_1 of { happy_var_1 -> 
	case happyOut8 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (AbsC.ArrDef happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_55 = happySpecReduce_2  14# happyReduction_55
happyReduction_55 happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn22
		 (AbsC.Pointer happy_var_1
	)}

happyReduce_56 = happySpecReduce_1  14# happyReduction_56
happyReduction_56 happy_x_1
	 =  happyIn22
		 (AbsC.Boolean
	)

happyReduce_57 = happySpecReduce_1  14# happyReduction_57
happyReduction_57 happy_x_1
	 =  happyIn22
		 (AbsC.T_Int
	)

happyReduce_58 = happySpecReduce_1  14# happyReduction_58
happyReduction_58 happy_x_1
	 =  happyIn22
		 (AbsC.T_Float
	)

happyReduce_59 = happySpecReduce_1  14# happyReduction_59
happyReduction_59 happy_x_1
	 =  happyIn22
		 (AbsC.T_Char
	)

happyReduce_60 = happySpecReduce_1  14# happyReduction_60
happyReduction_60 happy_x_1
	 =  happyIn22
		 (AbsC.T_Void
	)

happyReduce_61 = happySpecReduce_3  15# happyReduction_61
happyReduction_61 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	case happyOut24 happy_x_3 of { happy_var_3 -> 
	happyIn23
		 (AbsC.VarDecl happy_var_1 happy_var_3
	)}}

happyReduce_62 = happySpecReduce_1  16# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (AbsC.Simple happy_var_1
	)}

happyReduce_63 = happySpecReduce_3  16# happyReduction_63
happyReduction_63 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_2 of { happy_var_2 -> 
	happyIn24
		 (AbsC.Array happy_var_2
	)}

happyReduce_64 = happySpecReduce_1  17# happyReduction_64
happyReduction_64 happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 ((:[]) happy_var_1
	)}

happyReduce_65 = happySpecReduce_3  17# happyReduction_65
happyReduction_65 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	case happyOut25 happy_x_3 of { happy_var_3 -> 
	happyIn25
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_66 = happySpecReduce_0  18# happyReduction_66
happyReduction_66  =  happyIn26
		 ([]
	)

happyReduce_67 = happySpecReduce_1  18# happyReduction_67
happyReduction_67 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 ((:[]) happy_var_1
	)}

happyReduce_68 = happySpecReduce_3  18# happyReduction_68
happyReduction_68 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	case happyOut26 happy_x_3 of { happy_var_3 -> 
	happyIn26
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_69 = happySpecReduce_3  19# happyReduction_69
happyReduction_69 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut22 happy_x_2 of { happy_var_2 -> 
	case happyOut11 happy_x_3 of { happy_var_3 -> 
	happyIn27
		 (AbsC.Param happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_70 = happySpecReduce_0  20# happyReduction_70
happyReduction_70  =  happyIn28
		 (AbsC.M_Void
	)

happyReduce_71 = happySpecReduce_1  20# happyReduction_71
happyReduction_71 happy_x_1
	 =  happyIn28
		 (AbsC.M_Val
	)

happyReduce_72 = happySpecReduce_1  20# happyReduction_72
happyReduction_72 happy_x_1
	 =  happyIn28
		 (AbsC.M_Ref
	)

happyReduce_73 = happySpecReduce_1  20# happyReduction_73
happyReduction_73 happy_x_1
	 =  happyIn28
		 (AbsC.M_Const
	)

happyReduce_74 = happySpecReduce_1  20# happyReduction_74
happyReduction_74 happy_x_1
	 =  happyIn28
		 (AbsC.M_Res
	)

happyReduce_75 = happySpecReduce_1  20# happyReduction_75
happyReduction_75 happy_x_1
	 =  happyIn28
		 (AbsC.M_Valres
	)

happyReduce_76 = happySpecReduce_1  20# happyReduction_76
happyReduction_76 happy_x_1
	 =  happyIn28
		 (AbsC.M_Name
	)

happyReduce_77 = happySpecReduce_3  21# happyReduction_77
happyReduction_77 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_2 of { happy_var_2 -> 
	happyIn29
		 (AbsC.Block happy_var_2
	)}

happyReduce_78 = happySpecReduce_1  21# happyReduction_78
happyReduction_78 happy_x_1
	 =  happyIn29
		 (AbsC.Break
	)

happyReduce_79 = happySpecReduce_1  21# happyReduction_79
happyReduction_79 happy_x_1
	 =  happyIn29
		 (AbsC.Continue
	)

happyReduce_80 = happyReduce 5# 21# happyReduction_80
happyReduction_80 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn29
		 (AbsC.RetExp happy_var_3
	) `HappyStk` happyRest}

happyReduce_81 = happySpecReduce_2  21# happyReduction_81
happyReduction_81 happy_x_2
	happy_x_1
	 =  happyIn29
		 (AbsC.RetExpVoid
	)

happyReduce_82 = happyReduce 4# 21# happyReduction_82
happyReduction_82 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut15 happy_x_1 of { happy_var_1 -> 
	case happyOut30 happy_x_2 of { happy_var_2 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn29
		 (AbsC.Assgn happy_var_1 happy_var_2 happy_var_3
	) `HappyStk` happyRest}}}

happyReduce_83 = happySpecReduce_2  21# happyReduction_83
happyReduction_83 happy_x_2
	happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	happyIn29
		 (AbsC.LExprStmt happy_var_1
	)}

happyReduce_84 = happyReduce 5# 21# happyReduction_84
happyReduction_84 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	case happyOut29 happy_x_5 of { happy_var_5 -> 
	happyIn29
		 (AbsC.IfNoElse happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_85 = happyReduce 7# 21# happyReduction_85
happyReduction_85 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	case happyOut29 happy_x_5 of { happy_var_5 -> 
	case happyOut29 happy_x_7 of { happy_var_7 -> 
	happyIn29
		 (AbsC.IfElse happy_var_3 happy_var_5 happy_var_7
	) `HappyStk` happyRest}}}

happyReduce_86 = happyReduce 5# 21# happyReduction_86
happyReduction_86 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	case happyOut29 happy_x_5 of { happy_var_5 -> 
	happyIn29
		 (AbsC.While happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_87 = happyReduce 7# 21# happyReduction_87
happyReduction_87 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut29 happy_x_2 of { happy_var_2 -> 
	case happyOut13 happy_x_5 of { happy_var_5 -> 
	happyIn29
		 (AbsC.DoWhile happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_88 = happyReduce 9# 21# happyReduction_88
happyReduction_88 (happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut29 happy_x_3 of { happy_var_3 -> 
	case happyOut13 happy_x_5 of { happy_var_5 -> 
	case happyOut29 happy_x_7 of { happy_var_7 -> 
	case happyOut29 happy_x_9 of { happy_var_9 -> 
	happyIn29
		 (AbsC.For happy_var_3 happy_var_5 happy_var_7 happy_var_9
	) `HappyStk` happyRest}}}}

happyReduce_89 = happySpecReduce_2  21# happyReduction_89
happyReduction_89 happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn29
		 (AbsC.Comment happy_var_2
	)}

happyReduce_90 = happySpecReduce_1  22# happyReduction_90
happyReduction_90 happy_x_1
	 =  happyIn30
		 (AbsC.Assign
	)

happyReduce_91 = happySpecReduce_1  22# happyReduction_91
happyReduction_91 happy_x_1
	 =  happyIn30
		 (AbsC.AssgnMul
	)

happyReduce_92 = happySpecReduce_1  22# happyReduction_92
happyReduction_92 happy_x_1
	 =  happyIn30
		 (AbsC.AssgnAdd
	)

happyReduce_93 = happySpecReduce_1  22# happyReduction_93
happyReduction_93 happy_x_1
	 =  happyIn30
		 (AbsC.AssgnDiv
	)

happyReduce_94 = happySpecReduce_1  22# happyReduction_94
happyReduction_94 happy_x_1
	 =  happyIn30
		 (AbsC.AssgnSub
	)

happyReduce_95 = happySpecReduce_1  22# happyReduction_95
happyReduction_95 happy_x_1
	 =  happyIn30
		 (AbsC.AssgnPow
	)

happyReduce_96 = happySpecReduce_1  22# happyReduction_96
happyReduction_96 happy_x_1
	 =  happyIn30
		 (AbsC.AssgnAnd
	)

happyReduce_97 = happySpecReduce_1  22# happyReduction_97
happyReduction_97 happy_x_1
	 =  happyIn30
		 (AbsC.AssgnOr
	)

happyReduce_98 = happySpecReduce_0  23# happyReduction_98
happyReduction_98  =  happyIn31
		 ([]
	)

happyReduce_99 = happySpecReduce_1  23# happyReduction_99
happyReduction_99 happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 ((:[]) happy_var_1
	)}

happyReduce_100 = happySpecReduce_1  23# happyReduction_100
happyReduction_100 happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 ((:[]) happy_var_1
	)}

happyReduce_101 = happySpecReduce_3  23# happyReduction_101
happyReduction_101 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	happyIn31
		 ((:) happy_var_1 happy_var_2
	)}}

happyReduce_102 = happySpecReduce_3  23# happyReduction_102
happyReduction_102 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	happyIn31
		 ((:) happy_var_1 happy_var_2
	)}}

happyNewToken action sts stk [] =
	happyDoAction 64# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TS _ 26) -> cont 26#;
	PT _ (TS _ 27) -> cont 27#;
	PT _ (TS _ 28) -> cont 28#;
	PT _ (TS _ 29) -> cont 29#;
	PT _ (TS _ 30) -> cont 30#;
	PT _ (TS _ 31) -> cont 31#;
	PT _ (TS _ 32) -> cont 32#;
	PT _ (TS _ 33) -> cont 33#;
	PT _ (TS _ 34) -> cont 34#;
	PT _ (TS _ 35) -> cont 35#;
	PT _ (TS _ 36) -> cont 36#;
	PT _ (TS _ 37) -> cont 37#;
	PT _ (TS _ 38) -> cont 38#;
	PT _ (TS _ 39) -> cont 39#;
	PT _ (TS _ 40) -> cont 40#;
	PT _ (TS _ 41) -> cont 41#;
	PT _ (TS _ 42) -> cont 42#;
	PT _ (TS _ 43) -> cont 43#;
	PT _ (TS _ 44) -> cont 44#;
	PT _ (TS _ 45) -> cont 45#;
	PT _ (TS _ 46) -> cont 46#;
	PT _ (TS _ 47) -> cont 47#;
	PT _ (TS _ 48) -> cont 48#;
	PT _ (TS _ 49) -> cont 49#;
	PT _ (TS _ 50) -> cont 50#;
	PT _ (TS _ 51) -> cont 51#;
	PT _ (TS _ 52) -> cont 52#;
	PT _ (TS _ 53) -> cont 53#;
	PT _ (TS _ 54) -> cont 54#;
	PT _ (TS _ 55) -> cont 55#;
	PT _ (TS _ 56) -> cont 56#;
	PT _ (TS _ 57) -> cont 57#;
	PT _ (TI happy_dollar_dollar) -> cont 58#;
	PT _ (TC happy_dollar_dollar) -> cont 59#;
	PT _ (TL happy_dollar_dollar) -> cont 60#;
	PT _ (TD happy_dollar_dollar) -> cont 61#;
	PT _ (TV happy_dollar_dollar) -> cont 62#;
	_ -> cont 63#;
	_ -> happyError' (tk:tks)
	}

happyError_ 64# tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => [(Token)] -> Err a
happyError' = happyError

pProgram tks = happySomeParser where
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut18 x))

pDecl tks = happySomeParser where
  happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (happyOut20 x))

pRExpr tks = happySomeParser where
  happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (happyOut13 x))

pLExpr tks = happySomeParser where
  happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (happyOut15 x))

pStmt tks = happySomeParser where
  happySomeParser = happyThen (happyParse 4# tks) (\x -> happyReturn (happyOut29 x))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    t:_ -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}


















-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 







-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif



data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList


















infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}
          

          case action of
                0#           -> {- nothing -}
                                     happyFail i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}
                                                   
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}
                                     

                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = indexShortOffAddr happyActOffsets st
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st


indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#





data HappyAddr = HappyA# Happy_GHC_Exts.Addr#




-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = indexShortOffAddr happyGotoOffsets st1
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i



          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = indexShortOffAddr happyGotoOffsets st
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
