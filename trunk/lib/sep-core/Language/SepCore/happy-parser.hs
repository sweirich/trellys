{-# OPTIONS_GHC -w #-}
{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables,
  FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
  UndecidableInstances, TypeSynonymInstances  #-}

module Main  where
import Data.Char
import Unbound.LocallyNameless hiding (Con,Val,Equal,Refl)
import Unbound.LocallyNameless.Alpha(aeqR1)
import Unbound.LocallyNameless.Ops(unsafeUnbind)
import Text.Parsec.Pos
import Control.Monad(mplus)
import Control.Applicative((<$>), (<*>),Applicative)


import Data.Typeable

-- parser produced by Happy Version 1.18.6

data HappyAbsSyn t4 t5 t6 t7 t8 t9
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9

action_0 (14) = happyShift action_2
action_0 (4) = happyGoto action_3
action_0 _ = happyFail

action_1 (14) = happyShift action_2
action_1 _ = happyFail

action_2 (35) = happyShift action_4
action_2 _ = happyFail

action_3 (41) = happyAccept
action_3 _ = happyFail

action_4 (15) = happyShift action_6
action_4 (19) = happyShift action_7
action_4 (20) = happyShift action_8
action_4 (22) = happyShift action_9
action_4 (23) = happyShift action_10
action_4 (30) = happyShift action_11
action_4 (31) = happyShift action_12
action_4 (5) = happyGoto action_5
action_4 _ = happyFail

action_5 _ = happyReduce_1

action_6 _ = happyReduce_2

action_7 (10) = happyShift action_15
action_7 (16) = happyShift action_16
action_7 (18) = happyShift action_17
action_7 (21) = happyShift action_18
action_7 (26) = happyShift action_19
action_7 (31) = happyShift action_20
action_7 (8) = happyGoto action_28
action_7 _ = happyFail

action_8 (12) = happyShift action_27
action_8 _ = happyFail

action_9 (14) = happyShift action_24
action_9 (15) = happyShift action_25
action_9 (16) = happyShift action_26
action_9 _ = happyFail

action_10 (14) = happyShift action_21
action_10 (15) = happyShift action_22
action_10 (16) = happyShift action_23
action_10 _ = happyFail

action_11 (10) = happyShift action_15
action_11 (16) = happyShift action_16
action_11 (18) = happyShift action_17
action_11 (21) = happyShift action_18
action_11 (26) = happyShift action_19
action_11 (31) = happyShift action_20
action_11 (8) = happyGoto action_14
action_11 _ = happyFail

action_12 (15) = happyShift action_6
action_12 (19) = happyShift action_7
action_12 (20) = happyShift action_8
action_12 (22) = happyShift action_9
action_12 (23) = happyShift action_10
action_12 (30) = happyShift action_11
action_12 (31) = happyShift action_12
action_12 (5) = happyGoto action_13
action_12 _ = happyFail

action_13 (10) = happyShift action_15
action_13 (14) = happyShift action_50
action_13 (15) = happyShift action_6
action_13 (16) = happyShift action_16
action_13 (18) = happyShift action_17
action_13 (19) = happyShift action_7
action_13 (20) = happyShift action_8
action_13 (21) = happyShift action_18
action_13 (22) = happyShift action_9
action_13 (23) = happyShift action_10
action_13 (25) = happyShift action_51
action_13 (26) = happyShift action_19
action_13 (27) = happyShift action_52
action_13 (28) = happyShift action_53
action_13 (29) = happyShift action_54
action_13 (30) = happyShift action_11
action_13 (31) = happyShift action_55
action_13 (5) = happyGoto action_47
action_13 (8) = happyGoto action_48
action_13 (9) = happyGoto action_49
action_13 _ = happyFail

action_14 _ = happyReduce_13

action_15 (12) = happyShift action_46
action_15 _ = happyFail

action_16 _ = happyReduce_21

action_17 (14) = happyShift action_43
action_17 (15) = happyShift action_44
action_17 (16) = happyShift action_45
action_17 _ = happyFail

action_18 (14) = happyShift action_40
action_18 (15) = happyShift action_41
action_18 (16) = happyShift action_42
action_18 _ = happyFail

action_19 (10) = happyShift action_15
action_19 (16) = happyShift action_16
action_19 (18) = happyShift action_17
action_19 (21) = happyShift action_18
action_19 (26) = happyShift action_19
action_19 (31) = happyShift action_20
action_19 (8) = happyGoto action_39
action_19 _ = happyFail

action_20 (36) = happyShift action_37
action_20 (37) = happyShift action_38
action_20 (7) = happyGoto action_36
action_20 _ = happyFail

action_21 (39) = happyShift action_35
action_21 _ = happyFail

action_22 (39) = happyShift action_34
action_22 _ = happyFail

action_23 (39) = happyShift action_33
action_23 _ = happyFail

action_24 (39) = happyShift action_32
action_24 _ = happyFail

action_25 (39) = happyShift action_31
action_25 _ = happyFail

action_26 (39) = happyShift action_30
action_26 _ = happyFail

action_27 _ = happyReduce_14

action_28 (10) = happyShift action_15
action_28 (16) = happyShift action_16
action_28 (18) = happyShift action_17
action_28 (21) = happyShift action_18
action_28 (26) = happyShift action_19
action_28 (31) = happyShift action_20
action_28 (8) = happyGoto action_29
action_28 _ = happyFail

action_29 _ = happyReduce_12

action_30 (10) = happyShift action_15
action_30 (16) = happyShift action_16
action_30 (18) = happyShift action_17
action_30 (21) = happyShift action_18
action_30 (26) = happyShift action_19
action_30 (31) = happyShift action_20
action_30 (8) = happyGoto action_82
action_30 _ = happyFail

action_31 (17) = happyShift action_77
action_31 (24) = happyShift action_78
action_31 (6) = happyGoto action_81
action_31 _ = happyFail

action_32 (15) = happyShift action_6
action_32 (19) = happyShift action_7
action_32 (20) = happyShift action_8
action_32 (22) = happyShift action_9
action_32 (23) = happyShift action_10
action_32 (30) = happyShift action_11
action_32 (31) = happyShift action_12
action_32 (5) = happyGoto action_80
action_32 _ = happyFail

action_33 (10) = happyShift action_15
action_33 (16) = happyShift action_16
action_33 (18) = happyShift action_17
action_33 (21) = happyShift action_18
action_33 (26) = happyShift action_19
action_33 (31) = happyShift action_20
action_33 (8) = happyGoto action_79
action_33 _ = happyFail

action_34 (17) = happyShift action_77
action_34 (24) = happyShift action_78
action_34 (6) = happyGoto action_76
action_34 _ = happyFail

action_35 (15) = happyShift action_6
action_35 (19) = happyShift action_7
action_35 (20) = happyShift action_8
action_35 (22) = happyShift action_9
action_35 (23) = happyShift action_10
action_35 (30) = happyShift action_11
action_35 (31) = happyShift action_12
action_35 (5) = happyGoto action_75
action_35 _ = happyFail

action_36 (10) = happyShift action_15
action_36 (16) = happyShift action_16
action_36 (18) = happyShift action_17
action_36 (21) = happyShift action_18
action_36 (26) = happyShift action_19
action_36 (31) = happyShift action_20
action_36 (8) = happyGoto action_74
action_36 _ = happyFail

action_37 _ = happyReduce_19

action_38 _ = happyReduce_20

action_39 _ = happyReduce_32

action_40 (39) = happyShift action_73
action_40 _ = happyFail

action_41 (39) = happyShift action_72
action_41 _ = happyFail

action_42 (39) = happyShift action_71
action_42 _ = happyFail

action_43 (39) = happyShift action_70
action_43 _ = happyFail

action_44 (39) = happyShift action_69
action_44 _ = happyFail

action_45 (39) = happyShift action_68
action_45 _ = happyFail

action_46 _ = happyReduce_22

action_47 (32) = happyShift action_67
action_47 _ = happyFail

action_48 (32) = happyShift action_66
action_48 _ = happyFail

action_49 (32) = happyShift action_65
action_49 _ = happyFail

action_50 _ = happyReduce_33

action_51 (14) = happyShift action_62
action_51 (15) = happyShift action_63
action_51 (16) = happyShift action_64
action_51 _ = happyFail

action_52 (10) = happyShift action_15
action_52 (16) = happyShift action_16
action_52 (18) = happyShift action_17
action_52 (21) = happyShift action_18
action_52 (26) = happyShift action_19
action_52 (31) = happyShift action_20
action_52 (8) = happyGoto action_61
action_52 _ = happyFail

action_53 (14) = happyShift action_50
action_53 (25) = happyShift action_51
action_53 (27) = happyShift action_52
action_53 (28) = happyShift action_53
action_53 (29) = happyShift action_54
action_53 (31) = happyShift action_60
action_53 (9) = happyGoto action_59
action_53 _ = happyFail

action_54 (10) = happyShift action_15
action_54 (16) = happyShift action_16
action_54 (18) = happyShift action_17
action_54 (21) = happyShift action_18
action_54 (26) = happyShift action_19
action_54 (31) = happyShift action_20
action_54 (8) = happyGoto action_58
action_54 _ = happyFail

action_55 (14) = happyShift action_50
action_55 (15) = happyShift action_6
action_55 (19) = happyShift action_7
action_55 (20) = happyShift action_8
action_55 (22) = happyShift action_9
action_55 (23) = happyShift action_10
action_55 (25) = happyShift action_51
action_55 (27) = happyShift action_52
action_55 (28) = happyShift action_53
action_55 (29) = happyShift action_54
action_55 (30) = happyShift action_11
action_55 (31) = happyShift action_57
action_55 (36) = happyShift action_37
action_55 (37) = happyShift action_38
action_55 (5) = happyGoto action_13
action_55 (7) = happyGoto action_36
action_55 (9) = happyGoto action_56
action_55 _ = happyFail

action_56 (10) = happyShift action_15
action_56 (14) = happyShift action_50
action_56 (15) = happyShift action_6
action_56 (16) = happyShift action_16
action_56 (18) = happyShift action_17
action_56 (19) = happyShift action_7
action_56 (20) = happyShift action_8
action_56 (21) = happyShift action_18
action_56 (22) = happyShift action_9
action_56 (23) = happyShift action_10
action_56 (25) = happyShift action_51
action_56 (26) = happyShift action_19
action_56 (27) = happyShift action_52
action_56 (28) = happyShift action_53
action_56 (29) = happyShift action_54
action_56 (30) = happyShift action_11
action_56 (31) = happyShift action_55
action_56 (5) = happyGoto action_106
action_56 (8) = happyGoto action_107
action_56 (9) = happyGoto action_108
action_56 _ = happyFail

action_57 (14) = happyShift action_50
action_57 (15) = happyShift action_6
action_57 (19) = happyShift action_7
action_57 (20) = happyShift action_8
action_57 (22) = happyShift action_9
action_57 (23) = happyShift action_10
action_57 (25) = happyShift action_51
action_57 (27) = happyShift action_52
action_57 (28) = happyShift action_53
action_57 (29) = happyShift action_54
action_57 (30) = happyShift action_11
action_57 (31) = happyShift action_57
action_57 (5) = happyGoto action_13
action_57 (9) = happyGoto action_56
action_57 _ = happyFail

action_58 _ = happyReduce_42

action_59 _ = happyReduce_41

action_60 (14) = happyShift action_50
action_60 (25) = happyShift action_51
action_60 (27) = happyShift action_52
action_60 (28) = happyShift action_53
action_60 (29) = happyShift action_54
action_60 (31) = happyShift action_60
action_60 (9) = happyGoto action_56
action_60 _ = happyFail

action_61 (10) = happyShift action_15
action_61 (16) = happyShift action_16
action_61 (18) = happyShift action_17
action_61 (21) = happyShift action_18
action_61 (26) = happyShift action_19
action_61 (31) = happyShift action_20
action_61 (8) = happyGoto action_105
action_61 _ = happyFail

action_62 (39) = happyShift action_104
action_62 _ = happyFail

action_63 (39) = happyShift action_103
action_63 _ = happyFail

action_64 (39) = happyShift action_102
action_64 _ = happyFail

action_65 _ = happyReduce_9

action_66 _ = happyReduce_10

action_67 _ = happyReduce_11

action_68 (36) = happyShift action_37
action_68 (37) = happyShift action_38
action_68 (7) = happyGoto action_101
action_68 _ = happyFail

action_69 (36) = happyShift action_37
action_69 (37) = happyShift action_38
action_69 (7) = happyGoto action_100
action_69 _ = happyFail

action_70 (36) = happyShift action_37
action_70 (37) = happyShift action_38
action_70 (7) = happyGoto action_99
action_70 _ = happyFail

action_71 (36) = happyShift action_37
action_71 (37) = happyShift action_38
action_71 (7) = happyGoto action_98
action_71 _ = happyFail

action_72 (36) = happyShift action_37
action_72 (37) = happyShift action_38
action_72 (7) = happyGoto action_97
action_72 _ = happyFail

action_73 (36) = happyShift action_37
action_73 (37) = happyShift action_38
action_73 (7) = happyGoto action_96
action_73 _ = happyFail

action_74 (10) = happyShift action_15
action_74 (14) = happyShift action_50
action_74 (15) = happyShift action_6
action_74 (16) = happyShift action_16
action_74 (18) = happyShift action_17
action_74 (19) = happyShift action_7
action_74 (20) = happyShift action_8
action_74 (21) = happyShift action_18
action_74 (22) = happyShift action_9
action_74 (23) = happyShift action_10
action_74 (25) = happyShift action_51
action_74 (26) = happyShift action_19
action_74 (27) = happyShift action_52
action_74 (28) = happyShift action_53
action_74 (29) = happyShift action_54
action_74 (30) = happyShift action_11
action_74 (31) = happyShift action_55
action_74 (5) = happyGoto action_93
action_74 (8) = happyGoto action_94
action_74 (9) = happyGoto action_95
action_74 _ = happyFail

action_75 (40) = happyShift action_92
action_75 _ = happyFail

action_76 (40) = happyShift action_91
action_76 _ = happyFail

action_77 (12) = happyShift action_90
action_77 _ = happyFail

action_78 (14) = happyShift action_87
action_78 (15) = happyShift action_88
action_78 (16) = happyShift action_89
action_78 _ = happyFail

action_79 (40) = happyShift action_86
action_79 _ = happyFail

action_80 (40) = happyShift action_85
action_80 _ = happyFail

action_81 (40) = happyShift action_84
action_81 _ = happyFail

action_82 (40) = happyShift action_83
action_82 _ = happyFail

action_83 (15) = happyShift action_6
action_83 (19) = happyShift action_7
action_83 (20) = happyShift action_8
action_83 (22) = happyShift action_9
action_83 (23) = happyShift action_10
action_83 (30) = happyShift action_11
action_83 (31) = happyShift action_12
action_83 (5) = happyGoto action_132
action_83 _ = happyFail

action_84 (15) = happyShift action_6
action_84 (19) = happyShift action_7
action_84 (20) = happyShift action_8
action_84 (22) = happyShift action_9
action_84 (23) = happyShift action_10
action_84 (30) = happyShift action_11
action_84 (31) = happyShift action_12
action_84 (5) = happyGoto action_131
action_84 _ = happyFail

action_85 (15) = happyShift action_6
action_85 (19) = happyShift action_7
action_85 (20) = happyShift action_8
action_85 (22) = happyShift action_9
action_85 (23) = happyShift action_10
action_85 (30) = happyShift action_11
action_85 (31) = happyShift action_12
action_85 (5) = happyGoto action_130
action_85 _ = happyFail

action_86 (15) = happyShift action_6
action_86 (19) = happyShift action_7
action_86 (20) = happyShift action_8
action_86 (22) = happyShift action_9
action_86 (23) = happyShift action_10
action_86 (30) = happyShift action_11
action_86 (31) = happyShift action_12
action_86 (5) = happyGoto action_129
action_86 _ = happyFail

action_87 (39) = happyShift action_128
action_87 _ = happyFail

action_88 (39) = happyShift action_127
action_88 _ = happyFail

action_89 (39) = happyShift action_126
action_89 _ = happyFail

action_90 _ = happyReduce_15

action_91 (15) = happyShift action_6
action_91 (19) = happyShift action_7
action_91 (20) = happyShift action_8
action_91 (22) = happyShift action_9
action_91 (23) = happyShift action_10
action_91 (30) = happyShift action_11
action_91 (31) = happyShift action_12
action_91 (5) = happyGoto action_125
action_91 _ = happyFail

action_92 (15) = happyShift action_6
action_92 (19) = happyShift action_7
action_92 (20) = happyShift action_8
action_92 (22) = happyShift action_9
action_92 (23) = happyShift action_10
action_92 (30) = happyShift action_11
action_92 (31) = happyShift action_12
action_92 (5) = happyGoto action_124
action_92 _ = happyFail

action_93 (32) = happyShift action_123
action_93 _ = happyFail

action_94 (32) = happyShift action_122
action_94 _ = happyFail

action_95 (32) = happyShift action_121
action_95 _ = happyFail

action_96 (15) = happyShift action_6
action_96 (19) = happyShift action_7
action_96 (20) = happyShift action_8
action_96 (22) = happyShift action_9
action_96 (23) = happyShift action_10
action_96 (30) = happyShift action_11
action_96 (31) = happyShift action_12
action_96 (5) = happyGoto action_120
action_96 _ = happyFail

action_97 (17) = happyShift action_77
action_97 (24) = happyShift action_78
action_97 (6) = happyGoto action_119
action_97 _ = happyFail

action_98 (10) = happyShift action_15
action_98 (16) = happyShift action_16
action_98 (18) = happyShift action_17
action_98 (21) = happyShift action_18
action_98 (26) = happyShift action_19
action_98 (31) = happyShift action_20
action_98 (8) = happyGoto action_118
action_98 _ = happyFail

action_99 (15) = happyShift action_6
action_99 (19) = happyShift action_7
action_99 (20) = happyShift action_8
action_99 (22) = happyShift action_9
action_99 (23) = happyShift action_10
action_99 (30) = happyShift action_11
action_99 (31) = happyShift action_12
action_99 (5) = happyGoto action_117
action_99 _ = happyFail

action_100 (17) = happyShift action_77
action_100 (24) = happyShift action_78
action_100 (6) = happyGoto action_116
action_100 _ = happyFail

action_101 (10) = happyShift action_15
action_101 (16) = happyShift action_16
action_101 (18) = happyShift action_17
action_101 (21) = happyShift action_18
action_101 (26) = happyShift action_19
action_101 (31) = happyShift action_20
action_101 (8) = happyGoto action_115
action_101 _ = happyFail

action_102 (10) = happyShift action_15
action_102 (16) = happyShift action_16
action_102 (18) = happyShift action_17
action_102 (21) = happyShift action_18
action_102 (26) = happyShift action_19
action_102 (31) = happyShift action_20
action_102 (8) = happyGoto action_114
action_102 _ = happyFail

action_103 (17) = happyShift action_77
action_103 (24) = happyShift action_78
action_103 (6) = happyGoto action_113
action_103 _ = happyFail

action_104 (15) = happyShift action_6
action_104 (19) = happyShift action_7
action_104 (20) = happyShift action_8
action_104 (22) = happyShift action_9
action_104 (23) = happyShift action_10
action_104 (30) = happyShift action_11
action_104 (31) = happyShift action_12
action_104 (5) = happyGoto action_112
action_104 _ = happyFail

action_105 _ = happyReduce_37

action_106 (32) = happyShift action_111
action_106 _ = happyFail

action_107 (32) = happyShift action_110
action_107 _ = happyFail

action_108 (32) = happyShift action_109
action_108 _ = happyFail

action_109 _ = happyReduce_39

action_110 _ = happyReduce_38

action_111 _ = happyReduce_40

action_112 (40) = happyShift action_144
action_112 _ = happyFail

action_113 (40) = happyShift action_143
action_113 _ = happyFail

action_114 (40) = happyShift action_142
action_114 _ = happyFail

action_115 (40) = happyShift action_141
action_115 _ = happyFail

action_116 (40) = happyShift action_140
action_116 _ = happyFail

action_117 (40) = happyShift action_139
action_117 _ = happyFail

action_118 (40) = happyShift action_138
action_118 _ = happyFail

action_119 (40) = happyShift action_137
action_119 _ = happyFail

action_120 (40) = happyShift action_136
action_120 _ = happyFail

action_121 _ = happyReduce_27

action_122 _ = happyReduce_26

action_123 _ = happyReduce_28

action_124 _ = happyReduce_8

action_125 _ = happyReduce_6

action_126 (10) = happyShift action_15
action_126 (16) = happyShift action_16
action_126 (18) = happyShift action_17
action_126 (21) = happyShift action_18
action_126 (26) = happyShift action_19
action_126 (31) = happyShift action_20
action_126 (8) = happyGoto action_135
action_126 _ = happyFail

action_127 (17) = happyShift action_77
action_127 (24) = happyShift action_78
action_127 (6) = happyGoto action_134
action_127 _ = happyFail

action_128 (15) = happyShift action_6
action_128 (19) = happyShift action_7
action_128 (20) = happyShift action_8
action_128 (22) = happyShift action_9
action_128 (23) = happyShift action_10
action_128 (30) = happyShift action_11
action_128 (31) = happyShift action_12
action_128 (5) = happyGoto action_133
action_128 _ = happyFail

action_129 _ = happyReduce_7

action_130 _ = happyReduce_3

action_131 _ = happyReduce_4

action_132 _ = happyReduce_5

action_133 (40) = happyShift action_156
action_133 _ = happyFail

action_134 (40) = happyShift action_155
action_134 _ = happyFail

action_135 (40) = happyShift action_154
action_135 _ = happyFail

action_136 (10) = happyShift action_15
action_136 (16) = happyShift action_16
action_136 (18) = happyShift action_17
action_136 (21) = happyShift action_18
action_136 (26) = happyShift action_19
action_136 (31) = happyShift action_20
action_136 (8) = happyGoto action_153
action_136 _ = happyFail

action_137 (10) = happyShift action_15
action_137 (16) = happyShift action_16
action_137 (18) = happyShift action_17
action_137 (21) = happyShift action_18
action_137 (26) = happyShift action_19
action_137 (31) = happyShift action_20
action_137 (8) = happyGoto action_152
action_137 _ = happyFail

action_138 (10) = happyShift action_15
action_138 (16) = happyShift action_16
action_138 (18) = happyShift action_17
action_138 (21) = happyShift action_18
action_138 (26) = happyShift action_19
action_138 (31) = happyShift action_20
action_138 (8) = happyGoto action_151
action_138 _ = happyFail

action_139 (10) = happyShift action_15
action_139 (16) = happyShift action_16
action_139 (18) = happyShift action_17
action_139 (21) = happyShift action_18
action_139 (26) = happyShift action_19
action_139 (31) = happyShift action_20
action_139 (8) = happyGoto action_150
action_139 _ = happyFail

action_140 (10) = happyShift action_15
action_140 (16) = happyShift action_16
action_140 (18) = happyShift action_17
action_140 (21) = happyShift action_18
action_140 (26) = happyShift action_19
action_140 (31) = happyShift action_20
action_140 (8) = happyGoto action_149
action_140 _ = happyFail

action_141 (10) = happyShift action_15
action_141 (16) = happyShift action_16
action_141 (18) = happyShift action_17
action_141 (21) = happyShift action_18
action_141 (26) = happyShift action_19
action_141 (31) = happyShift action_20
action_141 (8) = happyGoto action_148
action_141 _ = happyFail

action_142 (14) = happyShift action_50
action_142 (25) = happyShift action_51
action_142 (27) = happyShift action_52
action_142 (28) = happyShift action_53
action_142 (29) = happyShift action_54
action_142 (31) = happyShift action_60
action_142 (9) = happyGoto action_147
action_142 _ = happyFail

action_143 (14) = happyShift action_50
action_143 (25) = happyShift action_51
action_143 (27) = happyShift action_52
action_143 (28) = happyShift action_53
action_143 (29) = happyShift action_54
action_143 (31) = happyShift action_60
action_143 (9) = happyGoto action_146
action_143 _ = happyFail

action_144 (14) = happyShift action_50
action_144 (25) = happyShift action_51
action_144 (27) = happyShift action_52
action_144 (28) = happyShift action_53
action_144 (29) = happyShift action_54
action_144 (31) = happyShift action_60
action_144 (9) = happyGoto action_145
action_144 _ = happyFail

action_145 _ = happyReduce_34

action_146 _ = happyReduce_35

action_147 _ = happyReduce_36

action_148 _ = happyReduce_24

action_149 _ = happyReduce_23

action_150 _ = happyReduce_25

action_151 _ = happyReduce_29

action_152 _ = happyReduce_31

action_153 _ = happyReduce_30

action_154 (17) = happyShift action_77
action_154 (24) = happyShift action_78
action_154 (6) = happyGoto action_159
action_154 _ = happyFail

action_155 (17) = happyShift action_77
action_155 (24) = happyShift action_78
action_155 (6) = happyGoto action_158
action_155 _ = happyFail

action_156 (17) = happyShift action_77
action_156 (24) = happyShift action_78
action_156 (6) = happyGoto action_157
action_156 _ = happyFail

action_157 _ = happyReduce_18

action_158 _ = happyReduce_16

action_159 _ = happyReduce_17

happyReduce_1 = happySpecReduce_3  4 happyReduction_1
happyReduction_1 (HappyAbsSyn5  happy_var_3)
	_
	(HappyTerminal (TokenProofVar happy_var_1))
	 =  HappyAbsSyn4
		 (Logicdecl happy_var_1 happy_var_3
	)
happyReduction_1 _ _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_1  5 happyReduction_2
happyReduction_2 (HappyTerminal (TokenPredVar happy_var_1))
	 =  HappyAbsSyn5
		 (PredicateVar (string2Name happy_var_1)
	)
happyReduction_2 _  = notHappyAtAll 

happyReduce_3 = happyReduce 6 5 happyReduction_3
happyReduction_3 ((HappyAbsSyn5  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (PredicateLambda (Bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_4 = happyReduce 6 5 happyReduction_4
happyReduction_4 ((HappyAbsSyn5  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (PredicateLambda (Bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_5 = happyReduce 6 5 happyReduction_5
happyReduction_5 ((HappyAbsSyn5  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (PredicateLambda (Bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_6 = happyReduce 6 5 happyReduction_6
happyReduction_6 ((HappyAbsSyn5  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Forall (Bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_7 = happyReduce 6 5 happyReduction_7
happyReduction_7 ((HappyAbsSyn5  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Forall (Bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_8 = happyReduce 6 5 happyReduction_8
happyReduction_8 ((HappyAbsSyn5  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Forall (Bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_9 = happyReduce 4 5 happyReduction_9
happyReduction_9 (_ `HappyStk`
	(HappyAbsSyn9  happy_var_3) `HappyStk`
	(HappyAbsSyn5  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (PredicateApplication happy_var_2 (ArgProof happy_var_3)
	) `HappyStk` happyRest

happyReduce_10 = happyReduce 4 5 happyReduction_10
happyReduction_10 (_ `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	(HappyAbsSyn5  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (PredicateApplication happy_var_2 (ArgTerm happy_var_3)
	) `HappyStk` happyRest

happyReduce_11 = happyReduce 4 5 happyReduction_11
happyReduction_11 (_ `HappyStk`
	(HappyAbsSyn5  happy_var_3) `HappyStk`
	(HappyAbsSyn5  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (PredicateApplication happy_var_2 (ArgPredicate happy_var_3)
	) `HappyStk` happyRest

happyReduce_12 = happySpecReduce_3  5 happyReduction_12
happyReduction_12 (HappyAbsSyn8  happy_var_3)
	(HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (Equal happy_var_2 happy_var_3
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_2  5 happyReduction_13
happyReduction_13 (HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (Terminate happy_var_2
	)
happyReduction_13 _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_2  5 happyReduction_14
happyReduction_14 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn5
		 (Bottom happy_var_2
	)
happyReduction_14 _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_2  6 happyReduction_15
happyReduction_15 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn6
		 (Formula happy_var_2
	)
happyReduction_15 _ _  = notHappyAtAll 

happyReduce_16 = happyReduce 6 6 happyReduction_16
happyReduction_16 ((HappyAbsSyn6  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (QuasiForall (Bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_17 = happyReduce 6 6 happyReduction_17
happyReduction_17 ((HappyAbsSyn6  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (QuasiForall (Bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_18 = happyReduce 6 6 happyReduction_18
happyReduction_18 ((HappyAbsSyn6  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (QuasiForall (Bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_19 = happySpecReduce_1  7 happyReduction_19
happyReduction_19 _
	 =  HappyAbsSyn7
		 (Plus
	)

happyReduce_20 = happySpecReduce_1  7 happyReduction_20
happyReduction_20 _
	 =  HappyAbsSyn7
		 (Minus
	)

happyReduce_21 = happySpecReduce_1  8 happyReduction_21
happyReduction_21 (HappyTerminal (TokenTermVar happy_var_1))
	 =  HappyAbsSyn8
		 (TermVar (string2name happy_var_1)
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_2  8 happyReduction_22
happyReduction_22 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn8
		 (Type happy_var_2
	)
happyReduction_22 _ _  = notHappyAtAll 

happyReduce_23 = happyReduce 7 8 happyReduction_23
happyReduction_23 ((HappyAbsSyn8  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_5) `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Pi (Bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_24 = happyReduce 7 8 happyReduction_24
happyReduction_24 ((HappyAbsSyn8  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_5) `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Pi (Bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_25 = happyReduce 7 8 happyReduction_25
happyReduction_25 ((HappyAbsSyn8  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_5) `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Pi (Bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_26 = happyReduce 5 8 happyReduction_26
happyReduction_26 (_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (TermApplication happy_var_3 (ArgTerm happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_27 = happyReduce 5 8 happyReduction_27
happyReduction_27 (_ `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (TermApplication happy_var_3 (ArgProof happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_28 = happyReduce 5 8 happyReduction_28
happyReduction_28 (_ `HappyStk`
	(HappyAbsSyn5  happy_var_4) `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (TermApplication happy_var_3 (ArgPredicate happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_29 = happyReduce 7 8 happyReduction_29
happyReduction_29 ((HappyAbsSyn8  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_5) `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (TermLambda (Bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_30 = happyReduce 7 8 happyReduction_30
happyReduction_30 ((HappyAbsSyn8  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_5) `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (TermLambda (Bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 7 8 happyReduction_31
happyReduction_31 ((HappyAbsSyn8  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_5) `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (TermLambda (Bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_32 = happySpecReduce_2  8 happyReduction_32
happyReduction_32 (HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (Abort happy_var_2
	)
happyReduction_32 _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_1  9 happyReduction_33
happyReduction_33 (HappyTerminal (TokenProofVar happy_var_1))
	 =  HappyAbsSyn9
		 (ProofVar (string2Name happy_var_1)
	)
happyReduction_33 _  = notHappyAtAll 

happyReduce_34 = happyReduce 6 9 happyReduction_34
happyReduction_34 ((HappyAbsSyn9  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (ProofLambda (Bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_35 = happyReduce 6 9 happyReduction_35
happyReduction_35 ((HappyAbsSyn9  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (ProofLambda (Bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_36 = happyReduce 6 9 happyReduction_36
happyReduction_36 ((HappyAbsSyn9  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (ProofLambda (Bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_37 = happySpecReduce_3  9 happyReduction_37
happyReduction_37 (HappyAbsSyn8  happy_var_3)
	(HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn9
		 (Join happy_var_2 happy_var_3
	)
happyReduction_37 _ _ _  = notHappyAtAll 

happyReduce_38 = happyReduce 4 9 happyReduction_38
happyReduction_38 (_ `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	(HappyAbsSyn9  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (ProofApplication happy_var_2 (ArgTerm happy_var_3)
	) `HappyStk` happyRest

happyReduce_39 = happyReduce 4 9 happyReduction_39
happyReduction_39 (_ `HappyStk`
	(HappyAbsSyn9  happy_var_3) `HappyStk`
	(HappyAbsSyn9  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (ProofApplication happy_var_2 (ArgProof happy_var_3)
	) `HappyStk` happyRest

happyReduce_40 = happyReduce 4 9 happyReduction_40
happyReduction_40 (_ `HappyStk`
	(HappyAbsSyn5  happy_var_3) `HappyStk`
	(HappyAbsSyn9  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (ProofApplication happy_var_2 (ArgPredicate happy_var_3)
	) `HappyStk` happyRest

happyReduce_41 = happySpecReduce_2  9 happyReduction_41
happyReduction_41 (HappyAbsSyn9  happy_var_2)
	_
	 =  HappyAbsSyn9
		 (Contra happy_var_2
	)
happyReduction_41 _ _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_2  9 happyReduction_42
happyReduction_42 (HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn9
		 (Valax happy_var_2
	)
happyReduction_42 _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 41 41 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenType -> cont 10;
	TokenData -> cont 11;
	TokenInt happy_dollar_dollar -> cont 12;
	TokenTheorem -> cont 13;
	TokenProofVar happy_dollar_dollar -> cont 14;
	TokenPredVar happy_dollar_dollar -> cont 15;
	TokenTermVar happy_dollar_dollar -> cont 16;
	TokeFm -> cont 17;
	TokenPi -> cont 18;
	TokenEq -> cont 19;
	TokenBot -> cont 20;
	TokenLM -> cont 21;
	TokenLamb -> cont 22;
	TokenForall -> cont 23;
	TokenQF -> cont 24;
	TokenPlam -> cont 25;
	TokenAb -> cont 26;
	TokenJoin -> cont 27;
	TokenContr -> cont 28;
	TokenValax -> cont 29;
	TokenEx -> cont 30;
	TokenBL -> cont 31;
	TokenBR -> cont 32;
	TokenBll -> cont 33;
	TokenBrr -> cont 34;
	TokenDC -> cont 35;
	TokenPlus -> cont 36;
	TokenMinus -> cont 37;
	TokenDef -> cont 38;
	TokenCL -> cont 39;
	TokenDot -> cont 40;
	_ -> happyError' (tk:tks)
	}

happyError_ tk tks = happyError' (tk:tks)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Monad HappyIdentity where
    return = HappyIdentity
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(Token)] -> HappyIdentity a
happyError' = HappyIdentity . parseError

parser tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


data Token =

       TokenType

       | TokenData

       | TokenInt Integer

       | TokenForall
 
       | TokenQF
 
       | TokenPlam

       | TokenTheorem

       | TokenProofVar String

       | TokenPredVar String

       | TokenTermVar String

       | TokeFm 

       | TokenPi

       | TokenEq

       | TokenBot

       | TokenLM

       | TokenLamb

       | TokenAb

       | TokenJoin

       | TokenContr

       | TokenValax

       | TokenEx

       | TokenBL

       | TokenBR

       | TokenBll

       | TokenBrr

       | TokenDC

       | TokenPlus

       | TokenMinus

       | TokenDef

       | TokenCL

       | TokenDot

		  deriving (Show)

parseError :: [Token] -> a
parseError _ = error "Parse error"

data Logicdecl = Logicdecl String Predicate 
             deriving (Show)
  
data Stage = Plus | Minus deriving(Show)

data LogicalKind = Formula Integer

         | QuasiForall ArgClass LogicalKind

  deriving(Show)

data Predicate = PredicateVar (Name Predicate)

           | PredicateLambda (Bind (ArgName, Embed ArgClass) Predicate)

           | PredicateApplication Predicate Arg

           | Forall (Bind (ArgName, Embed ArgClass) Predicate)

           | Equal Term Term

           | Terminate Term

           | Bottom Integer

  deriving(Show)

data Proof =  ProofVar (Name Proof)

             | ProofLambda (Bind (ArgName, Embed ArgClass) Proof)

             | ProofApplication Proof Arg

             | Join Term Term

             | Valax Term

             | Contra Proof
                      
    deriving(Show)

data Term =  TermVar (Name Term)

           | Type Integer

           | Pi (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermLambda (Bind (ArgName, Embed ArgClass) Term) Stage

           | TermApplication Term Arg Stage

           | Abort Term


  deriving(Show)

data ArgClass = ArgClassTerm Term

               | ArgClassPredicate Predicate

               | ArgClassLogicalKind LogicalKind

      deriving(Show)

data Arg = ArgTerm Term

          | ArgProof Proof

          | ArgPredicate Predicate

        deriving(Show)

data ArgName = ArgNameProof (Name Proof)
           
          | ArgNameTerm (Name Term)
        
          | ArgNamePredicate (Name Predicate)   

         deriving Show


$(derive [''Proof,''Term, ''Predicate, ''Arg, ''ArgName, ''Stage, ''ArgClass, ''LogicalKind])

instance Subst LogicalKind Stage
instance Subst LogicalKind ArgName

instance Subst LogicalKind Arg
instance Subst LogicalKind ArgClass
instance Subst LogicalKind Predicate
instance Subst LogicalKind Term
instance Subst LogicalKind Proof
instance Subst LogicalKind LogicalKind

instance Subst Arg Stage
instance Subst Arg ArgName
instance Subst Arg ArgClass
instance Subst Arg LogicalKind
instance Subst Arg Arg 

instance Subst Arg Predicate where
  subst n (ArgPredicate pd) prd = subst (translate n) pd prd
  subst n a prd = substR1 rep1 n a prd

-- | here we do a implicit mutually recursive call on the 'substR1' defined in (Subst Arg Term) and (Subst Arg Proof)

instance Subst Arg Term where
  subst n (ArgTerm t) tm = subst (translate n) t tm
  subst n a tm = substR1 rep1 n a tm

instance Subst Arg Proof where
  subst n (ArgProof p) pf = subst (translate n) p pf
  subst n a pf = substR1 rep1 n a pf

instance Subst Proof Arg
instance Subst Proof ArgName
instance Subst Proof Term 
instance Subst Proof Predicate 
instance Subst Proof Stage
instance Subst Proof LogicalKind
instance Subst Proof ArgClass
instance Subst Proof Proof where
  isvar (ProofVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Term Arg
instance Subst Term ArgClass
instance Subst Term ArgName
instance Subst Term Proof 
instance Subst Term Predicate 
instance Subst Term LogicalKind
instance Subst Term Stage
instance Subst Term Term where
  isvar (TermVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Predicate Term 
instance Subst Predicate Proof
instance Subst Predicate LogicalKind
instance Subst Predicate Stage
instance Subst Predicate Arg
instance Subst Predicate ArgClass
instance Subst Predicate ArgName
instance Subst Predicate Predicate where
        isvar (PredicateVar x) = Just (SubstName x)
        isvar _ = Nothing




instance Alpha Predicate
instance Alpha Term
instance Alpha Proof
instance Alpha LogicalKind
instance Alpha Stage
instance Alpha ArgClass
instance Alpha Arg
instance Alpha ArgName



lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
      | isSpace c = lexer cs
      | isAlpha c = lexVar (c:cs)
      | isDigit c = lexNum (c:cs)

lexer ('!': cs) = TokenEx : lexer cs 
lexer ('[': cs) = TokenBll : lexer cs
lexer (']': cs) = TokenBrr : lexer cs
lexer ('.': cs) = TokenDot : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('-':cs) = TokenMinus : lexer cs
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer (':': cs) = case cs of
		  (':': css) -> TokenDC : lexer css
		  ('=': css) -> TokenDef : lexer css
		  ( _ : css) -> TokenCL : lexer cs
		 
lexer ('$': cs) = case span isAlpha cs of
		  (proofvar, rest) -> TokenProofVar proofvar : lexer rest 

lexer ('#': cs) = case span isAlpha cs of
		  (predvar, rest) -> TokenPredVar predvar : lexer rest 


lexNum cs = TokenInt (read num) : lexer rest
      where (num,rest) = span isDigit cs

lexVar cs =
    case span isAlpha cs of
      ("valax",rest) -> TokenValax : lexer rest
      ("contr",rest)  -> TokenContr : lexer rest
      ("join",rest)  -> TokenJoin : lexer rest
      ("abort",rest)  -> TokenAb : lexer rest
      ("Lambda",rest)  -> TokenLamb : lexer rest
      ("lambda",rest)  -> TokenLM : lexer rest
      ("Bottom",rest)  -> TokenBot : lexer rest
      ("Eq",rest)  -> TokenEq : lexer rest
      ("Pi",rest)  -> TokenPi : lexer rest
      ("formula",rest)  -> TokenFm : lexer rest
      ("type",rest)  -> TokenType : lexer rest
      ("data",rest)  -> TokenData : lexer rest
      ("theorem",rest)  -> TokenTheorem : lexer rest
      (var,rest) -> TokenTermVar var : lexer rest
      


{- Our temp main loop. -}
main = getContents >>= print . parser . lexer
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates/GenericTemplate.hs" #-}








{-# LINE 51 "templates/GenericTemplate.hs" #-}

{-# LINE 61 "templates/GenericTemplate.hs" #-}

{-# LINE 70 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	 (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 148 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
	 sts1@(((st1@(HappyState (action))):(_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk





             new_state = action


happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 246 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail  (1) tk old_st _ stk =
--	trace "failing" $ 
    	happyError_ tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
	action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 311 "templates/GenericTemplate.hs" #-}
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
