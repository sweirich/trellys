{-# OPTIONS_GHC -w #-}
module Language.SepCore.Happyparser where 
import Language.SepCore.Syntax
import Data.Char
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)

-- parser produced by Happy Version 1.18.6

data HappyAbsSyn t7 t8 t9 t10 t11 t12
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12

action_0 (18) = happyShift action_24
action_0 (22) = happyShift action_25
action_0 (23) = happyShift action_26
action_0 (25) = happyShift action_27
action_0 (26) = happyShift action_28
action_0 (33) = happyShift action_29
action_0 (34) = happyShift action_30
action_0 (8) = happyGoto action_23
action_0 _ = happyFail

action_1 (17) = happyShift action_17
action_1 (28) = happyShift action_18
action_1 (30) = happyShift action_19
action_1 (31) = happyShift action_20
action_1 (32) = happyShift action_21
action_1 (34) = happyShift action_22
action_1 (12) = happyGoto action_16
action_1 _ = happyFail

action_2 (13) = happyShift action_10
action_2 (19) = happyShift action_11
action_2 (21) = happyShift action_12
action_2 (24) = happyShift action_13
action_2 (29) = happyShift action_14
action_2 (34) = happyShift action_15
action_2 (11) = happyGoto action_9
action_2 _ = happyFail

action_3 (20) = happyShift action_7
action_3 (27) = happyShift action_8
action_3 (9) = happyGoto action_6
action_3 _ = happyFail

action_4 (17) = happyShift action_5
action_4 _ = happyFail

action_5 (38) = happyShift action_64
action_5 _ = happyFail

action_6 (44) = happyAccept
action_6 _ = happyFail

action_7 (15) = happyShift action_63
action_7 _ = happyFail

action_8 (13) = happyShift action_10
action_8 (18) = happyShift action_24
action_8 (19) = happyShift action_11
action_8 (20) = happyShift action_7
action_8 (21) = happyShift action_12
action_8 (22) = happyShift action_25
action_8 (23) = happyShift action_26
action_8 (24) = happyShift action_13
action_8 (25) = happyShift action_27
action_8 (26) = happyShift action_28
action_8 (27) = happyShift action_8
action_8 (29) = happyShift action_14
action_8 (33) = happyShift action_29
action_8 (34) = happyShift action_62
action_8 (8) = happyGoto action_59
action_8 (9) = happyGoto action_60
action_8 (11) = happyGoto action_61
action_8 _ = happyFail

action_9 (44) = happyAccept
action_9 _ = happyFail

action_10 (15) = happyShift action_58
action_10 _ = happyFail

action_11 _ = happyReduce_24

action_12 (17) = happyShift action_55
action_12 (18) = happyShift action_56
action_12 (19) = happyShift action_57
action_12 _ = happyFail

action_13 (17) = happyShift action_52
action_13 (18) = happyShift action_53
action_13 (19) = happyShift action_54
action_13 _ = happyFail

action_14 (13) = happyShift action_10
action_14 (19) = happyShift action_11
action_14 (21) = happyShift action_12
action_14 (24) = happyShift action_13
action_14 (29) = happyShift action_14
action_14 (34) = happyShift action_15
action_14 (11) = happyGoto action_51
action_14 _ = happyFail

action_15 (39) = happyShift action_49
action_15 (40) = happyShift action_50
action_15 (10) = happyGoto action_48
action_15 _ = happyFail

action_16 (44) = happyAccept
action_16 _ = happyFail

action_17 _ = happyReduce_36

action_18 (17) = happyShift action_45
action_18 (18) = happyShift action_46
action_18 (19) = happyShift action_47
action_18 _ = happyFail

action_19 (13) = happyShift action_10
action_19 (19) = happyShift action_11
action_19 (21) = happyShift action_12
action_19 (24) = happyShift action_13
action_19 (29) = happyShift action_14
action_19 (34) = happyShift action_15
action_19 (11) = happyGoto action_44
action_19 _ = happyFail

action_20 (17) = happyShift action_17
action_20 (28) = happyShift action_18
action_20 (30) = happyShift action_19
action_20 (31) = happyShift action_20
action_20 (32) = happyShift action_21
action_20 (34) = happyShift action_22
action_20 (12) = happyGoto action_43
action_20 _ = happyFail

action_21 (13) = happyShift action_10
action_21 (19) = happyShift action_11
action_21 (21) = happyShift action_12
action_21 (24) = happyShift action_13
action_21 (29) = happyShift action_14
action_21 (34) = happyShift action_15
action_21 (11) = happyGoto action_42
action_21 _ = happyFail

action_22 (17) = happyShift action_17
action_22 (28) = happyShift action_18
action_22 (30) = happyShift action_19
action_22 (31) = happyShift action_20
action_22 (32) = happyShift action_21
action_22 (34) = happyShift action_22
action_22 (12) = happyGoto action_41
action_22 _ = happyFail

action_23 (44) = happyAccept
action_23 _ = happyFail

action_24 _ = happyReduce_5

action_25 (13) = happyShift action_10
action_25 (19) = happyShift action_11
action_25 (21) = happyShift action_12
action_25 (24) = happyShift action_13
action_25 (29) = happyShift action_14
action_25 (34) = happyShift action_15
action_25 (11) = happyGoto action_40
action_25 _ = happyFail

action_26 (15) = happyShift action_39
action_26 _ = happyFail

action_27 (17) = happyShift action_36
action_27 (18) = happyShift action_37
action_27 (19) = happyShift action_38
action_27 _ = happyFail

action_28 (17) = happyShift action_33
action_28 (18) = happyShift action_34
action_28 (19) = happyShift action_35
action_28 _ = happyFail

action_29 (13) = happyShift action_10
action_29 (19) = happyShift action_11
action_29 (21) = happyShift action_12
action_29 (24) = happyShift action_13
action_29 (29) = happyShift action_14
action_29 (34) = happyShift action_15
action_29 (11) = happyGoto action_32
action_29 _ = happyFail

action_30 (18) = happyShift action_24
action_30 (22) = happyShift action_25
action_30 (23) = happyShift action_26
action_30 (25) = happyShift action_27
action_30 (26) = happyShift action_28
action_30 (33) = happyShift action_29
action_30 (34) = happyShift action_30
action_30 (8) = happyGoto action_31
action_30 _ = happyFail

action_31 (13) = happyShift action_10
action_31 (17) = happyShift action_17
action_31 (18) = happyShift action_24
action_31 (19) = happyShift action_11
action_31 (21) = happyShift action_12
action_31 (22) = happyShift action_25
action_31 (23) = happyShift action_26
action_31 (24) = happyShift action_13
action_31 (25) = happyShift action_27
action_31 (26) = happyShift action_28
action_31 (28) = happyShift action_18
action_31 (29) = happyShift action_14
action_31 (30) = happyShift action_19
action_31 (31) = happyShift action_20
action_31 (32) = happyShift action_21
action_31 (33) = happyShift action_29
action_31 (34) = happyShift action_83
action_31 (8) = happyGoto action_91
action_31 (11) = happyGoto action_92
action_31 (12) = happyGoto action_93
action_31 _ = happyFail

action_32 _ = happyReduce_16

action_33 (42) = happyShift action_90
action_33 _ = happyFail

action_34 (42) = happyShift action_89
action_34 _ = happyFail

action_35 (42) = happyShift action_88
action_35 _ = happyFail

action_36 (42) = happyShift action_87
action_36 _ = happyFail

action_37 (42) = happyShift action_86
action_37 _ = happyFail

action_38 (42) = happyShift action_85
action_38 _ = happyFail

action_39 _ = happyReduce_17

action_40 (13) = happyShift action_10
action_40 (19) = happyShift action_11
action_40 (21) = happyShift action_12
action_40 (24) = happyShift action_13
action_40 (29) = happyShift action_14
action_40 (34) = happyShift action_15
action_40 (11) = happyGoto action_84
action_40 _ = happyFail

action_41 (13) = happyShift action_10
action_41 (17) = happyShift action_17
action_41 (18) = happyShift action_24
action_41 (19) = happyShift action_11
action_41 (21) = happyShift action_12
action_41 (22) = happyShift action_25
action_41 (23) = happyShift action_26
action_41 (24) = happyShift action_13
action_41 (25) = happyShift action_27
action_41 (26) = happyShift action_28
action_41 (28) = happyShift action_18
action_41 (29) = happyShift action_14
action_41 (30) = happyShift action_19
action_41 (31) = happyShift action_20
action_41 (32) = happyShift action_21
action_41 (33) = happyShift action_29
action_41 (34) = happyShift action_83
action_41 (8) = happyGoto action_80
action_41 (11) = happyGoto action_81
action_41 (12) = happyGoto action_82
action_41 _ = happyFail

action_42 _ = happyReduce_45

action_43 _ = happyReduce_44

action_44 (13) = happyShift action_10
action_44 (19) = happyShift action_11
action_44 (21) = happyShift action_12
action_44 (24) = happyShift action_13
action_44 (29) = happyShift action_14
action_44 (34) = happyShift action_15
action_44 (11) = happyGoto action_79
action_44 _ = happyFail

action_45 (42) = happyShift action_78
action_45 _ = happyFail

action_46 (42) = happyShift action_77
action_46 _ = happyFail

action_47 (42) = happyShift action_76
action_47 _ = happyFail

action_48 (13) = happyShift action_10
action_48 (19) = happyShift action_11
action_48 (21) = happyShift action_12
action_48 (24) = happyShift action_13
action_48 (29) = happyShift action_14
action_48 (34) = happyShift action_15
action_48 (11) = happyGoto action_75
action_48 _ = happyFail

action_49 _ = happyReduce_22

action_50 _ = happyReduce_23

action_51 _ = happyReduce_35

action_52 (42) = happyShift action_74
action_52 _ = happyFail

action_53 (42) = happyShift action_73
action_53 _ = happyFail

action_54 (42) = happyShift action_72
action_54 _ = happyFail

action_55 (42) = happyShift action_71
action_55 _ = happyFail

action_56 (42) = happyShift action_70
action_56 _ = happyFail

action_57 (42) = happyShift action_69
action_57 _ = happyFail

action_58 _ = happyReduce_25

action_59 (43) = happyShift action_68
action_59 _ = happyFail

action_60 (43) = happyShift action_67
action_60 _ = happyFail

action_61 (43) = happyShift action_66
action_61 _ = happyFail

action_62 (18) = happyShift action_24
action_62 (22) = happyShift action_25
action_62 (23) = happyShift action_26
action_62 (25) = happyShift action_27
action_62 (26) = happyShift action_28
action_62 (33) = happyShift action_29
action_62 (34) = happyShift action_30
action_62 (39) = happyShift action_49
action_62 (40) = happyShift action_50
action_62 (8) = happyGoto action_31
action_62 (10) = happyGoto action_48
action_62 _ = happyFail

action_63 _ = happyReduce_18

action_64 (18) = happyShift action_24
action_64 (22) = happyShift action_25
action_64 (23) = happyShift action_26
action_64 (25) = happyShift action_27
action_64 (26) = happyShift action_28
action_64 (33) = happyShift action_29
action_64 (34) = happyShift action_30
action_64 (8) = happyGoto action_65
action_64 _ = happyFail

action_65 _ = happyFail

action_66 (20) = happyShift action_7
action_66 (27) = happyShift action_8
action_66 (9) = happyGoto action_121
action_66 _ = happyFail

action_67 (20) = happyShift action_7
action_67 (27) = happyShift action_8
action_67 (9) = happyGoto action_120
action_67 _ = happyFail

action_68 (20) = happyShift action_7
action_68 (27) = happyShift action_8
action_68 (9) = happyGoto action_119
action_68 _ = happyFail

action_69 (39) = happyShift action_49
action_69 (40) = happyShift action_50
action_69 (10) = happyGoto action_118
action_69 _ = happyFail

action_70 (39) = happyShift action_49
action_70 (40) = happyShift action_50
action_70 (10) = happyGoto action_117
action_70 _ = happyFail

action_71 (39) = happyShift action_49
action_71 (40) = happyShift action_50
action_71 (10) = happyGoto action_116
action_71 _ = happyFail

action_72 (39) = happyShift action_49
action_72 (40) = happyShift action_50
action_72 (10) = happyGoto action_115
action_72 _ = happyFail

action_73 (39) = happyShift action_49
action_73 (40) = happyShift action_50
action_73 (10) = happyGoto action_114
action_73 _ = happyFail

action_74 (39) = happyShift action_49
action_74 (40) = happyShift action_50
action_74 (10) = happyGoto action_113
action_74 _ = happyFail

action_75 (13) = happyShift action_10
action_75 (17) = happyShift action_17
action_75 (18) = happyShift action_24
action_75 (19) = happyShift action_11
action_75 (21) = happyShift action_12
action_75 (22) = happyShift action_25
action_75 (23) = happyShift action_26
action_75 (24) = happyShift action_13
action_75 (25) = happyShift action_27
action_75 (26) = happyShift action_28
action_75 (28) = happyShift action_18
action_75 (29) = happyShift action_14
action_75 (30) = happyShift action_19
action_75 (31) = happyShift action_20
action_75 (32) = happyShift action_21
action_75 (33) = happyShift action_29
action_75 (34) = happyShift action_83
action_75 (8) = happyGoto action_110
action_75 (11) = happyGoto action_111
action_75 (12) = happyGoto action_112
action_75 _ = happyFail

action_76 (13) = happyShift action_10
action_76 (19) = happyShift action_11
action_76 (21) = happyShift action_12
action_76 (24) = happyShift action_13
action_76 (29) = happyShift action_14
action_76 (34) = happyShift action_15
action_76 (11) = happyGoto action_109
action_76 _ = happyFail

action_77 (20) = happyShift action_7
action_77 (27) = happyShift action_8
action_77 (9) = happyGoto action_108
action_77 _ = happyFail

action_78 (18) = happyShift action_24
action_78 (22) = happyShift action_25
action_78 (23) = happyShift action_26
action_78 (25) = happyShift action_27
action_78 (26) = happyShift action_28
action_78 (33) = happyShift action_29
action_78 (34) = happyShift action_30
action_78 (8) = happyGoto action_107
action_78 _ = happyFail

action_79 _ = happyReduce_40

action_80 (35) = happyShift action_106
action_80 _ = happyFail

action_81 (35) = happyShift action_105
action_81 _ = happyFail

action_82 (35) = happyShift action_104
action_82 _ = happyFail

action_83 (17) = happyShift action_17
action_83 (18) = happyShift action_24
action_83 (22) = happyShift action_25
action_83 (23) = happyShift action_26
action_83 (25) = happyShift action_27
action_83 (26) = happyShift action_28
action_83 (28) = happyShift action_18
action_83 (30) = happyShift action_19
action_83 (31) = happyShift action_20
action_83 (32) = happyShift action_21
action_83 (33) = happyShift action_29
action_83 (34) = happyShift action_103
action_83 (39) = happyShift action_49
action_83 (40) = happyShift action_50
action_83 (8) = happyGoto action_31
action_83 (10) = happyGoto action_48
action_83 (12) = happyGoto action_41
action_83 _ = happyFail

action_84 _ = happyReduce_15

action_85 (13) = happyShift action_10
action_85 (19) = happyShift action_11
action_85 (21) = happyShift action_12
action_85 (24) = happyShift action_13
action_85 (29) = happyShift action_14
action_85 (34) = happyShift action_15
action_85 (11) = happyGoto action_102
action_85 _ = happyFail

action_86 (20) = happyShift action_7
action_86 (27) = happyShift action_8
action_86 (9) = happyGoto action_101
action_86 _ = happyFail

action_87 (18) = happyShift action_24
action_87 (22) = happyShift action_25
action_87 (23) = happyShift action_26
action_87 (25) = happyShift action_27
action_87 (26) = happyShift action_28
action_87 (33) = happyShift action_29
action_87 (34) = happyShift action_30
action_87 (8) = happyGoto action_100
action_87 _ = happyFail

action_88 (13) = happyShift action_10
action_88 (19) = happyShift action_11
action_88 (21) = happyShift action_12
action_88 (24) = happyShift action_13
action_88 (29) = happyShift action_14
action_88 (34) = happyShift action_15
action_88 (11) = happyGoto action_99
action_88 _ = happyFail

action_89 (20) = happyShift action_7
action_89 (27) = happyShift action_8
action_89 (9) = happyGoto action_98
action_89 _ = happyFail

action_90 (18) = happyShift action_24
action_90 (22) = happyShift action_25
action_90 (23) = happyShift action_26
action_90 (25) = happyShift action_27
action_90 (26) = happyShift action_28
action_90 (33) = happyShift action_29
action_90 (34) = happyShift action_30
action_90 (8) = happyGoto action_97
action_90 _ = happyFail

action_91 (35) = happyShift action_96
action_91 _ = happyFail

action_92 (35) = happyShift action_95
action_92 _ = happyFail

action_93 (35) = happyShift action_94
action_93 _ = happyFail

action_94 _ = happyReduce_12

action_95 _ = happyReduce_13

action_96 _ = happyReduce_14

action_97 (43) = happyShift action_139
action_97 _ = happyFail

action_98 (43) = happyShift action_138
action_98 _ = happyFail

action_99 (43) = happyShift action_137
action_99 _ = happyFail

action_100 (43) = happyShift action_136
action_100 _ = happyFail

action_101 (43) = happyShift action_135
action_101 _ = happyFail

action_102 (43) = happyShift action_134
action_102 _ = happyFail

action_103 (17) = happyShift action_17
action_103 (18) = happyShift action_24
action_103 (22) = happyShift action_25
action_103 (23) = happyShift action_26
action_103 (25) = happyShift action_27
action_103 (26) = happyShift action_28
action_103 (28) = happyShift action_18
action_103 (30) = happyShift action_19
action_103 (31) = happyShift action_20
action_103 (32) = happyShift action_21
action_103 (33) = happyShift action_29
action_103 (34) = happyShift action_103
action_103 (8) = happyGoto action_31
action_103 (12) = happyGoto action_41
action_103 _ = happyFail

action_104 _ = happyReduce_42

action_105 _ = happyReduce_41

action_106 _ = happyReduce_43

action_107 (43) = happyShift action_133
action_107 _ = happyFail

action_108 (43) = happyShift action_132
action_108 _ = happyFail

action_109 (43) = happyShift action_131
action_109 _ = happyFail

action_110 (35) = happyShift action_130
action_110 _ = happyFail

action_111 (35) = happyShift action_129
action_111 _ = happyFail

action_112 (35) = happyShift action_128
action_112 _ = happyFail

action_113 (18) = happyShift action_24
action_113 (22) = happyShift action_25
action_113 (23) = happyShift action_26
action_113 (25) = happyShift action_27
action_113 (26) = happyShift action_28
action_113 (33) = happyShift action_29
action_113 (34) = happyShift action_30
action_113 (8) = happyGoto action_127
action_113 _ = happyFail

action_114 (20) = happyShift action_7
action_114 (27) = happyShift action_8
action_114 (9) = happyGoto action_126
action_114 _ = happyFail

action_115 (13) = happyShift action_10
action_115 (19) = happyShift action_11
action_115 (21) = happyShift action_12
action_115 (24) = happyShift action_13
action_115 (29) = happyShift action_14
action_115 (34) = happyShift action_15
action_115 (11) = happyGoto action_125
action_115 _ = happyFail

action_116 (18) = happyShift action_24
action_116 (22) = happyShift action_25
action_116 (23) = happyShift action_26
action_116 (25) = happyShift action_27
action_116 (26) = happyShift action_28
action_116 (33) = happyShift action_29
action_116 (34) = happyShift action_30
action_116 (8) = happyGoto action_124
action_116 _ = happyFail

action_117 (20) = happyShift action_7
action_117 (27) = happyShift action_8
action_117 (9) = happyGoto action_123
action_117 _ = happyFail

action_118 (13) = happyShift action_10
action_118 (19) = happyShift action_11
action_118 (21) = happyShift action_12
action_118 (24) = happyShift action_13
action_118 (29) = happyShift action_14
action_118 (34) = happyShift action_15
action_118 (11) = happyGoto action_122
action_118 _ = happyFail

action_119 _ = happyReduce_21

action_120 _ = happyReduce_19

action_121 _ = happyReduce_20

action_122 (43) = happyShift action_154
action_122 _ = happyFail

action_123 (43) = happyShift action_153
action_123 _ = happyFail

action_124 (43) = happyShift action_152
action_124 _ = happyFail

action_125 (43) = happyShift action_151
action_125 _ = happyFail

action_126 (43) = happyShift action_150
action_126 _ = happyFail

action_127 (43) = happyShift action_149
action_127 _ = happyFail

action_128 _ = happyReduce_30

action_129 _ = happyReduce_29

action_130 _ = happyReduce_31

action_131 (17) = happyShift action_17
action_131 (28) = happyShift action_18
action_131 (30) = happyShift action_19
action_131 (31) = happyShift action_20
action_131 (32) = happyShift action_21
action_131 (34) = happyShift action_22
action_131 (12) = happyGoto action_148
action_131 _ = happyFail

action_132 (17) = happyShift action_17
action_132 (28) = happyShift action_18
action_132 (30) = happyShift action_19
action_132 (31) = happyShift action_20
action_132 (32) = happyShift action_21
action_132 (34) = happyShift action_22
action_132 (12) = happyGoto action_147
action_132 _ = happyFail

action_133 (17) = happyShift action_17
action_133 (28) = happyShift action_18
action_133 (30) = happyShift action_19
action_133 (31) = happyShift action_20
action_133 (32) = happyShift action_21
action_133 (34) = happyShift action_22
action_133 (12) = happyGoto action_146
action_133 _ = happyFail

action_134 (18) = happyShift action_24
action_134 (22) = happyShift action_25
action_134 (23) = happyShift action_26
action_134 (25) = happyShift action_27
action_134 (26) = happyShift action_28
action_134 (33) = happyShift action_29
action_134 (34) = happyShift action_30
action_134 (8) = happyGoto action_145
action_134 _ = happyFail

action_135 (18) = happyShift action_24
action_135 (22) = happyShift action_25
action_135 (23) = happyShift action_26
action_135 (25) = happyShift action_27
action_135 (26) = happyShift action_28
action_135 (33) = happyShift action_29
action_135 (34) = happyShift action_30
action_135 (8) = happyGoto action_144
action_135 _ = happyFail

action_136 (18) = happyShift action_24
action_136 (22) = happyShift action_25
action_136 (23) = happyShift action_26
action_136 (25) = happyShift action_27
action_136 (26) = happyShift action_28
action_136 (33) = happyShift action_29
action_136 (34) = happyShift action_30
action_136 (8) = happyGoto action_143
action_136 _ = happyFail

action_137 (18) = happyShift action_24
action_137 (22) = happyShift action_25
action_137 (23) = happyShift action_26
action_137 (25) = happyShift action_27
action_137 (26) = happyShift action_28
action_137 (33) = happyShift action_29
action_137 (34) = happyShift action_30
action_137 (8) = happyGoto action_142
action_137 _ = happyFail

action_138 (18) = happyShift action_24
action_138 (22) = happyShift action_25
action_138 (23) = happyShift action_26
action_138 (25) = happyShift action_27
action_138 (26) = happyShift action_28
action_138 (33) = happyShift action_29
action_138 (34) = happyShift action_30
action_138 (8) = happyGoto action_141
action_138 _ = happyFail

action_139 (18) = happyShift action_24
action_139 (22) = happyShift action_25
action_139 (23) = happyShift action_26
action_139 (25) = happyShift action_27
action_139 (26) = happyShift action_28
action_139 (33) = happyShift action_29
action_139 (34) = happyShift action_30
action_139 (8) = happyGoto action_140
action_139 _ = happyFail

action_140 _ = happyReduce_11

action_141 _ = happyReduce_9

action_142 _ = happyReduce_10

action_143 _ = happyReduce_6

action_144 _ = happyReduce_7

action_145 _ = happyReduce_8

action_146 _ = happyReduce_37

action_147 _ = happyReduce_38

action_148 _ = happyReduce_39

action_149 (13) = happyShift action_10
action_149 (19) = happyShift action_11
action_149 (21) = happyShift action_12
action_149 (24) = happyShift action_13
action_149 (29) = happyShift action_14
action_149 (34) = happyShift action_15
action_149 (11) = happyGoto action_160
action_149 _ = happyFail

action_150 (13) = happyShift action_10
action_150 (19) = happyShift action_11
action_150 (21) = happyShift action_12
action_150 (24) = happyShift action_13
action_150 (29) = happyShift action_14
action_150 (34) = happyShift action_15
action_150 (11) = happyGoto action_159
action_150 _ = happyFail

action_151 (13) = happyShift action_10
action_151 (19) = happyShift action_11
action_151 (21) = happyShift action_12
action_151 (24) = happyShift action_13
action_151 (29) = happyShift action_14
action_151 (34) = happyShift action_15
action_151 (11) = happyGoto action_158
action_151 _ = happyFail

action_152 (13) = happyShift action_10
action_152 (19) = happyShift action_11
action_152 (21) = happyShift action_12
action_152 (24) = happyShift action_13
action_152 (29) = happyShift action_14
action_152 (34) = happyShift action_15
action_152 (11) = happyGoto action_157
action_152 _ = happyFail

action_153 (13) = happyShift action_10
action_153 (19) = happyShift action_11
action_153 (21) = happyShift action_12
action_153 (24) = happyShift action_13
action_153 (29) = happyShift action_14
action_153 (34) = happyShift action_15
action_153 (11) = happyGoto action_156
action_153 _ = happyFail

action_154 (13) = happyShift action_10
action_154 (19) = happyShift action_11
action_154 (21) = happyShift action_12
action_154 (24) = happyShift action_13
action_154 (29) = happyShift action_14
action_154 (34) = happyShift action_15
action_154 (11) = happyGoto action_155
action_154 _ = happyFail

action_155 _ = happyReduce_27

action_156 _ = happyReduce_26

action_157 _ = happyReduce_28

action_158 _ = happyReduce_32

action_159 _ = happyReduce_34

action_160 _ = happyReduce_33

happyReduce_4 = happySpecReduce_3  7 happyReduction_4
happyReduction_4 (HappyAbsSyn8  happy_var_3)
	_
	(HappyTerminal (TokenProofVar happy_var_1))
	 =  HappyAbsSyn7
		 (Logicdecl happy_var_1 happy_var_3
	)
happyReduction_4 _ _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_1  8 happyReduction_5
happyReduction_5 (HappyTerminal (TokenPredVar happy_var_1))
	 =  HappyAbsSyn8
		 (PredicateVar (string2Name happy_var_1)
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happyReduce 6 8 happyReduction_6
happyReduction_6 ((HappyAbsSyn8  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (PredicateLambda (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_7 = happyReduce 6 8 happyReduction_7
happyReduction_7 ((HappyAbsSyn8  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (PredicateLambda (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_8 = happyReduce 6 8 happyReduction_8
happyReduction_8 ((HappyAbsSyn8  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (PredicateLambda (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_9 = happyReduce 6 8 happyReduction_9
happyReduction_9 ((HappyAbsSyn8  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Forall (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_10 = happyReduce 6 8 happyReduction_10
happyReduction_10 ((HappyAbsSyn8  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Forall (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_11 = happyReduce 6 8 happyReduction_11
happyReduction_11 ((HappyAbsSyn8  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Forall (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_12 = happyReduce 4 8 happyReduction_12
happyReduction_12 (_ `HappyStk`
	(HappyAbsSyn12  happy_var_3) `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (PredicateApplication happy_var_2 (ArgProof happy_var_3)
	) `HappyStk` happyRest

happyReduce_13 = happyReduce 4 8 happyReduction_13
happyReduction_13 (_ `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (PredicateApplication happy_var_2 (ArgTerm happy_var_3)
	) `HappyStk` happyRest

happyReduce_14 = happyReduce 4 8 happyReduction_14
happyReduction_14 (_ `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (PredicateApplication happy_var_2 (ArgPredicate happy_var_3)
	) `HappyStk` happyRest

happyReduce_15 = happySpecReduce_3  8 happyReduction_15
happyReduction_15 (HappyAbsSyn11  happy_var_3)
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (Equal happy_var_2 happy_var_3
	)
happyReduction_15 _ _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_2  8 happyReduction_16
happyReduction_16 (HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (Terminate happy_var_2
	)
happyReduction_16 _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_2  8 happyReduction_17
happyReduction_17 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn8
		 (Bottom happy_var_2
	)
happyReduction_17 _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_2  9 happyReduction_18
happyReduction_18 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn9
		 (Formula happy_var_2
	)
happyReduction_18 _ _  = notHappyAtAll 

happyReduce_19 = happyReduce 4 9 happyReduction_19
happyReduction_19 ((HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (QuasiForall (ArgClassLogicalKind happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_20 = happyReduce 4 9 happyReduction_20
happyReduction_20 ((HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (QuasiForall (ArgClassTerm happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_21 = happyReduce 4 9 happyReduction_21
happyReduction_21 ((HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (QuasiForall (ArgClassPredicate happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_22 = happySpecReduce_1  10 happyReduction_22
happyReduction_22 _
	 =  HappyAbsSyn10
		 (Plus
	)

happyReduce_23 = happySpecReduce_1  10 happyReduction_23
happyReduction_23 _
	 =  HappyAbsSyn10
		 (Minus
	)

happyReduce_24 = happySpecReduce_1  11 happyReduction_24
happyReduction_24 (HappyTerminal (TokenTermVar happy_var_1))
	 =  HappyAbsSyn11
		 (TermVar (string2Name happy_var_1)
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_2  11 happyReduction_25
happyReduction_25 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn11
		 (Type happy_var_2
	)
happyReduction_25 _ _  = notHappyAtAll 

happyReduce_26 = happyReduce 7 11 happyReduction_26
happyReduction_26 ((HappyAbsSyn11  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_5) `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (Pi (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_27 = happyReduce 7 11 happyReduction_27
happyReduction_27 ((HappyAbsSyn11  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_5) `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (Pi (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_28 = happyReduce 7 11 happyReduction_28
happyReduction_28 ((HappyAbsSyn11  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_5) `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (Pi (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_29 = happyReduce 5 11 happyReduction_29
happyReduction_29 (_ `HappyStk`
	(HappyAbsSyn11  happy_var_4) `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TermApplication happy_var_3 (ArgTerm happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_30 = happyReduce 5 11 happyReduction_30
happyReduction_30 (_ `HappyStk`
	(HappyAbsSyn12  happy_var_4) `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TermApplication happy_var_3 (ArgProof happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 5 11 happyReduction_31
happyReduction_31 (_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TermApplication happy_var_3 (ArgPredicate happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_32 = happyReduce 7 11 happyReduction_32
happyReduction_32 ((HappyAbsSyn11  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_5) `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TermLambda (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_33 = happyReduce 7 11 happyReduction_33
happyReduction_33 ((HappyAbsSyn11  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_5) `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TermLambda (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_34 = happyReduce 7 11 happyReduction_34
happyReduction_34 ((HappyAbsSyn11  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_5) `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TermLambda (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_35 = happySpecReduce_2  11 happyReduction_35
happyReduction_35 (HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (Abort happy_var_2
	)
happyReduction_35 _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_1  12 happyReduction_36
happyReduction_36 (HappyTerminal (TokenProofVar happy_var_1))
	 =  HappyAbsSyn12
		 (ProofVar (string2Name happy_var_1)
	)
happyReduction_36 _  = notHappyAtAll 

happyReduce_37 = happyReduce 6 12 happyReduction_37
happyReduction_37 ((HappyAbsSyn12  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (ProofLambda (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_38 = happyReduce 6 12 happyReduction_38
happyReduction_38 ((HappyAbsSyn12  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (ProofLambda (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_39 = happyReduce 6 12 happyReduction_39
happyReduction_39 ((HappyAbsSyn12  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (ProofLambda (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_40 = happySpecReduce_3  12 happyReduction_40
happyReduction_40 (HappyAbsSyn11  happy_var_3)
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Join happy_var_2 happy_var_3
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happyReduce 4 12 happyReduction_41
happyReduction_41 (_ `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	(HappyAbsSyn12  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (ProofApplication happy_var_2 (ArgTerm happy_var_3)
	) `HappyStk` happyRest

happyReduce_42 = happyReduce 4 12 happyReduction_42
happyReduction_42 (_ `HappyStk`
	(HappyAbsSyn12  happy_var_3) `HappyStk`
	(HappyAbsSyn12  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (ProofApplication happy_var_2 (ArgProof happy_var_3)
	) `HappyStk` happyRest

happyReduce_43 = happyReduce 4 12 happyReduction_43
happyReduction_43 (_ `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	(HappyAbsSyn12  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (ProofApplication happy_var_2 (ArgPredicate happy_var_3)
	) `HappyStk` happyRest

happyReduce_44 = happySpecReduce_2  12 happyReduction_44
happyReduction_44 (HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Contra happy_var_2
	)
happyReduction_44 _ _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_2  12 happyReduction_45
happyReduction_45 (HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Valax happy_var_2
	)
happyReduction_45 _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 44 44 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenType -> cont 13;
	TokenData -> cont 14;
	TokenInt happy_dollar_dollar -> cont 15;
	TokenTheorem -> cont 16;
	TokenProofVar happy_dollar_dollar -> cont 17;
	TokenPredVar happy_dollar_dollar -> cont 18;
	TokenTermVar happy_dollar_dollar -> cont 19;
	TokenFm -> cont 20;
	TokenPi -> cont 21;
	TokenEq -> cont 22;
	TokenBot -> cont 23;
	TokenLM -> cont 24;
	TokenLamb -> cont 25;
	TokenForall -> cont 26;
	TokenQF -> cont 27;
	TokenPlam -> cont 28;
	TokenAb -> cont 29;
	TokenJoin -> cont 30;
	TokenContr -> cont 31;
	TokenValax -> cont 32;
	TokenEx -> cont 33;
	TokenBL -> cont 34;
	TokenBR -> cont 35;
	TokenBll -> cont 36;
	TokenBrr -> cont 37;
	TokenDC -> cont 38;
	TokenPlus -> cont 39;
	TokenMinus -> cont 40;
	TokenDef -> cont 41;
	TokenCL -> cont 42;
	TokenDot -> cont 43;
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
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn8 z -> happyReturn z; _other -> notHappyAtAll })

parser4Prf tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn12 z -> happyReturn z; _other -> notHappyAtAll })

parser4Term tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn11 z -> happyReturn z; _other -> notHappyAtAll })

parser4LK tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn9 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


data Token =

       TokenType

       | TokenData

       | TokenInt Integer

       | TokenOB

       | TokenCB

       | TokenFm

       | TokenForall
 
       | TokenQF
 
       | TokenPlam

       | TokenTheorem

       | TokenProofVar String

       | TokenPredVar String

       | TokenTermVar String

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
parseError _ = error "Parse error blah blah"

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
lexer ('(':cs) = TokenBL : lexer cs
lexer (')':cs) = TokenBR : lexer cs
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
      ("plambda",rest)  -> TokenPlam : lexer rest
      ("Bottom",rest)  -> TokenBot : lexer rest
      ("Eq",rest)  -> TokenEq : lexer rest
      ("Pi",rest)  -> TokenPi : lexer rest
      ("formula",rest)  -> TokenFm : lexer rest
      ("type",rest)  -> TokenType : lexer rest
      ("data",rest)  -> TokenData : lexer rest
      ("theorem",rest)  -> TokenTheorem : lexer rest
      ("Forall",rest) -> TokenForall : lexer rest
      ("Qforall",rest) -> TokenQF : lexer rest
      (var,rest) -> TokenTermVar var : lexer rest
      
-- For test purpose
readinput1 = do putStrLn "Please input a predicate"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser( lexer inpStr))

readinput2 = do putStrLn "Please input a proof"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Prf( lexer inpStr))

readinput3 = do putStrLn "Please input a term"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Term( lexer inpStr))

readinput4 = do putStrLn "Please input a LogicalKind"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4LK( lexer inpStr))
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
