{-# OPTIONS_GHC -w #-}
module Language.SepCore.Happyparser where 
import Language.SepCore.Syntax
import Data.Char
import Unbound.LocallyNameless hiding (Con,Val,Refl,Equal)
import Unbound.LocallyNameless.Subst(substR1)

-- parser produced by Happy Version 1.18.6

data HappyAbsSyn t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn13 t13
	| HappyAbsSyn14 t14
	| HappyAbsSyn15 t15
	| HappyAbsSyn16 t16
	| HappyAbsSyn17 t17
	| HappyAbsSyn18 t18
	| HappyAbsSyn19 t19
	| HappyAbsSyn20 t20
	| HappyAbsSyn21 t21
	| HappyAbsSyn22 t22
	| HappyAbsSyn23 t23

action_0 (29) = happyShift action_41
action_0 (33) = happyShift action_42
action_0 (34) = happyShift action_43
action_0 (36) = happyShift action_44
action_0 (37) = happyShift action_45
action_0 (44) = happyShift action_46
action_0 (45) = happyShift action_47
action_0 (19) = happyGoto action_40
action_0 _ = happyFail

action_1 (28) = happyShift action_11
action_1 (13) = happyGoto action_39
action_1 _ = happyFail

action_2 (28) = happyShift action_38
action_2 (14) = happyGoto action_37
action_2 _ = happyFail

action_3 (30) = happyShift action_36
action_3 (15) = happyGoto action_35
action_3 _ = happyFail

action_4 (30) = happyShift action_34
action_4 (16) = happyGoto action_33
action_4 _ = happyFail

action_5 (29) = happyShift action_32
action_5 (17) = happyGoto action_31
action_5 _ = happyFail

action_6 (29) = happyShift action_30
action_6 (18) = happyGoto action_29
action_6 _ = happyFail

action_7 (28) = happyShift action_23
action_7 (39) = happyShift action_24
action_7 (41) = happyShift action_25
action_7 (42) = happyShift action_26
action_7 (43) = happyShift action_27
action_7 (45) = happyShift action_28
action_7 (23) = happyGoto action_22
action_7 _ = happyFail

action_8 (24) = happyShift action_16
action_8 (30) = happyShift action_17
action_8 (32) = happyShift action_18
action_8 (35) = happyShift action_19
action_8 (40) = happyShift action_20
action_8 (45) = happyShift action_21
action_8 (22) = happyGoto action_15
action_8 _ = happyFail

action_9 (31) = happyShift action_13
action_9 (38) = happyShift action_14
action_9 (20) = happyGoto action_12
action_9 _ = happyFail

action_10 (28) = happyShift action_11
action_10 _ = happyFail

action_11 (49) = happyShift action_86
action_11 _ = happyFail

action_12 (55) = happyAccept
action_12 _ = happyFail

action_13 (26) = happyShift action_85
action_13 _ = happyFail

action_14 (24) = happyShift action_16
action_14 (29) = happyShift action_41
action_14 (30) = happyShift action_17
action_14 (31) = happyShift action_13
action_14 (32) = happyShift action_18
action_14 (33) = happyShift action_42
action_14 (34) = happyShift action_43
action_14 (35) = happyShift action_19
action_14 (36) = happyShift action_44
action_14 (37) = happyShift action_45
action_14 (38) = happyShift action_14
action_14 (40) = happyShift action_20
action_14 (44) = happyShift action_46
action_14 (45) = happyShift action_84
action_14 (19) = happyGoto action_81
action_14 (20) = happyGoto action_82
action_14 (22) = happyGoto action_83
action_14 _ = happyFail

action_15 (55) = happyAccept
action_15 _ = happyFail

action_16 (26) = happyShift action_80
action_16 _ = happyFail

action_17 _ = happyReduce_35

action_18 (28) = happyShift action_77
action_18 (29) = happyShift action_78
action_18 (30) = happyShift action_79
action_18 _ = happyFail

action_19 (28) = happyShift action_74
action_19 (29) = happyShift action_75
action_19 (30) = happyShift action_76
action_19 _ = happyFail

action_20 (24) = happyShift action_16
action_20 (30) = happyShift action_17
action_20 (32) = happyShift action_18
action_20 (35) = happyShift action_19
action_20 (40) = happyShift action_20
action_20 (45) = happyShift action_21
action_20 (22) = happyGoto action_73
action_20 _ = happyFail

action_21 (50) = happyShift action_71
action_21 (51) = happyShift action_72
action_21 (21) = happyGoto action_70
action_21 _ = happyFail

action_22 (55) = happyAccept
action_22 _ = happyFail

action_23 _ = happyReduce_47

action_24 (28) = happyShift action_67
action_24 (29) = happyShift action_68
action_24 (30) = happyShift action_69
action_24 _ = happyFail

action_25 (24) = happyShift action_16
action_25 (30) = happyShift action_17
action_25 (32) = happyShift action_18
action_25 (35) = happyShift action_19
action_25 (40) = happyShift action_20
action_25 (45) = happyShift action_21
action_25 (22) = happyGoto action_66
action_25 _ = happyFail

action_26 (28) = happyShift action_23
action_26 (39) = happyShift action_24
action_26 (41) = happyShift action_25
action_26 (42) = happyShift action_26
action_26 (43) = happyShift action_27
action_26 (45) = happyShift action_28
action_26 (23) = happyGoto action_65
action_26 _ = happyFail

action_27 (24) = happyShift action_16
action_27 (30) = happyShift action_17
action_27 (32) = happyShift action_18
action_27 (35) = happyShift action_19
action_27 (40) = happyShift action_20
action_27 (45) = happyShift action_21
action_27 (22) = happyGoto action_64
action_27 _ = happyFail

action_28 (28) = happyShift action_23
action_28 (39) = happyShift action_24
action_28 (41) = happyShift action_25
action_28 (42) = happyShift action_26
action_28 (43) = happyShift action_27
action_28 (45) = happyShift action_28
action_28 (23) = happyGoto action_63
action_28 _ = happyFail

action_29 (55) = happyAccept
action_29 _ = happyFail

action_30 (52) = happyShift action_62
action_30 _ = happyFail

action_31 (55) = happyAccept
action_31 _ = happyFail

action_32 (49) = happyShift action_61
action_32 _ = happyFail

action_33 (55) = happyAccept
action_33 _ = happyFail

action_34 (52) = happyShift action_60
action_34 _ = happyFail

action_35 (55) = happyAccept
action_35 _ = happyFail

action_36 (49) = happyShift action_59
action_36 _ = happyFail

action_37 (55) = happyAccept
action_37 _ = happyFail

action_38 (52) = happyShift action_58
action_38 _ = happyFail

action_39 (55) = happyAccept
action_39 _ = happyFail

action_40 (55) = happyAccept
action_40 _ = happyFail

action_41 _ = happyReduce_16

action_42 (24) = happyShift action_16
action_42 (30) = happyShift action_17
action_42 (32) = happyShift action_18
action_42 (35) = happyShift action_19
action_42 (40) = happyShift action_20
action_42 (45) = happyShift action_21
action_42 (22) = happyGoto action_57
action_42 _ = happyFail

action_43 (26) = happyShift action_56
action_43 _ = happyFail

action_44 (28) = happyShift action_53
action_44 (29) = happyShift action_54
action_44 (30) = happyShift action_55
action_44 _ = happyFail

action_45 (28) = happyShift action_50
action_45 (29) = happyShift action_51
action_45 (30) = happyShift action_52
action_45 _ = happyFail

action_46 (24) = happyShift action_16
action_46 (30) = happyShift action_17
action_46 (32) = happyShift action_18
action_46 (35) = happyShift action_19
action_46 (40) = happyShift action_20
action_46 (45) = happyShift action_21
action_46 (22) = happyGoto action_49
action_46 _ = happyFail

action_47 (29) = happyShift action_41
action_47 (33) = happyShift action_42
action_47 (34) = happyShift action_43
action_47 (36) = happyShift action_44
action_47 (37) = happyShift action_45
action_47 (44) = happyShift action_46
action_47 (45) = happyShift action_47
action_47 (19) = happyGoto action_48
action_47 _ = happyFail

action_48 (24) = happyShift action_16
action_48 (28) = happyShift action_23
action_48 (29) = happyShift action_41
action_48 (30) = happyShift action_17
action_48 (32) = happyShift action_18
action_48 (33) = happyShift action_42
action_48 (34) = happyShift action_43
action_48 (35) = happyShift action_19
action_48 (36) = happyShift action_44
action_48 (37) = happyShift action_45
action_48 (39) = happyShift action_24
action_48 (40) = happyShift action_20
action_48 (41) = happyShift action_25
action_48 (42) = happyShift action_26
action_48 (43) = happyShift action_27
action_48 (44) = happyShift action_46
action_48 (45) = happyShift action_105
action_48 (19) = happyGoto action_118
action_48 (22) = happyGoto action_119
action_48 (23) = happyGoto action_120
action_48 _ = happyFail

action_49 _ = happyReduce_27

action_50 (53) = happyShift action_117
action_50 _ = happyFail

action_51 (53) = happyShift action_116
action_51 _ = happyFail

action_52 (53) = happyShift action_115
action_52 _ = happyFail

action_53 (53) = happyShift action_114
action_53 _ = happyFail

action_54 (53) = happyShift action_113
action_54 _ = happyFail

action_55 (53) = happyShift action_112
action_55 _ = happyFail

action_56 _ = happyReduce_28

action_57 (24) = happyShift action_16
action_57 (30) = happyShift action_17
action_57 (32) = happyShift action_18
action_57 (35) = happyShift action_19
action_57 (40) = happyShift action_20
action_57 (45) = happyShift action_21
action_57 (22) = happyGoto action_111
action_57 _ = happyFail

action_58 (28) = happyShift action_23
action_58 (39) = happyShift action_24
action_58 (41) = happyShift action_25
action_58 (42) = happyShift action_26
action_58 (43) = happyShift action_27
action_58 (45) = happyShift action_28
action_58 (23) = happyGoto action_110
action_58 _ = happyFail

action_59 (24) = happyShift action_16
action_59 (30) = happyShift action_17
action_59 (32) = happyShift action_18
action_59 (35) = happyShift action_19
action_59 (40) = happyShift action_20
action_59 (45) = happyShift action_21
action_59 (22) = happyGoto action_109
action_59 _ = happyFail

action_60 (24) = happyShift action_16
action_60 (30) = happyShift action_17
action_60 (32) = happyShift action_18
action_60 (35) = happyShift action_19
action_60 (40) = happyShift action_20
action_60 (45) = happyShift action_21
action_60 (22) = happyGoto action_108
action_60 _ = happyFail

action_61 (31) = happyShift action_13
action_61 (38) = happyShift action_14
action_61 (20) = happyGoto action_107
action_61 _ = happyFail

action_62 (29) = happyShift action_41
action_62 (33) = happyShift action_42
action_62 (34) = happyShift action_43
action_62 (36) = happyShift action_44
action_62 (37) = happyShift action_45
action_62 (44) = happyShift action_46
action_62 (45) = happyShift action_47
action_62 (19) = happyGoto action_106
action_62 _ = happyFail

action_63 (24) = happyShift action_16
action_63 (28) = happyShift action_23
action_63 (29) = happyShift action_41
action_63 (30) = happyShift action_17
action_63 (32) = happyShift action_18
action_63 (33) = happyShift action_42
action_63 (34) = happyShift action_43
action_63 (35) = happyShift action_19
action_63 (36) = happyShift action_44
action_63 (37) = happyShift action_45
action_63 (39) = happyShift action_24
action_63 (40) = happyShift action_20
action_63 (41) = happyShift action_25
action_63 (42) = happyShift action_26
action_63 (43) = happyShift action_27
action_63 (44) = happyShift action_46
action_63 (45) = happyShift action_105
action_63 (19) = happyGoto action_102
action_63 (22) = happyGoto action_103
action_63 (23) = happyGoto action_104
action_63 _ = happyFail

action_64 _ = happyReduce_56

action_65 _ = happyReduce_55

action_66 (24) = happyShift action_16
action_66 (30) = happyShift action_17
action_66 (32) = happyShift action_18
action_66 (35) = happyShift action_19
action_66 (40) = happyShift action_20
action_66 (45) = happyShift action_21
action_66 (22) = happyGoto action_101
action_66 _ = happyFail

action_67 (53) = happyShift action_100
action_67 _ = happyFail

action_68 (53) = happyShift action_99
action_68 _ = happyFail

action_69 (53) = happyShift action_98
action_69 _ = happyFail

action_70 (24) = happyShift action_16
action_70 (30) = happyShift action_17
action_70 (32) = happyShift action_18
action_70 (35) = happyShift action_19
action_70 (40) = happyShift action_20
action_70 (45) = happyShift action_21
action_70 (22) = happyGoto action_97
action_70 _ = happyFail

action_71 _ = happyReduce_33

action_72 _ = happyReduce_34

action_73 _ = happyReduce_46

action_74 (53) = happyShift action_96
action_74 _ = happyFail

action_75 (53) = happyShift action_95
action_75 _ = happyFail

action_76 (53) = happyShift action_94
action_76 _ = happyFail

action_77 (53) = happyShift action_93
action_77 _ = happyFail

action_78 (53) = happyShift action_92
action_78 _ = happyFail

action_79 (53) = happyShift action_91
action_79 _ = happyFail

action_80 _ = happyReduce_36

action_81 (54) = happyShift action_90
action_81 _ = happyFail

action_82 (54) = happyShift action_89
action_82 _ = happyFail

action_83 (54) = happyShift action_88
action_83 _ = happyFail

action_84 (29) = happyShift action_41
action_84 (33) = happyShift action_42
action_84 (34) = happyShift action_43
action_84 (36) = happyShift action_44
action_84 (37) = happyShift action_45
action_84 (44) = happyShift action_46
action_84 (45) = happyShift action_47
action_84 (50) = happyShift action_71
action_84 (51) = happyShift action_72
action_84 (19) = happyGoto action_48
action_84 (21) = happyGoto action_70
action_84 _ = happyFail

action_85 _ = happyReduce_29

action_86 (29) = happyShift action_41
action_86 (33) = happyShift action_42
action_86 (34) = happyShift action_43
action_86 (36) = happyShift action_44
action_86 (37) = happyShift action_45
action_86 (44) = happyShift action_46
action_86 (45) = happyShift action_47
action_86 (19) = happyGoto action_87
action_86 _ = happyFail

action_87 _ = happyReduce_10

action_88 (31) = happyShift action_13
action_88 (38) = happyShift action_14
action_88 (20) = happyGoto action_148
action_88 _ = happyFail

action_89 (31) = happyShift action_13
action_89 (38) = happyShift action_14
action_89 (20) = happyGoto action_147
action_89 _ = happyFail

action_90 (31) = happyShift action_13
action_90 (38) = happyShift action_14
action_90 (20) = happyGoto action_146
action_90 _ = happyFail

action_91 (50) = happyShift action_71
action_91 (51) = happyShift action_72
action_91 (21) = happyGoto action_145
action_91 _ = happyFail

action_92 (50) = happyShift action_71
action_92 (51) = happyShift action_72
action_92 (21) = happyGoto action_144
action_92 _ = happyFail

action_93 (50) = happyShift action_71
action_93 (51) = happyShift action_72
action_93 (21) = happyGoto action_143
action_93 _ = happyFail

action_94 (50) = happyShift action_71
action_94 (51) = happyShift action_72
action_94 (21) = happyGoto action_142
action_94 _ = happyFail

action_95 (50) = happyShift action_71
action_95 (51) = happyShift action_72
action_95 (21) = happyGoto action_141
action_95 _ = happyFail

action_96 (50) = happyShift action_71
action_96 (51) = happyShift action_72
action_96 (21) = happyGoto action_140
action_96 _ = happyFail

action_97 (24) = happyShift action_16
action_97 (28) = happyShift action_23
action_97 (29) = happyShift action_41
action_97 (30) = happyShift action_17
action_97 (32) = happyShift action_18
action_97 (33) = happyShift action_42
action_97 (34) = happyShift action_43
action_97 (35) = happyShift action_19
action_97 (36) = happyShift action_44
action_97 (37) = happyShift action_45
action_97 (39) = happyShift action_24
action_97 (40) = happyShift action_20
action_97 (41) = happyShift action_25
action_97 (42) = happyShift action_26
action_97 (43) = happyShift action_27
action_97 (44) = happyShift action_46
action_97 (45) = happyShift action_105
action_97 (19) = happyGoto action_137
action_97 (22) = happyGoto action_138
action_97 (23) = happyGoto action_139
action_97 _ = happyFail

action_98 (24) = happyShift action_16
action_98 (30) = happyShift action_17
action_98 (32) = happyShift action_18
action_98 (35) = happyShift action_19
action_98 (40) = happyShift action_20
action_98 (45) = happyShift action_21
action_98 (22) = happyGoto action_136
action_98 _ = happyFail

action_99 (31) = happyShift action_13
action_99 (38) = happyShift action_14
action_99 (20) = happyGoto action_135
action_99 _ = happyFail

action_100 (29) = happyShift action_41
action_100 (33) = happyShift action_42
action_100 (34) = happyShift action_43
action_100 (36) = happyShift action_44
action_100 (37) = happyShift action_45
action_100 (44) = happyShift action_46
action_100 (45) = happyShift action_47
action_100 (19) = happyGoto action_134
action_100 _ = happyFail

action_101 _ = happyReduce_51

action_102 (46) = happyShift action_133
action_102 _ = happyFail

action_103 (46) = happyShift action_132
action_103 _ = happyFail

action_104 (46) = happyShift action_131
action_104 _ = happyFail

action_105 (28) = happyShift action_23
action_105 (29) = happyShift action_41
action_105 (33) = happyShift action_42
action_105 (34) = happyShift action_43
action_105 (36) = happyShift action_44
action_105 (37) = happyShift action_45
action_105 (39) = happyShift action_24
action_105 (41) = happyShift action_25
action_105 (42) = happyShift action_26
action_105 (43) = happyShift action_27
action_105 (44) = happyShift action_46
action_105 (45) = happyShift action_130
action_105 (50) = happyShift action_71
action_105 (51) = happyShift action_72
action_105 (19) = happyGoto action_48
action_105 (21) = happyGoto action_70
action_105 (23) = happyGoto action_63
action_105 _ = happyFail

action_106 _ = happyReduce_15

action_107 _ = happyReduce_14

action_108 _ = happyReduce_13

action_109 _ = happyReduce_12

action_110 _ = happyReduce_11

action_111 _ = happyReduce_26

action_112 (24) = happyShift action_16
action_112 (30) = happyShift action_17
action_112 (32) = happyShift action_18
action_112 (35) = happyShift action_19
action_112 (40) = happyShift action_20
action_112 (45) = happyShift action_21
action_112 (22) = happyGoto action_129
action_112 _ = happyFail

action_113 (31) = happyShift action_13
action_113 (38) = happyShift action_14
action_113 (20) = happyGoto action_128
action_113 _ = happyFail

action_114 (29) = happyShift action_41
action_114 (33) = happyShift action_42
action_114 (34) = happyShift action_43
action_114 (36) = happyShift action_44
action_114 (37) = happyShift action_45
action_114 (44) = happyShift action_46
action_114 (45) = happyShift action_47
action_114 (19) = happyGoto action_127
action_114 _ = happyFail

action_115 (24) = happyShift action_16
action_115 (30) = happyShift action_17
action_115 (32) = happyShift action_18
action_115 (35) = happyShift action_19
action_115 (40) = happyShift action_20
action_115 (45) = happyShift action_21
action_115 (22) = happyGoto action_126
action_115 _ = happyFail

action_116 (31) = happyShift action_13
action_116 (38) = happyShift action_14
action_116 (20) = happyGoto action_125
action_116 _ = happyFail

action_117 (29) = happyShift action_41
action_117 (33) = happyShift action_42
action_117 (34) = happyShift action_43
action_117 (36) = happyShift action_44
action_117 (37) = happyShift action_45
action_117 (44) = happyShift action_46
action_117 (45) = happyShift action_47
action_117 (19) = happyGoto action_124
action_117 _ = happyFail

action_118 (46) = happyShift action_123
action_118 _ = happyFail

action_119 (46) = happyShift action_122
action_119 _ = happyFail

action_120 (46) = happyShift action_121
action_120 _ = happyFail

action_121 _ = happyReduce_23

action_122 _ = happyReduce_24

action_123 _ = happyReduce_25

action_124 (54) = happyShift action_166
action_124 _ = happyFail

action_125 (54) = happyShift action_165
action_125 _ = happyFail

action_126 (54) = happyShift action_164
action_126 _ = happyFail

action_127 (54) = happyShift action_163
action_127 _ = happyFail

action_128 (54) = happyShift action_162
action_128 _ = happyFail

action_129 (54) = happyShift action_161
action_129 _ = happyFail

action_130 (28) = happyShift action_23
action_130 (29) = happyShift action_41
action_130 (33) = happyShift action_42
action_130 (34) = happyShift action_43
action_130 (36) = happyShift action_44
action_130 (37) = happyShift action_45
action_130 (39) = happyShift action_24
action_130 (41) = happyShift action_25
action_130 (42) = happyShift action_26
action_130 (43) = happyShift action_27
action_130 (44) = happyShift action_46
action_130 (45) = happyShift action_130
action_130 (19) = happyGoto action_48
action_130 (23) = happyGoto action_63
action_130 _ = happyFail

action_131 _ = happyReduce_53

action_132 _ = happyReduce_52

action_133 _ = happyReduce_54

action_134 (54) = happyShift action_160
action_134 _ = happyFail

action_135 (54) = happyShift action_159
action_135 _ = happyFail

action_136 (54) = happyShift action_158
action_136 _ = happyFail

action_137 (46) = happyShift action_157
action_137 _ = happyFail

action_138 (46) = happyShift action_156
action_138 _ = happyFail

action_139 (46) = happyShift action_155
action_139 _ = happyFail

action_140 (29) = happyShift action_41
action_140 (33) = happyShift action_42
action_140 (34) = happyShift action_43
action_140 (36) = happyShift action_44
action_140 (37) = happyShift action_45
action_140 (44) = happyShift action_46
action_140 (45) = happyShift action_47
action_140 (19) = happyGoto action_154
action_140 _ = happyFail

action_141 (31) = happyShift action_13
action_141 (38) = happyShift action_14
action_141 (20) = happyGoto action_153
action_141 _ = happyFail

action_142 (24) = happyShift action_16
action_142 (30) = happyShift action_17
action_142 (32) = happyShift action_18
action_142 (35) = happyShift action_19
action_142 (40) = happyShift action_20
action_142 (45) = happyShift action_21
action_142 (22) = happyGoto action_152
action_142 _ = happyFail

action_143 (29) = happyShift action_41
action_143 (33) = happyShift action_42
action_143 (34) = happyShift action_43
action_143 (36) = happyShift action_44
action_143 (37) = happyShift action_45
action_143 (44) = happyShift action_46
action_143 (45) = happyShift action_47
action_143 (19) = happyGoto action_151
action_143 _ = happyFail

action_144 (31) = happyShift action_13
action_144 (38) = happyShift action_14
action_144 (20) = happyGoto action_150
action_144 _ = happyFail

action_145 (24) = happyShift action_16
action_145 (30) = happyShift action_17
action_145 (32) = happyShift action_18
action_145 (35) = happyShift action_19
action_145 (40) = happyShift action_20
action_145 (45) = happyShift action_21
action_145 (22) = happyGoto action_149
action_145 _ = happyFail

action_146 _ = happyReduce_32

action_147 _ = happyReduce_30

action_148 _ = happyReduce_31

action_149 (54) = happyShift action_181
action_149 _ = happyFail

action_150 (54) = happyShift action_180
action_150 _ = happyFail

action_151 (54) = happyShift action_179
action_151 _ = happyFail

action_152 (54) = happyShift action_178
action_152 _ = happyFail

action_153 (54) = happyShift action_177
action_153 _ = happyFail

action_154 (54) = happyShift action_176
action_154 _ = happyFail

action_155 _ = happyReduce_41

action_156 _ = happyReduce_40

action_157 _ = happyReduce_42

action_158 (28) = happyShift action_23
action_158 (39) = happyShift action_24
action_158 (41) = happyShift action_25
action_158 (42) = happyShift action_26
action_158 (43) = happyShift action_27
action_158 (45) = happyShift action_28
action_158 (23) = happyGoto action_175
action_158 _ = happyFail

action_159 (28) = happyShift action_23
action_159 (39) = happyShift action_24
action_159 (41) = happyShift action_25
action_159 (42) = happyShift action_26
action_159 (43) = happyShift action_27
action_159 (45) = happyShift action_28
action_159 (23) = happyGoto action_174
action_159 _ = happyFail

action_160 (28) = happyShift action_23
action_160 (39) = happyShift action_24
action_160 (41) = happyShift action_25
action_160 (42) = happyShift action_26
action_160 (43) = happyShift action_27
action_160 (45) = happyShift action_28
action_160 (23) = happyGoto action_173
action_160 _ = happyFail

action_161 (29) = happyShift action_41
action_161 (33) = happyShift action_42
action_161 (34) = happyShift action_43
action_161 (36) = happyShift action_44
action_161 (37) = happyShift action_45
action_161 (44) = happyShift action_46
action_161 (45) = happyShift action_47
action_161 (19) = happyGoto action_172
action_161 _ = happyFail

action_162 (29) = happyShift action_41
action_162 (33) = happyShift action_42
action_162 (34) = happyShift action_43
action_162 (36) = happyShift action_44
action_162 (37) = happyShift action_45
action_162 (44) = happyShift action_46
action_162 (45) = happyShift action_47
action_162 (19) = happyGoto action_171
action_162 _ = happyFail

action_163 (29) = happyShift action_41
action_163 (33) = happyShift action_42
action_163 (34) = happyShift action_43
action_163 (36) = happyShift action_44
action_163 (37) = happyShift action_45
action_163 (44) = happyShift action_46
action_163 (45) = happyShift action_47
action_163 (19) = happyGoto action_170
action_163 _ = happyFail

action_164 (29) = happyShift action_41
action_164 (33) = happyShift action_42
action_164 (34) = happyShift action_43
action_164 (36) = happyShift action_44
action_164 (37) = happyShift action_45
action_164 (44) = happyShift action_46
action_164 (45) = happyShift action_47
action_164 (19) = happyGoto action_169
action_164 _ = happyFail

action_165 (29) = happyShift action_41
action_165 (33) = happyShift action_42
action_165 (34) = happyShift action_43
action_165 (36) = happyShift action_44
action_165 (37) = happyShift action_45
action_165 (44) = happyShift action_46
action_165 (45) = happyShift action_47
action_165 (19) = happyGoto action_168
action_165 _ = happyFail

action_166 (29) = happyShift action_41
action_166 (33) = happyShift action_42
action_166 (34) = happyShift action_43
action_166 (36) = happyShift action_44
action_166 (37) = happyShift action_45
action_166 (44) = happyShift action_46
action_166 (45) = happyShift action_47
action_166 (19) = happyGoto action_167
action_166 _ = happyFail

action_167 _ = happyReduce_22

action_168 _ = happyReduce_20

action_169 _ = happyReduce_21

action_170 _ = happyReduce_17

action_171 _ = happyReduce_18

action_172 _ = happyReduce_19

action_173 _ = happyReduce_48

action_174 _ = happyReduce_49

action_175 _ = happyReduce_50

action_176 (24) = happyShift action_16
action_176 (30) = happyShift action_17
action_176 (32) = happyShift action_18
action_176 (35) = happyShift action_19
action_176 (40) = happyShift action_20
action_176 (45) = happyShift action_21
action_176 (22) = happyGoto action_187
action_176 _ = happyFail

action_177 (24) = happyShift action_16
action_177 (30) = happyShift action_17
action_177 (32) = happyShift action_18
action_177 (35) = happyShift action_19
action_177 (40) = happyShift action_20
action_177 (45) = happyShift action_21
action_177 (22) = happyGoto action_186
action_177 _ = happyFail

action_178 (24) = happyShift action_16
action_178 (30) = happyShift action_17
action_178 (32) = happyShift action_18
action_178 (35) = happyShift action_19
action_178 (40) = happyShift action_20
action_178 (45) = happyShift action_21
action_178 (22) = happyGoto action_185
action_178 _ = happyFail

action_179 (24) = happyShift action_16
action_179 (30) = happyShift action_17
action_179 (32) = happyShift action_18
action_179 (35) = happyShift action_19
action_179 (40) = happyShift action_20
action_179 (45) = happyShift action_21
action_179 (22) = happyGoto action_184
action_179 _ = happyFail

action_180 (24) = happyShift action_16
action_180 (30) = happyShift action_17
action_180 (32) = happyShift action_18
action_180 (35) = happyShift action_19
action_180 (40) = happyShift action_20
action_180 (45) = happyShift action_21
action_180 (22) = happyGoto action_183
action_180 _ = happyFail

action_181 (24) = happyShift action_16
action_181 (30) = happyShift action_17
action_181 (32) = happyShift action_18
action_181 (35) = happyShift action_19
action_181 (40) = happyShift action_20
action_181 (45) = happyShift action_21
action_181 (22) = happyGoto action_182
action_181 _ = happyFail

action_182 _ = happyReduce_38

action_183 _ = happyReduce_37

action_184 _ = happyReduce_39

action_185 _ = happyReduce_43

action_186 _ = happyReduce_45

action_187 _ = happyReduce_44

happyReduce_10 = happySpecReduce_3  13 happyReduction_10
happyReduction_10 (HappyAbsSyn19  happy_var_3)
	_
	(HappyTerminal (TokenProofVar happy_var_1))
	 =  HappyAbsSyn13
		 (Logicdecl (string2Name happy_var_1) happy_var_3
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happySpecReduce_3  14 happyReduction_11
happyReduction_11 (HappyAbsSyn23  happy_var_3)
	_
	(HappyTerminal (TokenProofVar happy_var_1))
	 =  HappyAbsSyn14
		 (Proofdef (string2Name happy_var_1) happy_var_3
	)
happyReduction_11 _ _ _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_3  15 happyReduction_12
happyReduction_12 (HappyAbsSyn22  happy_var_3)
	_
	(HappyTerminal (TokenTermVar happy_var_1))
	 =  HappyAbsSyn15
		 (Progdecl (string2Name happy_var_1) happy_var_3
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_3  16 happyReduction_13
happyReduction_13 (HappyAbsSyn22  happy_var_3)
	_
	(HappyTerminal (TokenTermVar happy_var_1))
	 =  HappyAbsSyn16
		 (Progdef (string2Name happy_var_1) happy_var_3
	)
happyReduction_13 _ _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_3  17 happyReduction_14
happyReduction_14 (HappyAbsSyn20  happy_var_3)
	_
	(HappyTerminal (TokenPredVar happy_var_1))
	 =  HappyAbsSyn17
		 (Preddecl (string2Name happy_var_1) happy_var_3
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_3  18 happyReduction_15
happyReduction_15 (HappyAbsSyn19  happy_var_3)
	_
	(HappyTerminal (TokenPredVar happy_var_1))
	 =  HappyAbsSyn18
		 (Preddef (string2Name happy_var_1) happy_var_3
	)
happyReduction_15 _ _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  19 happyReduction_16
happyReduction_16 (HappyTerminal (TokenPredVar happy_var_1))
	 =  HappyAbsSyn19
		 (PredicateVar (string2Name happy_var_1)
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happyReduce 6 19 happyReduction_17
happyReduction_17 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (PredicateLambda (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_18 = happyReduce 6 19 happyReduction_18
happyReduction_18 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (PredicateLambda (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_19 = happyReduce 6 19 happyReduction_19
happyReduction_19 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (PredicateLambda (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_20 = happyReduce 6 19 happyReduction_20
happyReduction_20 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Forall (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_21 = happyReduce 6 19 happyReduction_21
happyReduction_21 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Forall (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_22 = happyReduce 6 19 happyReduction_22
happyReduction_22 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Forall (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_23 = happyReduce 4 19 happyReduction_23
happyReduction_23 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (PredicateApplication happy_var_2 (ArgProof happy_var_3)
	) `HappyStk` happyRest

happyReduce_24 = happyReduce 4 19 happyReduction_24
happyReduction_24 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (PredicateApplication happy_var_2 (ArgTerm happy_var_3)
	) `HappyStk` happyRest

happyReduce_25 = happyReduce 4 19 happyReduction_25
happyReduction_25 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (PredicateApplication happy_var_2 (ArgPredicate happy_var_3)
	) `HappyStk` happyRest

happyReduce_26 = happySpecReduce_3  19 happyReduction_26
happyReduction_26 (HappyAbsSyn22  happy_var_3)
	(HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (Equal happy_var_2 happy_var_3
	)
happyReduction_26 _ _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_2  19 happyReduction_27
happyReduction_27 (HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (Terminate happy_var_2
	)
happyReduction_27 _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_2  19 happyReduction_28
happyReduction_28 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn19
		 (Bottom happy_var_2
	)
happyReduction_28 _ _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_2  20 happyReduction_29
happyReduction_29 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn20
		 (Formula happy_var_2
	)
happyReduction_29 _ _  = notHappyAtAll 

happyReduce_30 = happyReduce 4 20 happyReduction_30
happyReduction_30 ((HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (QuasiForall (ArgClassLogicalKind happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 4 20 happyReduction_31
happyReduction_31 ((HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (QuasiForall (ArgClassTerm happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_32 = happyReduce 4 20 happyReduction_32
happyReduction_32 ((HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (QuasiForall (ArgClassPredicate happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_33 = happySpecReduce_1  21 happyReduction_33
happyReduction_33 _
	 =  HappyAbsSyn21
		 (Plus
	)

happyReduce_34 = happySpecReduce_1  21 happyReduction_34
happyReduction_34 _
	 =  HappyAbsSyn21
		 (Minus
	)

happyReduce_35 = happySpecReduce_1  22 happyReduction_35
happyReduction_35 (HappyTerminal (TokenTermVar happy_var_1))
	 =  HappyAbsSyn22
		 (TermVar (string2Name happy_var_1)
	)
happyReduction_35 _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_2  22 happyReduction_36
happyReduction_36 (HappyTerminal (TokenInt happy_var_2))
	_
	 =  HappyAbsSyn22
		 (Type happy_var_2
	)
happyReduction_36 _ _  = notHappyAtAll 

happyReduce_37 = happyReduce 7 22 happyReduction_37
happyReduction_37 ((HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_5) `HappyStk`
	(HappyAbsSyn21  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (Pi (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_38 = happyReduce 7 22 happyReduction_38
happyReduction_38 ((HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	(HappyAbsSyn21  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (Pi (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_39 = happyReduce 7 22 happyReduction_39
happyReduction_39 ((HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_5) `HappyStk`
	(HappyAbsSyn21  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (Pi (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_40 = happyReduce 5 22 happyReduction_40
happyReduction_40 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_4) `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	(HappyAbsSyn21  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (TermApplication happy_var_3 (ArgTerm happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_41 = happyReduce 5 22 happyReduction_41
happyReduction_41 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_4) `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	(HappyAbsSyn21  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (TermApplication happy_var_3 (ArgProof happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_42 = happyReduce 5 22 happyReduction_42
happyReduction_42 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	(HappyAbsSyn21  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (TermApplication happy_var_3 (ArgPredicate happy_var_4) happy_var_2
	) `HappyStk` happyRest

happyReduce_43 = happyReduce 7 22 happyReduction_43
happyReduction_43 ((HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	(HappyAbsSyn21  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (TermLambda (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_44 = happyReduce 7 22 happyReduction_44
happyReduction_44 ((HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_5) `HappyStk`
	(HappyAbsSyn21  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (TermLambda (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_45 = happyReduce 7 22 happyReduction_45
happyReduction_45 ((HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_5) `HappyStk`
	(HappyAbsSyn21  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (TermLambda (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_5)) happy_var_7) happy_var_4
	) `HappyStk` happyRest

happyReduce_46 = happySpecReduce_2  22 happyReduction_46
happyReduction_46 (HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn22
		 (Abort happy_var_2
	)
happyReduction_46 _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_1  23 happyReduction_47
happyReduction_47 (HappyTerminal (TokenProofVar happy_var_1))
	 =  HappyAbsSyn23
		 (ProofVar (string2Name happy_var_1)
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happyReduce 6 23 happyReduction_48
happyReduction_48 ((HappyAbsSyn23  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenProofVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (ProofLambda (bind (ArgNameProof (string2Name happy_var_2), Embed (ArgClassPredicate happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_49 = happyReduce 6 23 happyReduction_49
happyReduction_49 ((HappyAbsSyn23  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenPredVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (ProofLambda (bind (ArgNamePredicate (string2Name happy_var_2), Embed (ArgClassLogicalKind happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_50 = happyReduce 6 23 happyReduction_50
happyReduction_50 ((HappyAbsSyn23  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenTermVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (ProofLambda (bind (ArgNameTerm (string2Name happy_var_2), Embed (ArgClassTerm happy_var_4)) happy_var_6)
	) `HappyStk` happyRest

happyReduce_51 = happySpecReduce_3  23 happyReduction_51
happyReduction_51 (HappyAbsSyn22  happy_var_3)
	(HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn23
		 (Join happy_var_2 happy_var_3
	)
happyReduction_51 _ _ _  = notHappyAtAll 

happyReduce_52 = happyReduce 4 23 happyReduction_52
happyReduction_52 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (ProofApplication happy_var_2 (ArgTerm happy_var_3)
	) `HappyStk` happyRest

happyReduce_53 = happyReduce 4 23 happyReduction_53
happyReduction_53 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (ProofApplication happy_var_2 (ArgProof happy_var_3)
	) `HappyStk` happyRest

happyReduce_54 = happyReduce 4 23 happyReduction_54
happyReduction_54 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (ProofApplication happy_var_2 (ArgPredicate happy_var_3)
	) `HappyStk` happyRest

happyReduce_55 = happySpecReduce_2  23 happyReduction_55
happyReduction_55 (HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn23
		 (Contra happy_var_2
	)
happyReduction_55 _ _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_2  23 happyReduction_56
happyReduction_56 (HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn23
		 (Valax happy_var_2
	)
happyReduction_56 _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 55 55 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenType -> cont 24;
	TokenData -> cont 25;
	TokenInt happy_dollar_dollar -> cont 26;
	TokenTheorem -> cont 27;
	TokenProofVar happy_dollar_dollar -> cont 28;
	TokenPredVar happy_dollar_dollar -> cont 29;
	TokenTermVar happy_dollar_dollar -> cont 30;
	TokenFm -> cont 31;
	TokenPi -> cont 32;
	TokenEq -> cont 33;
	TokenBot -> cont 34;
	TokenLM -> cont 35;
	TokenLamb -> cont 36;
	TokenForall -> cont 37;
	TokenQF -> cont 38;
	TokenPlam -> cont 39;
	TokenAb -> cont 40;
	TokenJoin -> cont 41;
	TokenContr -> cont 42;
	TokenValax -> cont 43;
	TokenEx -> cont 44;
	TokenBL -> cont 45;
	TokenBR -> cont 46;
	TokenBll -> cont 47;
	TokenBrr -> cont 48;
	TokenDC -> cont 49;
	TokenPlus -> cont 50;
	TokenMinus -> cont 51;
	TokenDef -> cont 52;
	TokenCL -> cont 53;
	TokenDot -> cont 54;
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
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn19 z -> happyReturn z; _other -> notHappyAtAll })

parser4Logicdecl tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn13 z -> happyReturn z; _other -> notHappyAtAll })

parser4Proofdef tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn14 z -> happyReturn z; _other -> notHappyAtAll })

parser4Progdecl tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

parser4Progdef tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn16 z -> happyReturn z; _other -> notHappyAtAll })

parser4Preddecl tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn17 z -> happyReturn z; _other -> notHappyAtAll })

parser4Preddef tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn18 z -> happyReturn z; _other -> notHappyAtAll })

parser4Prf tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn23 z -> happyReturn z; _other -> notHappyAtAll })

parser4Term tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_8 tks) (\x -> case x of {HappyAbsSyn22 z -> happyReturn z; _other -> notHappyAtAll })

parser4LK tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_9 tks) (\x -> case x of {HappyAbsSyn20 z -> happyReturn z; _other -> notHappyAtAll })

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
lexer ('=': cs) = TokenDef : lexer cs 
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

readinput5 = do putStrLn "Please input a Proof declaration"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Logicdecl( lexer inpStr))

readinput6 = do putStrLn "Please input a Proof definition"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Proofdef( lexer inpStr))

readinput7 = do putStrLn "Please input a Program declaration"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Progdecl( lexer inpStr))

readinput8 = do putStrLn "Please input a Program definition"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Progdef( lexer inpStr))

readinput9 = do putStrLn "Please input a Predicate declaration"
                inpStr <- getLine 
                putStrLn $ "Here is the result: " ++ show(parser4Preddecl( lexer inpStr))

readinput10 = do putStrLn "Please input a Predicate definition"
                 inpStr <- getLine 
                 putStrLn $ "Here is the result: " ++ show(parser4Preddef( lexer inpStr))



 {- %name parser4Logicdel Logicdecl
%name parser4Proofdef Proofdef
%name parser4Progdecl Progdecl
%name parser4Progdef Progdef
%name parser4Preddecl Preddecl
%name parser4Preddef Preddef
  -}
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
