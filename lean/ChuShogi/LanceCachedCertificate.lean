import ChuShogi.LanceCachedData

/-! Complete graph closure and exactly the provider observations required
by the counter. Numeric lookup is justified by checked keys and injectivity. -/
namespace ChuShogi.LanceCachedCertificate
open FileGame FiniteSearch LanceObservables
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000000
set_option Elab.async false

theorem tree0_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree0 := by decide
theorem tree1_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree1 := by decide
theorem tree2_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree2 := ⟨by decide, tree0_closed, tree1_closed⟩
theorem tree3_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree3 := by decide
theorem tree4_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree4 := by decide
theorem tree5_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree5 := ⟨by decide, tree3_closed, tree4_closed⟩
theorem tree6_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree6 := ⟨by decide, tree2_closed, tree5_closed⟩
theorem tree7_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree7 := by decide
theorem tree8_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree8 := by decide
theorem tree9_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree9 := ⟨by decide, tree7_closed, tree8_closed⟩
theorem tree10_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree10 := by decide
theorem tree11_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree11 := by decide
theorem tree12_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree12 := ⟨by decide, tree10_closed, tree11_closed⟩
theorem tree13_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree13 := ⟨by decide, tree9_closed, tree12_closed⟩
theorem tree14_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree14 := ⟨by decide, tree6_closed, tree13_closed⟩
theorem tree15_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree15 := by decide
theorem tree16_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree16 := by decide
theorem tree17_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree17 := ⟨by decide, tree15_closed, tree16_closed⟩
theorem tree18_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree18 := by decide
theorem tree19_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree19 := by decide
theorem tree20_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree20 := ⟨by decide, tree18_closed, tree19_closed⟩
theorem tree21_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree21 := ⟨by decide, tree17_closed, tree20_closed⟩
theorem tree22_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree22 := by decide
theorem tree23_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree23 := by decide
theorem tree24_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree24 := ⟨by decide, tree22_closed, tree23_closed⟩
theorem tree25_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree25 := by decide
theorem tree26_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree26 := by decide
theorem tree27_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree27 := ⟨by decide, tree25_closed, tree26_closed⟩
theorem tree28_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree28 := ⟨by decide, tree24_closed, tree27_closed⟩
theorem tree29_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree29 := ⟨by decide, tree21_closed, tree28_closed⟩
theorem tree30_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree30 := ⟨by decide, tree14_closed, tree29_closed⟩
theorem tree31_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree31 := by decide
theorem tree32_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree32 := by decide
theorem tree33_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree33 := ⟨by decide, tree31_closed, tree32_closed⟩
theorem tree34_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree34 := by decide
theorem tree35_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree35 := by decide
theorem tree36_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree36 := ⟨by decide, tree34_closed, tree35_closed⟩
theorem tree37_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree37 := ⟨by decide, tree33_closed, tree36_closed⟩
theorem tree38_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree38 := by decide
theorem tree39_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree39 := by decide
theorem tree40_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree40 := ⟨by decide, tree38_closed, tree39_closed⟩
theorem tree41_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree41 := by decide
theorem tree42_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree42 := by decide
theorem tree43_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree43 := ⟨by decide, tree41_closed, tree42_closed⟩
theorem tree44_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree44 := ⟨by decide, tree40_closed, tree43_closed⟩
theorem tree45_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree45 := ⟨by decide, tree37_closed, tree44_closed⟩
theorem tree46_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree46 := by decide
theorem tree47_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree47 := by decide
theorem tree48_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree48 := ⟨by decide, tree46_closed, tree47_closed⟩
theorem tree49_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree49 := by decide
theorem tree50_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree50 := by decide
theorem tree51_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree51 := ⟨by decide, tree49_closed, tree50_closed⟩
theorem tree52_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree52 := ⟨by decide, tree48_closed, tree51_closed⟩
theorem tree53_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree53 := by decide
theorem tree54_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree54 := by decide
theorem tree55_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree55 := ⟨by decide, tree53_closed, tree54_closed⟩
theorem tree56_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree56 := by decide
theorem tree57_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree57 := by decide
theorem tree58_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree58 := ⟨by decide, tree56_closed, tree57_closed⟩
theorem tree59_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree59 := ⟨by decide, tree55_closed, tree58_closed⟩
theorem tree60_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree60 := ⟨by decide, tree52_closed, tree59_closed⟩
theorem tree61_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree61 := ⟨by decide, tree45_closed, tree60_closed⟩
theorem tree62_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree62 := ⟨by decide, tree30_closed, tree61_closed⟩
theorem tree63_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree63 := by decide
theorem tree64_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree64 := by decide
theorem tree65_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree65 := ⟨by decide, tree63_closed, tree64_closed⟩
theorem tree66_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree66 := by decide
theorem tree67_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree67 := by decide
theorem tree68_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree68 := ⟨by decide, tree66_closed, tree67_closed⟩
theorem tree69_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree69 := ⟨by decide, tree65_closed, tree68_closed⟩
theorem tree70_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree70 := by decide
theorem tree71_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree71 := by decide
theorem tree72_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree72 := ⟨by decide, tree70_closed, tree71_closed⟩
theorem tree73_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree73 := by decide
theorem tree74_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree74 := by decide
theorem tree75_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree75 := ⟨by decide, tree73_closed, tree74_closed⟩
theorem tree76_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree76 := ⟨by decide, tree72_closed, tree75_closed⟩
theorem tree77_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree77 := ⟨by decide, tree69_closed, tree76_closed⟩
theorem tree78_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree78 := by decide
theorem tree79_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree79 := by decide
theorem tree80_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree80 := ⟨by decide, tree78_closed, tree79_closed⟩
theorem tree81_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree81 := by decide
theorem tree82_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree82 := by decide
theorem tree83_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree83 := ⟨by decide, tree81_closed, tree82_closed⟩
theorem tree84_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree84 := ⟨by decide, tree80_closed, tree83_closed⟩
theorem tree85_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree85 := by decide
theorem tree86_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree86 := by decide
theorem tree87_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree87 := ⟨by decide, tree85_closed, tree86_closed⟩
theorem tree88_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree88 := by decide
theorem tree89_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree89 := by decide
theorem tree90_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree90 := ⟨by decide, tree88_closed, tree89_closed⟩
theorem tree91_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree91 := ⟨by decide, tree87_closed, tree90_closed⟩
theorem tree92_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree92 := ⟨by decide, tree84_closed, tree91_closed⟩
theorem tree93_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree93 := ⟨by decide, tree77_closed, tree92_closed⟩
theorem tree94_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree94 := by decide
theorem tree95_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree95 := by decide
theorem tree96_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree96 := ⟨by decide, tree94_closed, tree95_closed⟩
theorem tree97_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree97 := by decide
theorem tree98_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree98 := by decide
theorem tree99_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree99 := ⟨by decide, tree97_closed, tree98_closed⟩
theorem tree100_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree100 := ⟨by decide, tree96_closed, tree99_closed⟩
theorem tree101_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree101 := by decide
theorem tree102_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree102 := by decide
theorem tree103_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree103 := ⟨by decide, tree101_closed, tree102_closed⟩
theorem tree104_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree104 := by decide
theorem tree105_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree105 := by decide
theorem tree106_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree106 := ⟨by decide, tree104_closed, tree105_closed⟩
theorem tree107_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree107 := ⟨by decide, tree103_closed, tree106_closed⟩
theorem tree108_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree108 := ⟨by decide, tree100_closed, tree107_closed⟩
theorem tree109_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree109 := by decide
theorem tree110_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree110 := by decide
theorem tree111_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree111 := ⟨by decide, tree109_closed, tree110_closed⟩
theorem tree112_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree112 := by decide
theorem tree113_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree113 := by decide
theorem tree114_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree114 := ⟨by decide, tree112_closed, tree113_closed⟩
theorem tree115_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree115 := ⟨by decide, tree111_closed, tree114_closed⟩
theorem tree116_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree116 := by decide
theorem tree117_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree117 := by decide
theorem tree118_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree118 := ⟨by decide, tree116_closed, tree117_closed⟩
theorem tree119_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree119 := by decide
theorem tree120_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree120 := by decide
theorem tree121_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree121 := ⟨by decide, tree119_closed, tree120_closed⟩
theorem tree122_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree122 := ⟨by decide, tree118_closed, tree121_closed⟩
theorem tree123_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree123 := ⟨by decide, tree115_closed, tree122_closed⟩
theorem tree124_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree124 := ⟨by decide, tree108_closed, tree123_closed⟩
theorem tree125_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree125 := ⟨by decide, tree93_closed, tree124_closed⟩
theorem tree126_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree126 := ⟨by decide, tree62_closed, tree125_closed⟩
theorem tree127_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree127 := by decide
theorem tree128_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree128 := by decide
theorem tree129_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree129 := ⟨by decide, tree127_closed, tree128_closed⟩
theorem tree130_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree130 := by decide
theorem tree131_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree131 := by decide
theorem tree132_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree132 := ⟨by decide, tree130_closed, tree131_closed⟩
theorem tree133_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree133 := ⟨by decide, tree129_closed, tree132_closed⟩
theorem tree134_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree134 := by decide
theorem tree135_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree135 := by decide
theorem tree136_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree136 := ⟨by decide, tree134_closed, tree135_closed⟩
theorem tree137_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree137 := by decide
theorem tree138_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree138 := by decide
theorem tree139_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree139 := ⟨by decide, tree137_closed, tree138_closed⟩
theorem tree140_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree140 := ⟨by decide, tree136_closed, tree139_closed⟩
theorem tree141_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree141 := ⟨by decide, tree133_closed, tree140_closed⟩
theorem tree142_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree142 := by decide
theorem tree143_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree143 := by decide
theorem tree144_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree144 := ⟨by decide, tree142_closed, tree143_closed⟩
theorem tree145_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree145 := by decide
theorem tree146_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree146 := by decide
theorem tree147_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree147 := ⟨by decide, tree145_closed, tree146_closed⟩
theorem tree148_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree148 := ⟨by decide, tree144_closed, tree147_closed⟩
theorem tree149_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree149 := by decide
theorem tree150_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree150 := by decide
theorem tree151_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree151 := ⟨by decide, tree149_closed, tree150_closed⟩
theorem tree152_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree152 := by decide
theorem tree153_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree153 := by decide
theorem tree154_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree154 := ⟨by decide, tree152_closed, tree153_closed⟩
theorem tree155_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree155 := ⟨by decide, tree151_closed, tree154_closed⟩
theorem tree156_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree156 := ⟨by decide, tree148_closed, tree155_closed⟩
theorem tree157_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree157 := ⟨by decide, tree141_closed, tree156_closed⟩
theorem tree158_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree158 := by decide
theorem tree159_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree159 := by decide
theorem tree160_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree160 := ⟨by decide, tree158_closed, tree159_closed⟩
theorem tree161_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree161 := by decide
theorem tree162_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree162 := by decide
theorem tree163_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree163 := ⟨by decide, tree161_closed, tree162_closed⟩
theorem tree164_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree164 := ⟨by decide, tree160_closed, tree163_closed⟩
theorem tree165_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree165 := by decide
theorem tree166_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree166 := by decide
theorem tree167_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree167 := ⟨by decide, tree165_closed, tree166_closed⟩
theorem tree168_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree168 := by decide
theorem tree169_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree169 := by decide
theorem tree170_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree170 := ⟨by decide, tree168_closed, tree169_closed⟩
theorem tree171_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree171 := ⟨by decide, tree167_closed, tree170_closed⟩
theorem tree172_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree172 := ⟨by decide, tree164_closed, tree171_closed⟩
theorem tree173_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree173 := by decide
theorem tree174_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree174 := by decide
theorem tree175_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree175 := ⟨by decide, tree173_closed, tree174_closed⟩
theorem tree176_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree176 := by decide
theorem tree177_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree177 := by decide
theorem tree178_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree178 := ⟨by decide, tree176_closed, tree177_closed⟩
theorem tree179_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree179 := ⟨by decide, tree175_closed, tree178_closed⟩
theorem tree180_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree180 := by decide
theorem tree181_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree181 := by decide
theorem tree182_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree182 := ⟨by decide, tree180_closed, tree181_closed⟩
theorem tree183_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree183 := by decide
theorem tree184_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree184 := by decide
theorem tree185_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree185 := ⟨by decide, tree183_closed, tree184_closed⟩
theorem tree186_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree186 := ⟨by decide, tree182_closed, tree185_closed⟩
theorem tree187_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree187 := ⟨by decide, tree179_closed, tree186_closed⟩
theorem tree188_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree188 := ⟨by decide, tree172_closed, tree187_closed⟩
theorem tree189_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree189 := ⟨by decide, tree157_closed, tree188_closed⟩
theorem tree190_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree190 := by decide
theorem tree191_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree191 := by decide
theorem tree192_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree192 := ⟨by decide, tree190_closed, tree191_closed⟩
theorem tree193_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree193 := by decide
theorem tree194_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree194 := by decide
theorem tree195_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree195 := ⟨by decide, tree193_closed, tree194_closed⟩
theorem tree196_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree196 := ⟨by decide, tree192_closed, tree195_closed⟩
theorem tree197_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree197 := by decide
theorem tree198_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree198 := by decide
theorem tree199_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree199 := ⟨by decide, tree197_closed, tree198_closed⟩
theorem tree200_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree200 := by decide
theorem tree201_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree201 := by decide
theorem tree202_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree202 := ⟨by decide, tree200_closed, tree201_closed⟩
theorem tree203_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree203 := ⟨by decide, tree199_closed, tree202_closed⟩
theorem tree204_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree204 := ⟨by decide, tree196_closed, tree203_closed⟩
theorem tree205_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree205 := by decide
theorem tree206_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree206 := by decide
theorem tree207_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree207 := ⟨by decide, tree205_closed, tree206_closed⟩
theorem tree208_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree208 := by decide
theorem tree209_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree209 := by decide
theorem tree210_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree210 := ⟨by decide, tree208_closed, tree209_closed⟩
theorem tree211_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree211 := ⟨by decide, tree207_closed, tree210_closed⟩
theorem tree212_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree212 := by decide
theorem tree213_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree213 := by decide
theorem tree214_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree214 := ⟨by decide, tree212_closed, tree213_closed⟩
theorem tree215_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree215 := by decide
theorem tree216_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree216 := by decide
theorem tree217_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree217 := ⟨by decide, tree215_closed, tree216_closed⟩
theorem tree218_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree218 := ⟨by decide, tree214_closed, tree217_closed⟩
theorem tree219_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree219 := ⟨by decide, tree211_closed, tree218_closed⟩
theorem tree220_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree220 := ⟨by decide, tree204_closed, tree219_closed⟩
theorem tree221_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree221 := by decide
theorem tree222_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree222 := by decide
theorem tree223_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree223 := ⟨by decide, tree221_closed, tree222_closed⟩
theorem tree224_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree224 := by decide
theorem tree225_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree225 := by decide
theorem tree226_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree226 := ⟨by decide, tree224_closed, tree225_closed⟩
theorem tree227_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree227 := ⟨by decide, tree223_closed, tree226_closed⟩
theorem tree228_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree228 := by decide
theorem tree229_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree229 := by decide
theorem tree230_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree230 := ⟨by decide, tree228_closed, tree229_closed⟩
theorem tree231_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree231 := by decide
theorem tree232_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree232 := by decide
theorem tree233_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree233 := ⟨by decide, tree231_closed, tree232_closed⟩
theorem tree234_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree234 := ⟨by decide, tree230_closed, tree233_closed⟩
theorem tree235_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree235 := ⟨by decide, tree227_closed, tree234_closed⟩
theorem tree236_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree236 := by decide
theorem tree237_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree237 := by decide
theorem tree238_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree238 := ⟨by decide, tree236_closed, tree237_closed⟩
theorem tree239_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree239 := by decide
theorem tree240_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree240 := by decide
theorem tree241_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree241 := ⟨by decide, tree239_closed, tree240_closed⟩
theorem tree242_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree242 := ⟨by decide, tree238_closed, tree241_closed⟩
theorem tree243_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree243 := by decide
theorem tree244_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree244 := by decide
theorem tree245_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree245 := ⟨by decide, tree243_closed, tree244_closed⟩
theorem tree246_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree246 := by decide
theorem tree247_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree247 := by decide
theorem tree248_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree248 := ⟨by decide, tree246_closed, tree247_closed⟩
theorem tree249_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree249 := ⟨by decide, tree245_closed, tree248_closed⟩
theorem tree250_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree250 := ⟨by decide, tree242_closed, tree249_closed⟩
theorem tree251_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree251 := ⟨by decide, tree235_closed, tree250_closed⟩
theorem tree252_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree252 := ⟨by decide, tree220_closed, tree251_closed⟩
theorem tree253_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree253 := ⟨by decide, tree189_closed, tree252_closed⟩
theorem tree254_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree254 := ⟨by decide, tree126_closed, tree253_closed⟩
theorem tree255_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree255 := by decide
theorem tree256_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree256 := by decide
theorem tree257_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree257 := ⟨by decide, tree255_closed, tree256_closed⟩
theorem tree258_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree258 := by decide
theorem tree259_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree259 := by decide
theorem tree260_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree260 := ⟨by decide, tree258_closed, tree259_closed⟩
theorem tree261_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree261 := ⟨by decide, tree257_closed, tree260_closed⟩
theorem tree262_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree262 := by decide
theorem tree263_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree263 := by decide
theorem tree264_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree264 := ⟨by decide, tree262_closed, tree263_closed⟩
theorem tree265_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree265 := by decide
theorem tree266_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree266 := by decide
theorem tree267_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree267 := ⟨by decide, tree265_closed, tree266_closed⟩
theorem tree268_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree268 := ⟨by decide, tree264_closed, tree267_closed⟩
theorem tree269_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree269 := ⟨by decide, tree261_closed, tree268_closed⟩
theorem tree270_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree270 := by decide
theorem tree271_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree271 := by decide
theorem tree272_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree272 := ⟨by decide, tree270_closed, tree271_closed⟩
theorem tree273_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree273 := by decide
theorem tree274_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree274 := by decide
theorem tree275_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree275 := ⟨by decide, tree273_closed, tree274_closed⟩
theorem tree276_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree276 := ⟨by decide, tree272_closed, tree275_closed⟩
theorem tree277_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree277 := by decide
theorem tree278_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree278 := by decide
theorem tree279_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree279 := ⟨by decide, tree277_closed, tree278_closed⟩
theorem tree280_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree280 := by decide
theorem tree281_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree281 := by decide
theorem tree282_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree282 := ⟨by decide, tree280_closed, tree281_closed⟩
theorem tree283_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree283 := ⟨by decide, tree279_closed, tree282_closed⟩
theorem tree284_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree284 := ⟨by decide, tree276_closed, tree283_closed⟩
theorem tree285_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree285 := ⟨by decide, tree269_closed, tree284_closed⟩
theorem tree286_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree286 := by decide
theorem tree287_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree287 := by decide
theorem tree288_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree288 := ⟨by decide, tree286_closed, tree287_closed⟩
theorem tree289_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree289 := by decide
theorem tree290_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree290 := by decide
theorem tree291_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree291 := ⟨by decide, tree289_closed, tree290_closed⟩
theorem tree292_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree292 := ⟨by decide, tree288_closed, tree291_closed⟩
theorem tree293_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree293 := by decide
theorem tree294_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree294 := by decide
theorem tree295_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree295 := ⟨by decide, tree293_closed, tree294_closed⟩
theorem tree296_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree296 := by decide
theorem tree297_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree297 := by decide
theorem tree298_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree298 := ⟨by decide, tree296_closed, tree297_closed⟩
theorem tree299_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree299 := ⟨by decide, tree295_closed, tree298_closed⟩
theorem tree300_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree300 := ⟨by decide, tree292_closed, tree299_closed⟩
theorem tree301_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree301 := by decide
theorem tree302_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree302 := by decide
theorem tree303_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree303 := ⟨by decide, tree301_closed, tree302_closed⟩
theorem tree304_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree304 := by decide
theorem tree305_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree305 := by decide
theorem tree306_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree306 := ⟨by decide, tree304_closed, tree305_closed⟩
theorem tree307_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree307 := ⟨by decide, tree303_closed, tree306_closed⟩
theorem tree308_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree308 := by decide
theorem tree309_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree309 := by decide
theorem tree310_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree310 := ⟨by decide, tree308_closed, tree309_closed⟩
theorem tree311_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree311 := by decide
theorem tree312_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree312 := by decide
theorem tree313_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree313 := ⟨by decide, tree311_closed, tree312_closed⟩
theorem tree314_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree314 := ⟨by decide, tree310_closed, tree313_closed⟩
theorem tree315_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree315 := ⟨by decide, tree307_closed, tree314_closed⟩
theorem tree316_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree316 := ⟨by decide, tree300_closed, tree315_closed⟩
theorem tree317_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree317 := ⟨by decide, tree285_closed, tree316_closed⟩
theorem tree318_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree318 := by decide
theorem tree319_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree319 := by decide
theorem tree320_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree320 := ⟨by decide, tree318_closed, tree319_closed⟩
theorem tree321_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree321 := by decide
theorem tree322_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree322 := by decide
theorem tree323_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree323 := ⟨by decide, tree321_closed, tree322_closed⟩
theorem tree324_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree324 := ⟨by decide, tree320_closed, tree323_closed⟩
theorem tree325_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree325 := by decide
theorem tree326_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree326 := by decide
theorem tree327_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree327 := ⟨by decide, tree325_closed, tree326_closed⟩
theorem tree328_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree328 := by decide
theorem tree329_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree329 := by decide
theorem tree330_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree330 := ⟨by decide, tree328_closed, tree329_closed⟩
theorem tree331_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree331 := ⟨by decide, tree327_closed, tree330_closed⟩
theorem tree332_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree332 := ⟨by decide, tree324_closed, tree331_closed⟩
theorem tree333_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree333 := by decide
theorem tree334_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree334 := by decide
theorem tree335_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree335 := ⟨by decide, tree333_closed, tree334_closed⟩
theorem tree336_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree336 := by decide
theorem tree337_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree337 := by decide
theorem tree338_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree338 := ⟨by decide, tree336_closed, tree337_closed⟩
theorem tree339_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree339 := ⟨by decide, tree335_closed, tree338_closed⟩
theorem tree340_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree340 := by decide
theorem tree341_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree341 := by decide
theorem tree342_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree342 := ⟨by decide, tree340_closed, tree341_closed⟩
theorem tree343_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree343 := by decide
theorem tree344_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree344 := by decide
theorem tree345_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree345 := ⟨by decide, tree343_closed, tree344_closed⟩
theorem tree346_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree346 := ⟨by decide, tree342_closed, tree345_closed⟩
theorem tree347_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree347 := ⟨by decide, tree339_closed, tree346_closed⟩
theorem tree348_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree348 := ⟨by decide, tree332_closed, tree347_closed⟩
theorem tree349_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree349 := by decide
theorem tree350_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree350 := by decide
theorem tree351_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree351 := ⟨by decide, tree349_closed, tree350_closed⟩
theorem tree352_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree352 := by decide
theorem tree353_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree353 := by decide
theorem tree354_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree354 := ⟨by decide, tree352_closed, tree353_closed⟩
theorem tree355_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree355 := ⟨by decide, tree351_closed, tree354_closed⟩
theorem tree356_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree356 := by decide
theorem tree357_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree357 := by decide
theorem tree358_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree358 := ⟨by decide, tree356_closed, tree357_closed⟩
theorem tree359_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree359 := by decide
theorem tree360_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree360 := by decide
theorem tree361_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree361 := ⟨by decide, tree359_closed, tree360_closed⟩
theorem tree362_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree362 := ⟨by decide, tree358_closed, tree361_closed⟩
theorem tree363_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree363 := ⟨by decide, tree355_closed, tree362_closed⟩
theorem tree364_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree364 := by decide
theorem tree365_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree365 := by decide
theorem tree366_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree366 := ⟨by decide, tree364_closed, tree365_closed⟩
theorem tree367_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree367 := by decide
theorem tree368_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree368 := by decide
theorem tree369_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree369 := ⟨by decide, tree367_closed, tree368_closed⟩
theorem tree370_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree370 := ⟨by decide, tree366_closed, tree369_closed⟩
theorem tree371_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree371 := by decide
theorem tree372_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree372 := by decide
theorem tree373_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree373 := ⟨by decide, tree371_closed, tree372_closed⟩
theorem tree374_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree374 := by decide
theorem tree375_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree375 := by decide
theorem tree376_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree376 := ⟨by decide, tree374_closed, tree375_closed⟩
theorem tree377_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree377 := ⟨by decide, tree373_closed, tree376_closed⟩
theorem tree378_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree378 := ⟨by decide, tree370_closed, tree377_closed⟩
theorem tree379_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree379 := ⟨by decide, tree363_closed, tree378_closed⟩
theorem tree380_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree380 := ⟨by decide, tree348_closed, tree379_closed⟩
theorem tree381_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree381 := ⟨by decide, tree317_closed, tree380_closed⟩
theorem tree382_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree382 := by decide
theorem tree383_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree383 := by decide
theorem tree384_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree384 := ⟨by decide, tree382_closed, tree383_closed⟩
theorem tree385_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree385 := by decide
theorem tree386_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree386 := by decide
theorem tree387_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree387 := ⟨by decide, tree385_closed, tree386_closed⟩
theorem tree388_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree388 := ⟨by decide, tree384_closed, tree387_closed⟩
theorem tree389_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree389 := by decide
theorem tree390_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree390 := by decide
theorem tree391_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree391 := ⟨by decide, tree389_closed, tree390_closed⟩
theorem tree392_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree392 := by decide
theorem tree393_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree393 := by decide
theorem tree394_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree394 := ⟨by decide, tree392_closed, tree393_closed⟩
theorem tree395_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree395 := ⟨by decide, tree391_closed, tree394_closed⟩
theorem tree396_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree396 := ⟨by decide, tree388_closed, tree395_closed⟩
theorem tree397_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree397 := by decide
theorem tree398_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree398 := by decide
theorem tree399_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree399 := ⟨by decide, tree397_closed, tree398_closed⟩
theorem tree400_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree400 := by decide
theorem tree401_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree401 := by decide
theorem tree402_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree402 := ⟨by decide, tree400_closed, tree401_closed⟩
theorem tree403_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree403 := ⟨by decide, tree399_closed, tree402_closed⟩
theorem tree404_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree404 := by decide
theorem tree405_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree405 := by decide
theorem tree406_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree406 := ⟨by decide, tree404_closed, tree405_closed⟩
theorem tree407_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree407 := by decide
theorem tree408_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree408 := by decide
theorem tree409_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree409 := ⟨by decide, tree407_closed, tree408_closed⟩
theorem tree410_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree410 := ⟨by decide, tree406_closed, tree409_closed⟩
theorem tree411_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree411 := ⟨by decide, tree403_closed, tree410_closed⟩
theorem tree412_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree412 := ⟨by decide, tree396_closed, tree411_closed⟩
theorem tree413_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree413 := by decide
theorem tree414_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree414 := by decide
theorem tree415_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree415 := ⟨by decide, tree413_closed, tree414_closed⟩
theorem tree416_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree416 := by decide
theorem tree417_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree417 := by decide
theorem tree418_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree418 := ⟨by decide, tree416_closed, tree417_closed⟩
theorem tree419_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree419 := ⟨by decide, tree415_closed, tree418_closed⟩
theorem tree420_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree420 := by decide
theorem tree421_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree421 := by decide
theorem tree422_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree422 := ⟨by decide, tree420_closed, tree421_closed⟩
theorem tree423_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree423 := by decide
theorem tree424_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree424 := by decide
theorem tree425_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree425 := ⟨by decide, tree423_closed, tree424_closed⟩
theorem tree426_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree426 := ⟨by decide, tree422_closed, tree425_closed⟩
theorem tree427_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree427 := ⟨by decide, tree419_closed, tree426_closed⟩
theorem tree428_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree428 := by decide
theorem tree429_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree429 := by decide
theorem tree430_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree430 := ⟨by decide, tree428_closed, tree429_closed⟩
theorem tree431_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree431 := by decide
theorem tree432_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree432 := by decide
theorem tree433_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree433 := ⟨by decide, tree431_closed, tree432_closed⟩
theorem tree434_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree434 := ⟨by decide, tree430_closed, tree433_closed⟩
theorem tree435_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree435 := by decide
theorem tree436_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree436 := by decide
theorem tree437_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree437 := ⟨by decide, tree435_closed, tree436_closed⟩
theorem tree438_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree438 := by decide
theorem tree439_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree439 := by decide
theorem tree440_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree440 := ⟨by decide, tree438_closed, tree439_closed⟩
theorem tree441_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree441 := ⟨by decide, tree437_closed, tree440_closed⟩
theorem tree442_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree442 := ⟨by decide, tree434_closed, tree441_closed⟩
theorem tree443_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree443 := ⟨by decide, tree427_closed, tree442_closed⟩
theorem tree444_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree444 := ⟨by decide, tree412_closed, tree443_closed⟩
theorem tree445_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree445 := by decide
theorem tree446_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree446 := by decide
theorem tree447_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree447 := ⟨by decide, tree445_closed, tree446_closed⟩
theorem tree448_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree448 := by decide
theorem tree449_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree449 := by decide
theorem tree450_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree450 := ⟨by decide, tree448_closed, tree449_closed⟩
theorem tree451_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree451 := ⟨by decide, tree447_closed, tree450_closed⟩
theorem tree452_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree452 := by decide
theorem tree453_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree453 := by decide
theorem tree454_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree454 := ⟨by decide, tree452_closed, tree453_closed⟩
theorem tree455_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree455 := by decide
theorem tree456_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree456 := by decide
theorem tree457_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree457 := ⟨by decide, tree455_closed, tree456_closed⟩
theorem tree458_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree458 := ⟨by decide, tree454_closed, tree457_closed⟩
theorem tree459_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree459 := ⟨by decide, tree451_closed, tree458_closed⟩
theorem tree460_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree460 := by decide
theorem tree461_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree461 := by decide
theorem tree462_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree462 := ⟨by decide, tree460_closed, tree461_closed⟩
theorem tree463_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree463 := by decide
theorem tree464_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree464 := by decide
theorem tree465_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree465 := ⟨by decide, tree463_closed, tree464_closed⟩
theorem tree466_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree466 := ⟨by decide, tree462_closed, tree465_closed⟩
theorem tree467_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree467 := by decide
theorem tree468_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree468 := by decide
theorem tree469_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree469 := ⟨by decide, tree467_closed, tree468_closed⟩
theorem tree470_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree470 := by decide
theorem tree471_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree471 := by decide
theorem tree472_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree472 := ⟨by decide, tree470_closed, tree471_closed⟩
theorem tree473_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree473 := ⟨by decide, tree469_closed, tree472_closed⟩
theorem tree474_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree474 := ⟨by decide, tree466_closed, tree473_closed⟩
theorem tree475_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree475 := ⟨by decide, tree459_closed, tree474_closed⟩
theorem tree476_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree476 := by decide
theorem tree477_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree477 := by decide
theorem tree478_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree478 := ⟨by decide, tree476_closed, tree477_closed⟩
theorem tree479_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree479 := by decide
theorem tree480_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree480 := by decide
theorem tree481_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree481 := ⟨by decide, tree479_closed, tree480_closed⟩
theorem tree482_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree482 := ⟨by decide, tree478_closed, tree481_closed⟩
theorem tree483_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree483 := by decide
theorem tree484_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree484 := by decide
theorem tree485_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree485 := ⟨by decide, tree483_closed, tree484_closed⟩
theorem tree486_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree486 := by decide
theorem tree487_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree487 := by decide
theorem tree488_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree488 := ⟨by decide, tree486_closed, tree487_closed⟩
theorem tree489_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree489 := ⟨by decide, tree485_closed, tree488_closed⟩
theorem tree490_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree490 := ⟨by decide, tree482_closed, tree489_closed⟩
theorem tree491_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree491 := by decide
theorem tree492_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree492 := by decide
theorem tree493_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree493 := ⟨by decide, tree491_closed, tree492_closed⟩
theorem tree494_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree494 := by decide
theorem tree495_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree495 := by decide
theorem tree496_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree496 := ⟨by decide, tree494_closed, tree495_closed⟩
theorem tree497_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree497 := ⟨by decide, tree493_closed, tree496_closed⟩
theorem tree498_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree498 := by decide
theorem tree499_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree499 := by decide
theorem tree500_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree500 := ⟨by decide, tree498_closed, tree499_closed⟩
theorem tree501_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree501 := by decide
theorem tree502_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree502 := by decide
theorem tree503_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree503 := ⟨by decide, tree501_closed, tree502_closed⟩
theorem tree504_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree504 := ⟨by decide, tree500_closed, tree503_closed⟩
theorem tree505_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree505 := ⟨by decide, tree497_closed, tree504_closed⟩
theorem tree506_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree506 := ⟨by decide, tree490_closed, tree505_closed⟩
theorem tree507_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree507 := ⟨by decide, tree475_closed, tree506_closed⟩
theorem tree508_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree508 := ⟨by decide, tree444_closed, tree507_closed⟩
theorem tree509_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree509 := ⟨by decide, tree381_closed, tree508_closed⟩
theorem tree510_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree510 := ⟨by decide, tree254_closed, tree509_closed⟩
theorem tree_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree := tree510_closed

theorem initial_contained : contains (code initial) tree = true := by decide

theorem reach_classified (st : State) (h : R st) : Classified slots st :=
  LanceStateCode.contains_all _ tree tree_correct tree_classified st
    (LanceStateCode.reach_length _ _ _ h)
    (LanceStateCode.reach_contained slots initial rfl tree tree_correct initial_contained tree_closed st h)

theorem captured_checked : (OrderedFile.enumerate 0 OrderedFile.lanceSlots).all
    (fun u => contains (code (capture u)) tree) = true := by decide

theorem captured_contained : ∀ u ∈ OrderedFile.enumerate 0 OrderedFile.lanceSlots,
    contains (code (capture u)) tree = true := List.all_eq_true.mp captured_checked

theorem singleton_checked : (OrderedFile.enumerate 0 OrderedFile.lanceSlots).all
    (fun u => (List.finRange 6).all (fun i => if decide (eligible u i) then contains (code (mark u i)) tree else true)) = true := by decide

theorem singleton_contained : ∀ u ∈ OrderedFile.enumerate 0 OrderedFile.lanceSlots,
    ∀ i : Fin 6, eligible u i → contains (code (mark u i)) tree = true := by
  intro u hu i hi
  have h := (List.all_eq_true.mp ((List.all_eq_true.mp singleton_checked) u hu)) i (List.mem_finRange i)
  simpa only [decide_eq_true hi,ite_true] using h

theorem capture_reachable (u : List Nat) (h : valid u) : R (capture u) :=
  LanceStateCode.contains_all _ tree tree_correct tree_reachable _
    (LanceStateCode.capture_length u h) (captured_contained u ((valid_mem u).mp h))

theorem singleton_reachable (u : List Nat) (h : valid u) (i : Fin 6) (hi : eligible u i) : R (mark u i) :=
  LanceStateCode.contains_all _ tree tree_correct tree_reachable _
    (LanceStateCode.mark_length u h i) (singleton_contained u ((valid_mem u).mp h) i hi)

theorem projected_iff (u : List Nat) : (∃ st, R st ∧ st.map shown=u) ↔ valid u := by
  constructor
  · rintro ⟨st,hs,rfl⟩
    simpa only [valid,← slots_ordered] using (reach_classified st hs).2.1
  · intro hu
    exact ⟨capture u,capture_reachable u hu,capture_projection u hu⟩

end ChuShogi.LanceCachedCertificate
