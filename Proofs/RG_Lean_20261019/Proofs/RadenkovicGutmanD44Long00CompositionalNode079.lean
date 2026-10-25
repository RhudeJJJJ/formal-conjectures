/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode033
import Proofs.RadenkovicGutmanD44Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5808],[0,5808]],[[0,0,0],[0,0,0],[0,0]],[[0,-52272,52272],[-52272,191664,25168],[52272,25168]],[[0,0,0],[0,0,0],[0,0]],[[-784080,574992,365904],[574992,1312608,30976],[365904,30976]],[[0,0,0],[0,0,0],[0,0]],[[-4965840,8084736,1010592],[8084736,3529328,13552],[1010592,13552]],[[0,0,0],[0,0,0],[0,0]],[[2718144,36588464,1465552],[36588464,4975520,1936],[1465552,1936]],[[0,0,0],[0,0],[0]],[[127897968,90593184,1231296],[90593184,4065600],[1231296]],[[0,0,0],[0,0],[0]],[[607960144,142317296,617584],[142317296,1986336],[617584]],[[0,0,0],[0,0],[0]],[[1609145120,151422304,181984],[151422304,571120],[181984]],[[0,0,0],[0,0],[0]],[[2856258240,112537744,29040],[112537744,89056],[29040]],[[0,0,0],[0,0],[0]],[[3647956400,59061552,1936],[59061552,5808],[1936]],[[0,0],[0]],[[3469892800,21780000],[21780000]],[[0,0],[0]],[[2501784384,5517600],[5517600]],[[0,0],[0]],[[1377332352,913792],[913792]],[[0,0],[0]],[[578641360,89056],[89056]],[[0,0],[0]],[[183945168,3872],[3872]],[[0]],[[43455456]],[[0]],[[7387776]],[[0]],[[853776]],[[0]],[[60016]],[[0]],[[1936]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
