/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode095
import Proofs.RadenkovicGutmanD45Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29160,-29160,0],[-29160,-28080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-767880,-330480,0],[-330480,-95400,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7581600,-1603800,0],[-1603800,-164880,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-40857480,-4417200,0],[-4417200,-159840,0],[0,0]],[[0,0,0],[0,0],[0]],[[-139629240,-7722360,0],[-7722360,-90000],[0]],[[0,0,0],[0,0],[0]],[[-327412080,-9064800,0],[-9064800,-29160],[0]],[[0,0,0],[0,0],[0]],[[-552054240,-7353360,0],[-7353360,-5040],[0]],[[0,0,0],[0,0],[0]],[[-689321880,-4168800,0],[-4168800,-360],[0]],[[0,0,0],[0,0],[0]],[[-649278000,-1645560,0],[-1645560,0],[0]],[[0,0],[0]],[[-466233840,-442800],[-442800]],[[0,0],[0]],[[-256285440,-77400],[-77400]],[[0,0],[0]],[[-107615160,-7920],[-7920]],[[0,0],[0]],[[-34205400,-360],[-360]],[[0,0],[0]],[[-8080560,0],[0]],[[0]],[[-1373760]],[[0]],[[-158760]],[[0]],[[-11160]],[[0]],[[-360]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
