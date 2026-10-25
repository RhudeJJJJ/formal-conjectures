/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode071
import Proofs.RadenkovicGutmanD45Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-109350,0],[-109350,-21465,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1833435,-2052135,0],[-2052135,-259740,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-37462095,-16448670,0],[-16448670,-1270845,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-339760170,-74608695,0],[-74608695,-3262680,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1819028205,-213984450,0],[-213984450,-4809960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6451864335,-411285285,0],[-411285285,-4232610,0],[0,0]],[[0,0,0],[0,0],[0]],[[-16133606640,-548397990,0],[-548397990,-2240685],[0]],[[0,0,0],[0,0],[0]],[[-29555386560,-517918860,0],[-517918860,-696780],[0]],[[0,0,0],[0,0],[0]],[[-40674076515,-350099190,0],[-350099190,-117045],[0]],[[0,0,0],[0,0],[0]],[[-42755085720,-169545735,0],[-169545735,-8190],[0]],[[0,0,0],[0,0],[0]],[[-34685622990,-58234590,0],[-58234590,0],[0]],[[0,0],[0]],[[-21830651100,-13830525],[-13830525]],[[0,0],[0]],[[-10663573995,-2157570],[-2157570]],[[0,0],[0]],[[-4023193815,-198765],[-198765]],[[0,0],[0]],[[-1159416360,-8190],[-8190]],[[0,0],[0]],[[-250200900,0],[0]],[[0]],[[-39100725]],[[0]],[[-4175775]],[[0]],[[-272475]],[[0]],[[-8190]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
