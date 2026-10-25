/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode071
import Proofs.RadenkovicGutmanD41Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-90774,0],[-90774,-18081,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1524339,-1705887,0],[-1705887,-217956,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-31160943,-13681782,0],[-13681782,-1063253,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-282672450,-62071007,0],[-62071007,-2723712,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1513480437,-178023722,0],[-178023722,-4009144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5367979407,-342132413,0],[-342132413,-3524114,0],[0,0]],[[0,0,0],[0,0],[0]],[[-13422228712,-456128526,0],[-456128526,-1864229],[0]],[[0,0,0],[0,0],[0]],[[-24585958320,-430715660,0],[-430715660,-579412],[0]],[[0,0,0],[0,0],[0]],[[-33831508955,-291112054,0],[-291112054,-97293],[0]],[[0,0,0],[0,0],[0]],[[-35558539696,-140961567,0],[-140961567,-6806],[0]],[[0,0,0],[0,0],[0]],[[-28844254318,-48411078,0],[-48411078,0],[0]],[[0,0],[0]],[[-18152331308,-11496277],[-11496277]],[[0,0],[0]],[[-8865987395,-1793258],[-1793258]],[[0,0],[0]],[[-3344696647,-165189],[-165189]],[[0,0],[0]],[[-963805696,-6806],[-6806]],[[0,0],[0]],[[-207972500,0],[0]],[[0]],[[-32499101]],[[0]],[[-3470527]],[[0]],[[-226443]],[[0]],[[-6806]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
