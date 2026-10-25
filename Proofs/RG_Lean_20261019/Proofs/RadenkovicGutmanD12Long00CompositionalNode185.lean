/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode184
import Proofs.RadenkovicGutmanD12Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[12,0],[0]],[[0,0],[0]],[[192,0],[0]],[[0,0],[0]],[[1284,0],[0]],[[0,0],[0]],[[4656,0],[0]],[[0,0],[0]],[[9936,0],[0]],[[0,0],[0]],[[12672,12],[12]],[[0,0],[0]],[[9348,84],[84]],[[0,0],[0]],[[3600,192],[192]],[[0,0],[0]],[[540,156],[156]],[[0,0],[0]],[[0,36],[36]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
