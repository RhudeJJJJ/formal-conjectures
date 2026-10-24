/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode177
import Proofs.RadenkovicGutmanD4Long00CompositionalNode184
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .plus e177 e184
noncomputable def p185 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-64,0],[0,0]],[[0,0],[0,0]],[[-424,0],[0,0]],[[0,0],[0,0]],[[-1496,0],[0,0]],[[0,0],[0,0]],[[-2992,0],[0,0]],[[0,0],[0,0]],[[-3264,-4],[-4,0]],[[0,0],[0,0]],[[-1496,-28],[-28,0]],[[0,0],[0,0]],[[328,-60],[-60,0]],[[0,0],[0,0]],[[564,-32],[-32,0]],[[0,0],[0,0]],[[144,16],[16,0]],[[0,0],[0,0]],[[0,12],[12,-4]]]
theorem step185 : p185=NestedHorner.add p177 p184 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_plus e185 e177 e184 p177 p184 p185 rfl h177 h184 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
