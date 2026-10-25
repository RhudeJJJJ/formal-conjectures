/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode036
import Proofs.RadenkovicGutmanD28Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-52]],[[0,0],[0]],[[540,-468],[-468]],[[0,0],[0]],[[468,-1248],[-1248]],[[0,0],[0]],[[-6564,-1144],[-1144]],[[0,0],[0]],[[-23064,-416],[-416]],[[0,0],[0]],[[-35760,-52],[-52]],[[0]],[[-31072]],[[0]],[[-15940]],[[0]],[[-4776]],[[0]],[[-772]],[[0]],[[-52]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
