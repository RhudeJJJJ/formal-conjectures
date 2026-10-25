/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode119
import Proofs.RadenkovicGutmanD27Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-50],[0]],[[0,0],[0]],[[-742,0],[0,0]],[[0,0],[0,0]],[[-4588,0],[0,0]],[[0,0],[0,0]],[[-15302,0],[0,0]],[[0,0],[0,0]],[[-29800,0],[0,0]],[[0,0],[0,0]],[[-34248,-50],[-50,0]],[[0,0],[0,0]],[[-22036,-400],[-400,0]],[[0,0],[0,0]],[[-6230,-1100],[-1100,0]],[[0,0],[0,0]],[[474,-1200],[-1200,0]],[[0,0],[0,0]],[[522,-450],[-450,0]],[[0],[0,0]],[[0],[0,-50]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
