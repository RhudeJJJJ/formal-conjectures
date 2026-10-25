/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode073
import Proofs.RadenkovicGutmanD24Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1728,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15552,-139968,0],[-139968,-36144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2466288,-1984176,0],[-1984176,-234336,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-37676016,-12013920,0],[-12013920,-711216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-266408064,-41081040,0],[-41081040,-1162464,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1126497072,-88646880,0],[-88646880,-1092288,0],[0,0]],[[0,0,0],[0,0],[0]],[[-3177214224,-128015376,0],[-128015376,-603552],[0]],[[0,0,0],[0,0],[0]],[[-6346395168,-127970496,0],[-127970496,-193200],[0]],[[0,0,0],[0,0],[0]],[[-9314216832,-90175200,0],[-90175200,-33120],[0]],[[0,0,0],[0,0],[0]],[[-10283042640,-45048192,0],[-45048192,-2352],[0]],[[0,0,0],[0,0],[0]],[[-8666801184,-15843984,0],[-15843984,0],[0]],[[0,0],[0]],[[-5621936160,-3832800],[-3832800]],[[0,0],[0]],[[-2813438016,-606672],[-606672]],[[0,0],[0]],[[-1082540496,-56544],[-56544]],[[0,0],[0]],[[-317046480,-2352],[-2352]],[[0,0],[0]],[[-69340320,0],[0]],[[0]],[[-10958400]],[[0]],[[-1181424]],[[0]],[[-77712]],[[0]],[[-2352]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
