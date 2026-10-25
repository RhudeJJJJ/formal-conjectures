/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode092
import Proofs.RadenkovicGutmanD24Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1728,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15552,-15552,0],[-15552,-14544,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-405648,-172368,0],[-172368,-47136,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3941136,-811296,0],[-811296,-75216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20779776,-2142000,0],[-2142000,-63264,0],[0,0]],[[0,0,0],[0,0],[0]],[[-69021264,-3529632,0],[-3529632,-26688],[0]],[[0,0,0],[0,0],[0]],[[-156002544,-3804912,0],[-3804912,-3552],[0]],[[0,0,0],[0,0],[0]],[[-250773984,-2713152,0],[-2713152,1200],[0]],[[0,0,0],[0,0],[0]],[[-294031104,-1242912,0],[-1242912,480],[0]],[[0,0,0],[0,0],[0]],[[-254372016,-321792,0],[-321792,48],[0]],[[0,0],[0]],[[-162087648,-16752],[-16752]],[[0,0],[0]],[[-74521056,17760],[17760]],[[0,0],[0]],[[-23223360,6096],[6096]],[[0,0],[0]],[[-3894192,864],[864]],[[0,0],[0]],[[251088,48],[48]],[[0]],[[344736]],[[0]],[[98496]],[[0]],[[15216]],[[0]],[[1296]],[[0]],[[48]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
