/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode079
import Proofs.RadenkovicGutmanD37Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-73926,0],[-73926,-12321,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1219779,-1071927,0],[-1071927,-106782,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19923057,-6604056,0],[-6604056,-362785,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-144747108,-22882835,0],[-22882835,-627002,0],[0,0]],[[0,0,0],[0,0],[0]],[[-621861405,-49875408,0],[-49875408,-607836],[0]],[[0,0,0],[0,0],[0]],[[-1773031601,-72580273,0],[-72580273,-342250],[0]],[[0,0,0],[0,0],[0]],[[-3570042606,-72989604,0],[-72989604,-110889],[0]],[[0,0,0],[0,0],[0]],[[-5272177804,-51677012,0],[-51677012,-19166],[0]],[[0,0,0],[0,0],[0]],[[-5849653491,-25915170,0],[-25915170,-1369],[0]],[[0,0],[0]],[[-4950487446,-9143551],[-9143551]],[[0,0],[0]],[[-3222311130,-2217780],[-2217780]],[[0,0],[0]],[[-1617292792,-351833],[-351833]],[[0,0],[0]],[[-623862883,-32856],[-32856]],[[0,0],[0]],[[-183113333,-1369],[-1369]],[[0]],[[-40125390]],[[0]],[[-6352160]],[[0]],[[-685869]],[[0]],[[-45177]],[[0]],[[-1369]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
