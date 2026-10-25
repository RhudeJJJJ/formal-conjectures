/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode079
import Proofs.RadenkovicGutmanD22Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-26136,0],[-26136,-4356,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-431244,-378972,0],[-378972,-37752,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7043652,-2334816,0],[-2334816,-128260,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-51174288,-8090060,0],[-8090060,-221672,0],[0,0]],[[0,0,0],[0,0],[0]],[[-219854580,-17633088,0],[-17633088,-214896],[0]],[[0,0,0],[0,0],[0]],[[-626842436,-25660228,0],[-25660228,-121000],[0]],[[0,0,0],[0,0],[0]],[[-1262162616,-25804944,0],[-25804944,-39204],[0]],[[0,0,0],[0,0],[0]],[[-1863940144,-18270032,0],[-18270032,-6776],[0]],[[0,0,0],[0,0],[0]],[[-2068102476,-9162120,0],[-9162120,-484],[0]],[[0,0],[0]],[[-1750208856,-3232636],[-3232636]],[[0,0],[0]],[[-1139224680,-784080],[-784080]],[[0,0],[0]],[[-571782112,-124388],[-124388]],[[0,0],[0]],[[-220562188,-11616],[-11616]],[[0,0],[0]],[[-64738388,-484],[-484]],[[0]],[[-14186040]],[[0]],[[-2245760]],[[0]],[[-242484]],[[0]],[[-15972]],[[0]],[[-484]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
