/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode033
import Proofs.RadenkovicGutmanD30Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2700],[0,2700]],[[0,0,0],[0,0,0],[0,0]],[[0,-24300,24300],[-24300,89100,11700],[24300,11700]],[[0,0,0],[0,0,0],[0,0]],[[-364500,267300,170100],[267300,610200,14400],[170100,14400]],[[0,0,0],[0,0,0],[0,0]],[[-2308500,3758400,469800],[3758400,1640700,6300],[469800,6300]],[[0,0,0],[0,0,0],[0,0]],[[1263600,17009100,681300],[17009100,2313000,900],[681300,900]],[[0,0,0],[0,0],[0]],[[59456700,42114600,572400],[42114600,1890000],[572400]],[[0,0,0],[0,0],[0]],[[282626100,66159900,287100],[66159900,923400],[287100]],[[0,0,0],[0,0],[0]],[[748053000,70392600,84600],[70392600,265500],[84600]],[[0,0,0],[0,0],[0]],[[1327806000,52316100,13500],[52316100,41400],[13500]],[[0,0,0],[0,0],[0]],[[1695847500,27456300,900],[27456300,2700],[900]],[[0,0],[0]],[[1613070000,10125000],[10125000]],[[0,0],[0]],[[1163019600,2565000],[2565000]],[[0,0],[0]],[[640288800,424800],[424800]],[[0,0],[0]],[[268996500,41400],[41400]],[[0,0],[0]],[[85511700,1800],[1800]],[[0]],[[20201400]],[[0]],[[3434400]],[[0]],[[396900]],[[0]],[[27900]],[[0]],[[900]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
