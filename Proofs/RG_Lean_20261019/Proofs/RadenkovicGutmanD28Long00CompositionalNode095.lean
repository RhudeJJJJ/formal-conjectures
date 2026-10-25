/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode093
import Proofs.RadenkovicGutmanD28Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,784]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-7056],[0,-14112,23184],[-7056,23184,56]],[[0,0,0],[0,0,0],[0,0]],[[-63504,-235872,84000],[-235872,444192,77952],[84000,77952]],[[0,0,0],[0,0,0],[0,0]],[[-2937816,577584,707000],[577584,3121216,85568],[707000,85568]],[[0,0,0],[0,0,0],[0,0]],[[-16048368,16438464,2005696],[16438464,8325408,36176],[2005696,36176]],[[0,0,0],[0,0,0],[0,0]],[[15227016,81236064,2936304],[81236064,11723264,5488],[2936304,5488]],[[0,0,0],[0,0,0],[0,0]],[[440197520,208522832,2489088],[208522832,9652160,112],[2489088,112]],[[0,0,0],[0,0],[0]],[[2022319880,334596528,1264368],[334596528,4792480],[1264368]],[[0,0,0],[0,0],[0]],[[5263519520,361282544,380352],[361282544,1416352],[380352]],[[0,0,0],[0,0],[0]],[[9223280304,271596640,63168],[271596640,232288],[63168]],[[0,0,0],[0,0],[0]],[[11639366592,143997056,4704],[143997056,17248],[4704]],[[0,0,0],[0,0],[0]],[[10941030912,53682608,56],[53682608,224],[56]],[[0,0],[0]],[[7797673184,13795040],[13795040]],[[0,0],[0]],[[4246495456,2337216],[2337216]],[[0,0],[0]],[[1767118864,238224],[238224]],[[0,0],[0]],[[557678408,11760],[11760]],[[0,0],[0]],[[131262432,112],[112]],[[0]],[[22367856]],[[0]],[[2620464]],[[0]],[[191688]],[[0]],[[7056]],[[0]],[[56]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
