/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode093
import Proofs.RadenkovicGutmanD31Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,961]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-8649],[0,-17298,28458],[-8649,28458,62]],[[0,0,0],[0,0,0],[0,0]],[[-77841,-288765,103323],[-288765,545910,95604],[103323,95604]],[[0,0,0],[0,0,0],[0,0]],[[-3594078,722331,868589],[722331,3833770,104780],[868589,104780]],[[0,0,0],[0,0,0],[0,0]],[[-19502937,20259585,2462578],[20259585,10221258,44144],[2462578,44144]],[[0,0,0],[0,0,0],[0,0]],[[20116644,99972024,3602820],[99972024,14384372,6634],[3602820,6634]],[[0,0,0],[0,0,0],[0,0]],[[546355997,256428125,3051516],[256428125,11833196,124],[3051516,124]],[[0,0,0],[0,0],[0]],[[2498976836,411229539,1548171],[411229539,5867866],[1548171]],[[0,0,0],[0,0],[0]],[[6492760838,443775416,464814],[443775416,1730482],[464814]],[[0,0,0],[0,0],[0]],[[11365451322,333397405,76911],[333397405,282658],[76911]],[[0,0,0],[0,0],[0]],[[14331590160,176623523,5673],[176623523,20770],[5673]],[[0,0,0],[0,0],[0]],[[13462702320,65777102,62],[65777102,248],[62]],[[0,0],[0]],[[9588647138,16877795],[16877795]],[[0,0],[0]],[[5218256350,2852775],[2852775]],[[0,0],[0]],[[2169813349,289509],[289509]],[[0,0],[0]],[[684116060,14136],[14136]],[[0,0],[0]],[[160824714,124],[124]],[[0]],[[27358182]],[[0]],[[3196503]],[[0]],[[232686]],[[0]],[[8463]],[[0]],[[62]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
