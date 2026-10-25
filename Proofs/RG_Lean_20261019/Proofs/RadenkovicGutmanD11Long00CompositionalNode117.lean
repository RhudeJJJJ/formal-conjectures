/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode112
import Proofs.RadenkovicGutmanD11Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,264],[0,264,368]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2376,6732],[2376,9792,8032],[6732,8032,4]],[[0,0,0],[0,0,0],[0,0]],[[93960,178416,86568],[178416,197832,20288],[86568,20288]],[[0,0,0],[0,0,0],[0,0]],[[2714364,2342232,350128],[2342232,896576,18408],[350128,18408]],[[0,0,0],[0,0,0],[0,0]],[[29974536,12686560,693648],[12686560,1904680,6768],[693648,6768]],[[0,0,0],[0,0,0],[0,0]],[[176366580,38191144,782968],[38191144,2290160,888],[782968,888]],[[0,0,0],[0,0,0],[0,0]],[[647789216,72764776,535888],[72764776,1671104,8],[535888,8]],[[0,0,0],[0,0],[0]],[[1621706612,93822472,226292],[93822472,752944],[226292]],[[0,0,0],[0,0],[0]],[[2918349072,84904208,57712],[84904208,204840],[57712]],[[0,0,0],[0,0],[0]],[[3905024544,54914912,8212],[54914912,31056],[8212]],[[0,0,0],[0,0],[0]],[[3971039352,25507400,520],[25507400,2088],[520]],[[0,0,0],[0,0],[0]],[[3110707248,8441552,4],[8441552,16],[4]],[[0,0],[0]],[[1890648848,1944232],[1944232]],[[0,0],[0]],[[893053496,297040],[297040]],[[0,0],[0]],[[326562512,27328],[27328]],[[0,0],[0]],[[91494804,1200],[1200]],[[0,0],[0]],[[19274864,8],[8]],[[0]],[[2957968]],[[0]],[[313296]],[[0]],[[20716]],[[0]],[[680]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
