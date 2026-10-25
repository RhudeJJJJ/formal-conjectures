/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode035
import Proofs.RadenkovicGutmanD23Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-4761],[0,-9522],[-4761]],[[0,0,0],[0,0],[0]],[[0,-157113,-41262],[-157113,-82524],[-41262]],[[0,0,0],[0,0],[0]],[[-1285470,-1756809,-140185],[-1756809,-280370],[-140185]],[[0,0,0],[0,0],[0]],[[-17568090,-8393643,-242282],[-8393643,-484564],[-242282]],[[0,0,0],[0,0],[0]],[[-107093934,-22720550,-234876],[-22720550,-469752],[-234876]],[[0,0,0],[0,0],[0]],[[-387659664,-38999467,-132250],[-38999467,-264500],[-132250]],[[0,0,0],[0,0],[0]],[[-935587284,-44931673,-42849],[-44931673,-85698],[-42849]],[[0,0,0],[0,0],[0]],[[-1600815364,-35779444,-7406],[-35779444,-14812],[-7406]],[[0,0,0],[0,0],[0]],[[-2013588774,-19921611,-529],[-19921611,-1058],[-529]],[[0,0],[0]],[[-1903319782,-7728161],[-7728161]],[[0,0],[0]],[[-1368908112,-2045114],[-2045114]],[[0,0],[0]],[[-752966962,-351785],[-351785]],[[0,0],[0]],[[-316245722,-35443],[-35443]],[[0,0],[0]],[[-100524812,-1587],[-1587]],[[0]],[[-23747868]],[[0]],[[-4037328]],[[0]],[[-466578]],[[0]],[[-32798]],[[0]],[[-1058]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
