/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode033
import Proofs.RadenkovicGutmanD19Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,361]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,8664],[0,8664,38]],[[0,0,0],[0,0,0],[0,0]],[[-29241,-19494,48735],[-19494,188442,27398],[48735,27398]],[[0,0,0],[0,0,0],[0,0]],[[-802332,740772,295488],[740772,1125636,29260],[295488,29260]],[[0,0,0],[0,0,0],[0,0]],[[-3455055,7281180,744192],[7281180,2785438,12502],[744192,12502]],[[0,0,0],[0,0,0],[0,0]],[[8214954,29176666,1016690],[29176666,3736084,2052],[1016690,2052]],[[0,0,0],[0,0,0],[0,0]],[[118659389,67343676,824638],[67343676,2977984,76],[824638,76]],[[0,0,0],[0,0],[0]],[[493208156,100984012,408386],[100984012,1453044],[408386]],[[0,0,0],[0,0],[0]],[[1219263706,104098112,122056],[104098112,429742],[122056]],[[0,0,0],[0,0],[0]],[[2070074624,75828202,20710],[75828202,72732],[20710]],[[0,0,0],[0,0],[0]],[[2562235538,39427318,1691],[39427318,6042],[1691]],[[0,0,0],[0,0],[0]],[[2383404308,14578434,38],[14578434,152],[38]],[[0,0],[0]],[[1692889056,3762760],[3762760]],[[0,0],[0]],[[924407000,651700],[651700]],[[0,0],[0]],[[387942361,70148],[70148]],[[0,0],[0]],[[124228308,3990],[3990]],[[0,0],[0]],[[29894562,76],[76]],[[0]],[[5264824]],[[0]],[[649097]],[[0]],[[51832]],[[0]],[[2299]],[[0]],[[38]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
