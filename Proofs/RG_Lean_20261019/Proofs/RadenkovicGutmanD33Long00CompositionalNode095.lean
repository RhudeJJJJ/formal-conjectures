/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode093
import Proofs.RadenkovicGutmanD33Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-9801],[0,-19602,32274],[-9801,32274,66]],[[0,0,0],[0,0,0],[0,0]],[[-88209,-326997,117315],[-326997,619542,108372],[117315,108372]],[[0,0,0],[0,0,0],[0,0]],[[-4068306,827739,985545],[827739,4349466,118668],[985545,118668]],[[0,0,0],[0,0,0],[0,0]],[[-21992553,23028489,2793186],[23028489,11593098,49896],[2793186,49896]],[[0,0,0],[0,0,0],[0,0]],[[23726736,113541384,4085004],[113541384,16309524,7458],[4085004,7458]],[[0,0,0],[0,0,0],[0,0]],[[623471805,291113757,3458268],[291113757,13410540,132],[3458268,132]],[[0,0,0],[0,0],[0]],[[2844702960,466703523,1753323],[466703523,6645210],[1753323]],[[0,0,0],[0,0],[0]],[[7383791910,503478624,525822],[503478624,1957362],[525822]],[[0,0,0],[0,0],[0]],[[12917647314,378114165,86823],[378114165,318978],[86823]],[[0,0,0],[0,0],[0]],[[16281798192,200223771,6369],[200223771,23298],[6369]],[[0,0,0],[0,0],[0]],[[15288915312,74522118,66],[74522118,264],[66]],[[0,0],[0]],[[10885372674,19105515],[19105515]],[[0,0],[0]],[[5921664606,3224991],[3224991]],[[0,0],[0]],[[2461218309,326469],[326469]],[[0,0],[0]],[[775578408,15840],[15840]],[[0,0],[0]],[[182199402,132],[132]],[[0]],[[30963966]],[[0]],[[3612279]],[[0]],[[262218]],[[0]],[[9471]],[[0]],[[66]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
