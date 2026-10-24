/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode042
import Proofs.RadenkovicGutmanD4Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .times e042 e052
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,48],[0,48,-16]],[[0,0,0],[0,0,0],[0,0]],[[0,432,432],[432,2016,-80],[432,-80]],[[0,0,0],[0,0,0],[0,0]],[[11664,19872,1728],[19872,9408,-512],[1728,-512]],[[0,0,0],[0,0,0],[0,0]],[[282528,150048,1440],[150048,14240,-592],[1440,-592]],[[0,0,0],[0,0,0],[0,0]],[[2456784,525760,-3440],[525760,896,-240],[-3440,-240]],[[0,0,0],[0,0,0],[0,0]],[[11630304,1055520,-9024],[1055520,-21888,-32],[-9024,-32]],[[0,0,0],[0,0],[0]],[[35047248,1293920,-9072],[1293920,-28288],[-9072]],[[0,0,0],[0,0],[0]],[[72643136,936000,-4896],[936000,-16992],[-4896]],[[0,0,0],[0,0],[0]],[[108061600,284560,-1488],[284560,-5504],[-1488]],[[0,0,0],[0,0],[0]],[[118012288,-138800,-240],[-138800,-928],[-240]],[[0,0,0],[0,0],[0]],[[95381152,-201232,-16],[-201232,-64],[-16]],[[0,0],[0]],[[56641120,-108480],[-108480]],[[0,0],[0]],[[23927296,-33936],[-33936]],[[0,0],[0]],[[6501344,-6432],[-6432]],[[0,0],[0]],[[664464,-688],[-688]],[[0,0],[0]],[[-283776,-32],[-32]],[[0]],[[-156640]],[[0]],[[-38464]],[[0]],[[-5520]],[[0]],[[-448]],[[0]],[[-16]]]
theorem step095 : p095=NestedArithmetic.mul p042 p052 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_times e095 e042 e052 p042 p052 p095 rfl h042 h052 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
