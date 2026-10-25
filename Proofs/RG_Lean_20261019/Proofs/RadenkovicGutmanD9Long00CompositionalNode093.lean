/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode033
import Proofs.RadenkovicGutmanD9Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,81]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,1944],[0,1944,18]],[[0,0,0],[0,0,0],[0,0]],[[-6561,-4374,10935],[-4374,42282,6318],[10935,6318]],[[0,0,0],[0,0,0],[0,0]],[[-180792,166212,67068],[166212,255636,7020],[67068,7020]],[[0,0,0],[0,0,0],[0,0]],[[-788535,1647540,171072],[1647540,641358,3222],[171072,3222]],[[0,0,0],[0,0,0],[0,0]],[[1802574,6657066,237330],[6657066,875124,612],[237330,612]],[[0,0,0],[0,0,0],[0,0]],[[26817669,15506316,196398],[15506316,713664,36],[196398,36]],[[0,0,0],[0,0],[0]],[[112506336,23497452,100026],[23497452,359604],[100026]],[[0,0,0],[0,0],[0]],[[280373706,24526152,31176],[24526152,111582],[31176]],[[0,0,0],[0,0],[0]],[[480009384,18140922,5670],[18140922,20412],[5670]],[[0,0,0],[0,0],[0]],[[599641938,9616518,531],[9616518,1962],[531]],[[0,0,0],[0,0],[0]],[[563715108,3646674,18],[3646674,72],[18]],[[0,0],[0]],[[405387216,974160],[974160]],[[0,0],[0]],[[224668440,177300],[177300]],[[0,0],[0]],[[96008481,20628],[20628]],[[0,0],[0]],[[31448088,1350],[1350]],[[0,0],[0]],[[7791282,36],[36]],[[0]],[[1426464]],[[0]],[[185697]],[[0]],[[16092]],[[0]],[[819]],[[0]],[[18]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
