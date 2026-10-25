/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode033
import Proofs.RadenkovicGutmanD36Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3888],[0,3888]],[[0,0,0],[0,0,0],[0,0]],[[0,-34992,34992],[-34992,128304,16848],[34992,16848]],[[0,0,0],[0,0,0],[0,0]],[[-524880,384912,244944],[384912,878688,20736],[244944,20736]],[[0,0,0],[0,0,0],[0,0]],[[-3324240,5412096,676512],[5412096,2362608,9072],[676512,9072]],[[0,0,0],[0,0,0],[0,0]],[[1819584,24493104,981072],[24493104,3330720,1296],[981072,1296]],[[0,0,0],[0,0],[0]],[[85617648,60645024,824256],[60645024,2721600],[824256]],[[0,0,0],[0,0],[0]],[[406981584,95270256,413424],[95270256,1329696],[413424]],[[0,0,0],[0,0],[0]],[[1077196320,101365344,121824],[101365344,382320],[121824]],[[0,0,0],[0,0],[0]],[[1912040640,75335184,19440],[75335184,59616],[19440]],[[0,0,0],[0,0],[0]],[[2442020400,39537072,1296],[39537072,3888],[1296]],[[0,0],[0]],[[2322820800,14580000],[14580000]],[[0,0],[0]],[[1674748224,3693600],[3693600]],[[0,0],[0]],[[922015872,611712],[611712]],[[0,0],[0]],[[387354960,59616],[59616]],[[0,0],[0]],[[123136848,2592],[2592]],[[0]],[[29090016]],[[0]],[[4945536]],[[0]],[[571536]],[[0]],[[40176]],[[0]],[[1296]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
