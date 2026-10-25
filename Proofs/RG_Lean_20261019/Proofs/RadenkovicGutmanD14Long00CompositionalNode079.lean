/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode033
import Proofs.RadenkovicGutmanD14Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,588],[0,588]],[[0,0,0],[0,0,0],[0,0]],[[0,-5292,5292],[-5292,19404,2548],[5292,2548]],[[0,0,0],[0,0,0],[0,0]],[[-79380,58212,37044],[58212,132888,3136],[37044,3136]],[[0,0,0],[0,0,0],[0,0]],[[-502740,818496,102312],[818496,357308,1372],[102312,1372]],[[0,0,0],[0,0,0],[0,0]],[[275184,3704204,148372],[3704204,503720,196],[148372,196]],[[0,0,0],[0,0],[0]],[[12948348,9171624,124656],[9171624,411600],[124656]],[[0,0,0],[0,0],[0]],[[61549684,14408156,62524],[14408156,201096],[62524]],[[0,0,0],[0,0],[0]],[[162909320,15329944,18424],[15329944,57820],[18424]],[[0,0,0],[0,0],[0]],[[289166640,11393284,2940],[11393284,9016],[2940]],[[0,0,0],[0,0],[0]],[[369317900,5979372,196],[5979372,588],[196]],[[0,0],[0]],[[351290800,2205000],[2205000]],[[0,0],[0]],[[253279824,558600],[558600]],[[0,0],[0]],[[139440672,92512],[92512]],[[0,0],[0]],[[58581460,9016],[9016]],[[0,0],[0]],[[18622548,392],[392]],[[0]],[[4399416]],[[0]],[[747936]],[[0]],[[86436]],[[0]],[[6076]],[[0]],[[196]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
