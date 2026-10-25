/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode033
import Proofs.RadenkovicGutmanD8Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,192],[0,192]],[[0,0,0],[0,0,0],[0,0]],[[0,-1728,1728],[-1728,6336,832],[1728,832]],[[0,0,0],[0,0,0],[0,0]],[[-25920,19008,12096],[19008,43392,1024],[12096,1024]],[[0,0,0],[0,0,0],[0,0]],[[-164160,267264,33408],[267264,116672,448],[33408,448]],[[0,0,0],[0,0,0],[0,0]],[[89856,1209536,48448],[1209536,164480,64],[48448,64]],[[0,0,0],[0,0],[0]],[[4228032,2994816,40704],[2994816,134400],[40704]],[[0,0,0],[0,0],[0]],[[20097856,4704704,20416],[4704704,65664],[20416]],[[0,0,0],[0,0],[0]],[[53194880,5005696,6016],[5005696,18880],[6016]],[[0,0,0],[0,0],[0]],[[94421760,3720256,960],[3720256,2944],[960]],[[0,0,0],[0,0],[0]],[[120593600,1952448,64],[1952448,192],[64]],[[0,0],[0]],[[114707200,720000],[720000]],[[0,0],[0]],[[82703616,182400],[182400]],[[0,0],[0]],[[45531648,30208],[30208]],[[0,0],[0]],[[19128640,2944],[2944]],[[0,0],[0]],[[6080832,128],[128]],[[0]],[[1436544]],[[0]],[[244224]],[[0]],[[28224]],[[0]],[[1984]],[[0]],[[64]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
