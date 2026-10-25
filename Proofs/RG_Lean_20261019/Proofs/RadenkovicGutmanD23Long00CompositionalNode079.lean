/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode033
import Proofs.RadenkovicGutmanD23Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1587],[0,1587]],[[0,0,0],[0,0,0],[0,0]],[[0,-14283,14283],[-14283,52371,6877],[14283,6877]],[[0,0,0],[0,0,0],[0,0]],[[-214245,157113,99981],[157113,358662,8464],[99981,8464]],[[0,0,0],[0,0,0],[0,0]],[[-1356885,2209104,276138],[2209104,964367,3703],[276138,3703]],[[0,0,0],[0,0,0],[0,0]],[[742716,9997571,400453],[9997571,1359530,529],[400453,529]],[[0,0,0],[0,0],[0]],[[34947327,24754026,336444],[24754026,1110900],[336444]],[[0,0,0],[0,0],[0]],[[166121341,38887319,168751],[38887319,542754],[168751]],[[0,0,0],[0,0],[0]],[[439688930,41375206,49726],[41375206,156055],[49726]],[[0,0,0],[0,0],[0]],[[780454860,30750241,7935],[30750241,24334],[7935]],[[0,0,0],[0,0],[0]],[[996781475,16138203,529],[16138203,1587],[529]],[[0,0],[0]],[[948126700,5951250],[5951250]],[[0,0],[0]],[[683597076,1507650],[1507650]],[[0,0],[0]],[[376347528,249688],[249688]],[[0,0],[0]],[[158110165,24334],[24334]],[[0,0],[0]],[[50261877,1058],[1058]],[[0]],[[11873934]],[[0]],[[2018664]],[[0]],[[233289]],[[0]],[[16399]],[[0]],[[529]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
