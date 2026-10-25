/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode043
import Proofs.RadenkovicGutmanD27Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-6561],[0,-13122,4050],[-6561,4050]],[[0,0,0],[0,0,0],[0,0]],[[0,-258795,-20412],[-258795,19926,17550],[-20412,17550]],[[0,0,0],[0,0,0],[0,0]],[[-2405700,-2095875,61965],[-2095875,528930,21600],[61965,21600]],[[0,0,0],[0,0,0],[0,0]],[[-29014200,-6351291,370818],[-6351291,1793286,9450],[370818,9450]],[[0,0,0],[0,0,0],[0,0]],[[-154832310,-7120980,698274],[-7120980,2822148,1350],[698274,1350]],[[0,0,0],[0,0],[0]],[[-481839030,6818337,676350],[6818337,2470500],[676350]],[[0,0,0],[0,0],[0]],[[-963352494,33911649,371601],[33911649,1267002],[371601]],[[0,0,0],[0,0],[0]],[[-1267375032,53243568,116694],[53243568,377838],[116694]],[[0,0,0],[0,0],[0]],[[-1033465230,49149963,19521],[49149963,60642],[19521]],[[0,0,0],[0,0],[0]],[[-333820980,29740689,1350],[29740689,4050],[1350]],[[0,0],[0]],[[337392216,12141522],[12141522]],[[0,0],[0]],[[592549830,3320595],[3320595]],[[0,0],[0]],[[473921766,583821],[583821]],[[0,0],[0]],[[248032530,59697],[59697]],[[0,0],[0]],[[91357146,2700],[2700]],[[0]],[[23997060]],[[0]],[[4419630]],[[0]],[[543672]],[[0]],[[40176]],[[0]],[[1350]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
