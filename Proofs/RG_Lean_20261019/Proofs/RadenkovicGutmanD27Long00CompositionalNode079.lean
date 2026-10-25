/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode033
import Proofs.RadenkovicGutmanD27Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2187],[0,2187]],[[0,0,0],[0,0,0],[0,0]],[[0,-19683,19683],[-19683,72171,9477],[19683,9477]],[[0,0,0],[0,0,0],[0,0]],[[-295245,216513,137781],[216513,494262,11664],[137781,11664]],[[0,0,0],[0,0,0],[0,0]],[[-1869885,3044304,380538],[3044304,1328967,5103],[380538,5103]],[[0,0,0],[0,0,0],[0,0]],[[1023516,13777371,551853],[13777371,1873530,729],[551853,729]],[[0,0,0],[0,0],[0]],[[48159927,34112826,463644],[34112826,1530900],[463644]],[[0,0,0],[0,0],[0]],[[228927141,53589519,232551],[53589519,747954],[232551]],[[0,0,0],[0,0],[0]],[[605922930,57018006,68526],[57018006,215055],[68526]],[[0,0,0],[0,0],[0]],[[1075522860,42376041,10935],[42376041,33534],[10935]],[[0,0,0],[0,0],[0]],[[1373636475,22239603,729],[22239603,2187],[729]],[[0,0],[0]],[[1306586700,8201250],[8201250]],[[0,0],[0]],[[942045876,2077650],[2077650]],[[0,0],[0]],[[518633928,344088],[344088]],[[0,0],[0]],[[217887165,33534],[33534]],[[0,0],[0]],[[69264477,1458],[1458]],[[0]],[[16363134]],[[0]],[[2781864]],[[0]],[[321489]],[[0]],[[22599]],[[0]],[[729]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
