/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode033
import Proofs.RadenkovicGutmanD43Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5547],[0,5547]],[[0,0,0],[0,0,0],[0,0]],[[0,-49923,49923],[-49923,183051,24037],[49923,24037]],[[0,0,0],[0,0,0],[0,0]],[[-748845,549153,349461],[549153,1253622,29584],[349461,29584]],[[0,0,0],[0,0,0],[0,0]],[[-4742685,7721424,965178],[7721424,3370727,12943],[965178,12943]],[[0,0,0],[0,0,0],[0,0]],[[2595996,34944251,1399693],[34944251,4751930,1849],[1399693,1849]],[[0,0,0],[0,0],[0]],[[122150487,86522106,1175964],[86522106,3882900],[1175964]],[[0,0,0],[0,0],[0]],[[580639621,135921839,589831],[135921839,1897074],[589831]],[[0,0,0],[0,0],[0]],[[1536833330,144617686,173806],[144617686,545455],[173806]],[[0,0,0],[0,0],[0]],[[2727903660,107480521,27735],[107480521,85054],[27735]],[[0,0,0],[0,0],[0]],[[3484024475,56407443,1849],[56407443,5547],[1849]],[[0,0],[0]],[[3313962700,20801250],[20801250]],[[0,0],[0]],[[2389359156,5269650],[5269650]],[[0,0],[0]],[[1315437768,872728],[872728]],[[0,0],[0]],[[552638365,85054],[85054]],[[0,0],[0]],[[175679037,3698],[3698]],[[0]],[[41502654]],[[0]],[[7055784]],[[0]],[[815409]],[[0]],[[57319]],[[0]],[[1849]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
