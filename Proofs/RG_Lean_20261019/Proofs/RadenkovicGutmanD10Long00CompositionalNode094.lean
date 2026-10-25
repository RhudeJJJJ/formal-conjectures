/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode035
import Proofs.RadenkovicGutmanD10Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-900],[0,-1800,480],[-900,480]],[[0,0,0],[0,0,0],[0,0]],[[0,-25380,-3480],[-25380,1680,2080],[-3480,2080]],[[0,0,0],[0,0,0],[0,0]],[[-165240,-159300,3740],[-159300,67960,2560],[3740,2560]],[[0,0,0],[0,0,0],[0,0]],[[-1402920,-146700,37720],[-146700,242480,1120],[37720,1120]],[[0,0,0],[0,0,0],[0,0]],[[-3102840,1403240,76720],[1403240,395680,160],[76720,160]],[[0,0,0],[0,0],[0]],[[9967680,5943860,76760],[5943860,357040],[76760]],[[0,0,0],[0,0],[0]],[[80605680,11750780,42940],[11750780,187960],[42940]],[[0,0,0],[0,0],[0]],[[247619440,14281200,13640],[14281200,57360],[13640]],[[0,0,0],[0,0],[0]],[[471592360,11574420,2300],[11574420,9400],[2300]],[[0,0,0],[0,0],[0]],[[625358440,6449020,160],[6449020,640],[160]],[[0,0],[0]],[[606576640,2482040],[2482040]],[[0,0],[0]],[[441024440,648700],[648700]],[[0,0],[0]],[[243066200,109940],[109940]],[[0,0],[0]],[[101731920,10900],[10900]],[[0,0],[0]],[[32114000,480],[480]],[[0]],[[7517760]],[[0]],[[1264760]],[[0]],[[144520]],[[0]],[[10040]],[[0]],[[320]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
