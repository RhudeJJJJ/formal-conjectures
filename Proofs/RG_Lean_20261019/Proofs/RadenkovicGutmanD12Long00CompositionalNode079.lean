/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode033
import Proofs.RadenkovicGutmanD12Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,432],[0,432]],[[0,0,0],[0,0,0],[0,0]],[[0,-3888,3888],[-3888,14256,1872],[3888,1872]],[[0,0,0],[0,0,0],[0,0]],[[-58320,42768,27216],[42768,97632,2304],[27216,2304]],[[0,0,0],[0,0,0],[0,0]],[[-369360,601344,75168],[601344,262512,1008],[75168,1008]],[[0,0,0],[0,0,0],[0,0]],[[202176,2721456,109008],[2721456,370080,144],[109008,144]],[[0,0,0],[0,0],[0]],[[9513072,6738336,91584],[6738336,302400],[91584]],[[0,0,0],[0,0],[0]],[[45220176,10585584,45936],[10585584,147744],[45936]],[[0,0,0],[0,0],[0]],[[119688480,11262816,13536],[11262816,42480],[13536]],[[0,0,0],[0,0],[0]],[[212448960,8370576,2160],[8370576,6624],[2160]],[[0,0,0],[0,0],[0]],[[271335600,4393008,144],[4393008,432],[144]],[[0,0],[0]],[[258091200,1620000],[1620000]],[[0,0],[0]],[[186083136,410400],[410400]],[[0,0],[0]],[[102446208,67968],[67968]],[[0,0],[0]],[[43039440,6624],[6624]],[[0,0],[0]],[[13681872,288],[288]],[[0]],[[3232224]],[[0]],[[549504]],[[0]],[[63504]],[[0]],[[4464]],[[0]],[[144]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
