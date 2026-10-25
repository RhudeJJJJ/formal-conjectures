/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode033
import Proofs.RadenkovicGutmanD26Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,676]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,16224],[0,16224,52]],[[0,0,0],[0,0,0],[0,0]],[[-54756,-36504,91260],[-36504,352872,50960],[91260,50960]],[[0,0,0],[0,0,0],[0,0]],[[-1500876,1387152,551772],[1387152,2101632,53872],[551772,53872]],[[0,0,0],[0,0,0],[0,0]],[[-6442956,13606632,1385280],[13606632,5182840,22568],[1385280,22568]],[[0,0,0],[0,0,0],[0,0]],[[15465372,54412072,1885208],[54412072,6921616,3536],[1885208,3536]],[[0,0,0],[0,0,0],[0,0]],[[221807924,125305440,1521208],[125305440,5484544,104],[1521208,104]],[[0,0,0],[0,0],[0]],[[919845108,187403632,747760],[187403632,2653040],[747760]],[[0,0,0],[0,0],[0]],[[2269414472,192567752,220896],[192567752,774072],[220896]],[[0,0,0],[0,0],[0]],[[3844961640,139715368,36712],[139715368,127920],[36712]],[[0,0,0],[0,0],[0]],[[4747959736,72273656,2860],[72273656,10088],[2860]],[[0,0,0],[0,0],[0]],[[4404593856,26539656,52],[26539656,208],[52]],[[0,0],[0]],[[3118411504,6783400],[6783400]],[[0,0],[0]],[[1696133088,1157520],[1157520]],[[0,0],[0]],[[708325956,121472],[121472]],[[0,0],[0]],[[225399252,6552],[6552]],[[0,0],[0]],[[53788488,104],[104]],[[0]],[[9363016]],[[0]],[[1134484]],[[0]],[[88036]],[[0]],[[3692]],[[0]],[[52]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
