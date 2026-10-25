/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode073
import Proofs.RadenkovicGutmanD15Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1080,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9720,-58320,0],[-58320,-17730,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1060290,-817290,0],[-817290,-104340,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15688890,-4903740,0],[-4903740,-301410,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-109409760,-16649550,0],[-16649550,-479220,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-458768370,-35731020,0],[-35731020,-442920,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1286389230,-51380430,0],[-51380430,-242220],[0]],[[0,0,0],[0,0],[0]],[[-2558299020,-51190920,0],[-51190920,-77010],[0]],[[0,0,0],[0,0],[0]],[[-3741782880,-35975580,0],[-35975580,-13140],[0]],[[0,0,0],[0,0],[0]],[[-4119514590,-17932920,0],[-17932920,-930],[0]],[[0,0,0],[0,0],[0]],[[-3464038380,-6295830,0],[-6295830,0],[0]],[[0,0],[0]],[[-2242674300,-1520700],[-1520700]],[[0,0],[0]],[[-1120460040,-240390],[-240390]],[[0,0],[0]],[[-430506030,-22380],[-22380]],[[0,0],[0]],[[-125925270,-930],[-930]],[[0,0],[0]],[[-27510300,0],[0]],[[0]],[[-4343400]],[[0]],[[-467850]],[[0]],[[-30750]],[[0]],[[-930]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
