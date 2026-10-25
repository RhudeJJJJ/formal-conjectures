/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode073
import Proofs.RadenkovicGutmanD36Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2592,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23328,-303264,0],[-303264,-69768,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5239080,-4329288,0],[-4329288,-486288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-81661608,-26356752,0],[-26356752,-1524744,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-582316992,-90505080,0],[-90505080,-2535120,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2474680968,-195924816,0],[-195924816,-2405664,0],[0,0]],[[0,0,0],[0,0],[0]],[[-7003804248,-283636440,0],[-283636440,-1337328],[0]],[[0,0,0],[0,0],[0]],[[-14025826224,-284085792,0],[-284085792,-429768],[0]],[[0,0,0],[0,0],[0]],[[-20626053696,-200491344,0],[-200491344,-73872],[0]],[[0,0,0],[0,0],[0]],[[-22808202552,-100283328,0],[-100283328,-5256],[0]],[[0,0,0],[0,0],[0]],[[-19248881328,-35307288,0],[-35307288,0],[0]],[[0,0],[0]],[[-12500218800,-8548560],[-8548560]],[[0,0],[0]],[[-6261560928,-1354104],[-1354104]],[[0,0],[0]],[[-2411272440,-126288],[-126288]],[[0,0],[0]],[[-706701816,-5256],[-5256]],[[0,0],[0]],[[-154658160,0],[0]],[[0]],[[-24455520]],[[0]],[[-2637864]],[[0]],[[-173592]],[[0]],[[-5256]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
