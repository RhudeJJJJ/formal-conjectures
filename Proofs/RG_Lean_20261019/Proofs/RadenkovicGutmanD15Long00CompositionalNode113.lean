/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,225]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-4050,4050],[0,4050]],[[0,0,0],[0,0,0],[0,0]],[[18225,-36450,18225],[-36450,37800,10800],[18225,10800]],[[0,0,0],[0,0,0],[0,0]],[[-12150,-85050,97200],[-85050,269550,9900],[97200,9900]],[[0,0,0],[0,0,0],[0,0]],[[-674325,619650,218700],[619650,668700,3600],[218700,3600]],[[0,0,0],[0,0,0],[0,0]],[[-1856250,3882600,270000],[3882600,880200,450],[270000,450]],[[0,0,0],[0,0],[0]],[[3907125,10273050,199350],[10273050,684900],[199350]],[[0,0,0],[0,0],[0]],[[37071900,16431750,90000],[16431750,323550],[90000]],[[0,0,0],[0,0],[0]],[[115824150,17570700,24300],[17570700,90900],[24300]],[[0,0,0],[0,0],[0]],[[222708150,13075200,3600],[13075200,13950],[3600]],[[0,0,0],[0,0],[0]],[[299741400,6863850,225],[6863850,900],[225]],[[0,0],[0]],[[297232200,2531250],[2531250]],[[0,0],[0]],[[222406200,641250],[641250]],[[0,0],[0]],[[126821250,106200],[106200]],[[0,0],[0]],[[55133325,10350],[10350]],[[0,0],[0]],[[18126900,450],[450]],[[0]],[[4427550]],[[0]],[[778050]],[[0]],[[92925]],[[0]],[[6750]],[[0]],[[225]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
