/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode096
import Proofs.RadenkovicGutmanD39Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,9126],[0,9126,-2886]],[[0,0,0],[0,0,0],[0,0]],[[0,0,109512],[0,372411,-12168],[109512,-12168]],[[0,0,0],[0,0,0],[0,0]],[[382239,3025269,580554],[3025269,1752660,-88842],[580554,-88842]],[[0,0,0],[0,0,0],[0,0]],[[26473473,26299728,1162044],[26299728,2709447,-104442],[1162044,-104442]],[[0,0,0],[0,0,0],[0,0]],[[285843168,99539739,931554],[99539739,365352,-42588],[931554,-42588]],[[0,0,0],[0,0,0],[0,0]],[[1490960367,214049706,-118794],[214049706,-3748992,-5694],[-118794,-5694]],[[0,0,0],[0,0],[0]],[[4746032499,285167805,-776490],[285167805,-4963842],[-776490]],[[0,0,0],[0,0],[0]],[[10182637140,237347604,-597168],[237347604,-2998905],[-597168]],[[0,0,0],[0,0],[0]],[[15494911380,111387666,-216138],[111387666,-972972],[-216138]],[[0,0,0],[0,0],[0]],[[17168075301,11100648,-38922],[11100648,-164073],[-38922]],[[0,0,0],[0,0],[0]],[[13976466036,-21223293,-2808],[-21223293,-11310],[-2808]],[[0,0],[0]],[[8287172322,-15247284],[-15247284]],[[0,0],[0]],[[3440593884,-5296629],[-5296629]],[[0,0],[0]],[[875774913,-1061970],[-1061970]],[[0,0],[0]],[[46921251,-117741],[-117741]],[[0,0],[0]],[[-63253476,-5616],[-5616]],[[0]],[[-29324880]],[[0]],[[-6915909]],[[0]],[[-977457]],[[0]],[[-78819]],[[0]],[[-2808]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
