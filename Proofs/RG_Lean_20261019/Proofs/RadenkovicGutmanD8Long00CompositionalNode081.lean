/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode079
import Proofs.RadenkovicGutmanD8Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-3456,0],[-3456,-576,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-57024,-50112,0],[-50112,-4992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-931392,-308736,0],[-308736,-16960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6766848,-1069760,0],[-1069760,-29312,0],[0,0]],[[0,0,0],[0,0],[0]],[[-29071680,-2331648,0],[-2331648,-28416],[0]],[[0,0,0],[0,0],[0]],[[-82888256,-3393088,0],[-3393088,-16000],[0]],[[0,0,0],[0,0],[0]],[[-166897536,-3412224,0],[-3412224,-5184],[0]],[[0,0,0],[0,0],[0]],[[-246471424,-2415872,0],[-2415872,-896],[0]],[[0,0,0],[0,0],[0]],[[-273468096,-1211520,0],[-1211520,-64],[0]],[[0,0],[0]],[[-231432576,-427456],[-427456]],[[0,0],[0]],[[-150641280,-103680],[-103680]],[[0,0],[0]],[[-75607552,-16448],[-16448]],[[0,0],[0]],[[-29165248,-1536],[-1536]],[[0,0],[0]],[[-8560448,-64],[-64]],[[0]],[[-1875840]],[[0]],[[-296960]],[[0]],[[-32064]],[[0]],[[-2112]],[[0]],[[-64]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
