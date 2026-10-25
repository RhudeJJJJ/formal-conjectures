/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode035
import Proofs.RadenkovicGutmanD26Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-6084],[0,-12168,3744],[-6084,3744]],[[0,0,0],[0,0,0],[0,0]],[[0,-167076,-19032],[-167076,29328,16224],[-19032,16224]],[[0,0,0],[0,0,0],[0,0]],[[-1036152,-897156,56732],[-897156,585208,19968],[56732,19968]],[[0,0,0],[0,0,0],[0,0]],[[-7488936,505908,341848],[505908,1986608,8736],[341848,8736]],[[0,0,0],[0,0,0],[0,0]],[[-3147768,15412072,644592],[15412072,3178656,1248],[644592,1248]],[[0,0,0],[0,0],[0]],[[153960768,54029300,624728],[54029300,2836912],[624728]],[[0,0,0],[0,0],[0]],[[812658288,100489532,343356],[100489532,1482936],[343356]],[[0,0,0],[0,0],[0]],[[2246147696,118427504,107848],[118427504,450320],[107848]],[[0,0,0],[0,0],[0]],[[4074286632,94197012,18044],[94197012,73528],[18044]],[[0,0,0],[0,0],[0]],[[5251983464,51821692,1248],[51821692,4992],[1248]],[[0,0],[0]],[[5000421504,19761976],[19761976]],[[0,0],[0]],[[3588021944,5129020],[5129020]],[[0,0],[0]],[[1958089432,864500],[864500]],[[0,0],[0]],[[813271888,85332],[85332]],[[0,0],[0]],[[255157968,3744],[3744]],[[0]],[[59432256]],[[0]],[[9956856]],[[0]],[[1133704]],[[0]],[[78520]],[[0]],[[2496]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
