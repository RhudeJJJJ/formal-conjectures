/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode033
import Proofs.RadenkovicGutmanD12Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,432],[0,432,-240]],[[0,0,0],[0,0,0],[0,0]],[[0,-3888,3888],[-3888,14256,-2448],[3888,-2448]],[[0,0,0],[0,0,0],[0,0]],[[-38880,42768,7776],[42768,19872,-9216],[7776,-9216]],[[0,0,0],[0,0,0],[0,0]],[[-32400,251424,-28512],[251424,-152208,-9552],[-28512,-9552]],[[0,0,0],[0,0,0],[0,0]],[[1232496,-77904,-124272],[-77904,-563040,-3696],[-124272,-3696]],[[0,0,0],[0,0,0],[0,0]],[[4617072,-3292704,-196416],[-3292704,-849600,-480],[-196416,-480]],[[0,0,0],[0,0],[0]],[[-1441344,-10668816,-166704],[-10668816,-702816],[-166704]],[[0,0,0],[0,0],[0]],[[-52560480,-18350784,-82464],[-18350784,-341520],[-82464]],[[0,0,0],[0,0],[0]],[[-181048800,-20175984,-23760],[-20175984,-97056],[-23760]],[[0,0,0],[0,0],[0]],[[-355307280,-15112272,-3696],[-15112272,-14928],[-3696]],[[0,0,0],[0,0],[0]],[[-474919680,-7895520,-240],[-7895520,-960],[-240]],[[0,0],[0]],[[-460988544,-2880000],[-2880000]],[[0,0],[0]],[[-334630272,-719232],[-719232]],[[0,0],[0]],[[-184029360,-117216],[-117216]],[[0,0],[0]],[[-76863168,-11232],[-11232]],[[0,0],[0]],[[-24219936,-480],[-480]],[[0]],[[-5661216]],[[0]],[[-951216]],[[0]],[[-108576]],[[0]],[[-7536]],[[0]],[[-240]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
