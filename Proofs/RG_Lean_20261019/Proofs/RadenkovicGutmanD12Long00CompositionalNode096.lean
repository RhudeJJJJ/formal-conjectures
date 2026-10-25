/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode043
import Proofs.RadenkovicGutmanD12Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,432],[0,432,-240]],[[0,0,0],[0,0,0],[0,0]],[[0,3888,3888],[3888,16416,-2448],[3888,-2448]],[[0,0,0],[0,0,0],[0,0]],[[97200,163296,7776],[163296,38592,-9216],[7776,-9216]],[[0,0,0],[0,0,0],[0,0]],[[2268000,1034208,-28512],[1034208,-88608,-9552],[-28512,-9552]],[[0,0,0],[0,0,0],[0,0]],[[18479664,2756736,-124272],[2756736,-453120,-3696],[-124272,-3696]],[[0,0,0],[0,0,0],[0,0]],[[80923680,3131424,-196416],[3131424,-743040,-480],[-196416,-480]],[[0,0,0],[0,0],[0]],[[222291696,-975072,-166704],[-975072,-642816],[-166704]],[[0,0,0],[0,0],[0]],[[410268864,-8256000,-82464],[-8256000,-322080],[-82464]],[[0,0,0],[0,0],[0]],[[520726368,-12779376,-23760],[-12779376,-93696],[-23760]],[[0,0,0],[0,0],[0]],[[443815104,-11274672,-3696],[-11274672,-14688],[-3696]],[[0,0,0],[0,0],[0]],[[218944416,-6494928,-240],[-6494928,-960],[-240]],[[0,0],[0]],[[2283360,-2528640],[-2528640]],[[0,0],[0]],[[-96170496,-661584],[-661584]],[[0,0],[0]],[[-89710176,-111648],[-111648]],[[0,0],[0]],[[-48480720,-10992],[-10992]],[[0,0],[0]],[[-17844480,-480],[-480]],[[0]],[[-4626720]],[[0]],[[-836736]],[[0]],[[-100848]],[[0]],[[-7296]],[[0]],[[-240]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
