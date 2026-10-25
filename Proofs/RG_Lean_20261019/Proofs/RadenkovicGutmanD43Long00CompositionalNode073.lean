/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode071
import Proofs.RadenkovicGutmanD43Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-99846,0],[-99846,-19737,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1675323,-1875015,0],[-1875015,-238392,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34239051,-15033402,0],[-15033402,-1164741,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-310560534,-68195807,0],[-68195807,-2987124,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1662745629,-195590918,0],[-195590918,-4400448,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5897473435,-375913869,0],[-375913869,-3870258,0],[0,0]],[[0,0,0],[0,0],[0]],[[-14746764516,-501201722,0],[-501201722,-2048133],[0]],[[0,0,0],[0,0],[0]],[[-27013543592,-473313212,0],[-473313212,-636744],[0]],[[0,0,0],[0,0],[0]],[[-37174083123,-319925934,0],[-319925934,-106941],[0]],[[0,0,0],[0,0],[0]],[[-39073981148,-154924055,0],[-154924055,-7482],[0]],[[0,0,0],[0,0],[0]],[[-31697665430,-53209490,0],[-53209490,0],[0]],[[0,0],[0]],[[-19949105412,-12636453],[-12636453]],[[0,0],[0]],[[-9744055979,-1971206],[-1971206]],[[0,0],[0]],[[-3676118891,-181589],[-181589]],[[0,0],[0]],[[-1059353676,-7482],[-7482]],[[0,0],[0]],[[-228599180,0],[0]],[[0]],[[-35723669]],[[0]],[[-3815003]],[[0]],[[-248927]],[[0]],[[-7482]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
