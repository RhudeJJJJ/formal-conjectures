/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,324],[0,648,-288],[324,-288,64]],[[0,0,0],[0,0,0],[0,0]],[[0,16848,216],[16848,-7056,-96],[216,-96]],[[0,0,0],[0,0,0],[0,0]],[[219024,108864,-3420],[108864,-52728,1536],[-3420,1536]],[[0,0,0],[0,0,0],[0,0]],[[2684448,198288,-5976],[198288,-124720,2144],[-5976,2144]],[[0,0,0],[0,0,0],[0,0]],[[14822352,-280608,5520],[-280608,-127136,928],[5520,928]],[[0,0,0],[0,0,0],[0,0]],[[48510624,-1887600,24744],[-1887600,-32688,128],[24744,128]],[[0,0,0],[0,0],[0]],[[104017696,-3798880,28996],[-3798880,46152],[28996]],[[0,0,0],[0,0],[0]],[[151885792,-4183072,17080],[-4183072,46576],[17080]],[[0,0,0],[0,0],[0]],[[150495856,-2658944,5508],[-2658944,18376],[5508]],[[0,0,0],[0,0],[0]],[[94258336,-792400,928],[-792400,3456],[928]],[[0,0,0],[0,0],[0]],[[25489120,126784,64],[126784,256],[64]],[[0,0],[0]],[[-12867040,220560],[220560]],[[0,0],[0]],[[-16824080,94112],[94112]],[[0,0],[0]],[[-7713568,21104],[21104]],[[0,0],[0]],[[-1244000,2528],[2528]],[[0,0],[0]],[[483744,128],[128]],[[0]],[[354960]],[[0]],[[104416]],[[0]],[[17360]],[[0]],[[1600]],[[0]],[[64]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
