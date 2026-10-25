/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,6561],[0,13122],[6561]],[[0,0,0],[0,0],[0]],[[0,236196,56862],[236196,113724],[56862]],[[0,0,0],[0,0],[0]],[[2125764,2676888,193185],[2676888,386370],[193185]],[[0,0,0],[0,0],[0]],[[29760696,12990780,333882],[12990780,667764],[333882]],[[0,0,0],[0,0],[0]],[[186358644,35779320,323676],[35779320,647352],[323676]],[[0,0,0],[0,0],[0]],[[694573704,62551116,182250],[62551116,364500],[182250]],[[0,0,0],[0,0],[0]],[[1729112184,73424880,59049],[73424880,118098],[59049]],[[0,0,0],[0,0],[0]],[[3055798872,59562216,10206],[59562216,20412],[10206]],[[0,0,0],[0,0],[0]],[[3973606956,33767280,729],[33767280,1458],[729]],[[0,0],[0]],[[3884934312,13329036],[13329036]],[[0,0],[0]],[[2890694952,3586680],[3586680]],[[0,0],[0]],[[1644979752,626940],[626940]],[[0,0],[0]],[[714662028,64152],[64152]],[[0,0],[0]],[[234930456,2916],[2916]],[[0]],[[57381048]],[[0]],[[10083528]],[[0]],[[1204308]],[[0]],[[87480]],[[0]],[[2916]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
