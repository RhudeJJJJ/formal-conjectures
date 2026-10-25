/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode051
import Proofs.RadenkovicGutmanD34Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3468],[0,-3468]],[[0,0,0],[0,0,0],[0,0]],[[0,31212,-52020],[31212,-156060,-15232],[-52020,-15232]],[[0,0,0],[0,0,0],[0,0]],[[468180,-1031832,-400656],[-1031832,-1151172,-19380],[-400656,-19380]],[[0,0,0],[0,0,0],[0,0]],[[-2680560,-12573540,-1228964],[-12573540,-3378852,-9180],[-1228964,-9180]],[[0,0,0],[0,0,0],[0,0]],[[-79074684,-59081324,-1969484],[-59081324,-5212676,-1632],[-1969484,-1632]],[[0,0,0],[0,0,0],[0,0]],[[-550277148,-155513076,-1813220],[-155513076,-4655416,-68],[-1813220,-68]],[[0,0,0],[0,0],[0]],[[-2084951536,-260251300,-990012],[-260251300,-2484856],[-990012]],[[0,0,0],[0,0],[0]],[[-5132874804,-293934964,-317628],[-293934964,-785332],[-317628]],[[0,0,0],[0,0],[0]],[[-8873876920,-230803356,-56100],[-230803356,-137972],[-56100]],[[0,0,0],[0,0],[0]],[[-11236554668,-127464368,-4488],[-127464368,-11220],[-4488]],[[0,0,0],[0,0],[0]],[[-10678863004,-49355284,-68],[-49355284,-204],[-68]],[[0,0],[0]],[[-7721793312,-13141136],[-13141136]],[[0,0],[0]],[[-4273127888,-2303432],[-2303432]],[[0,0],[0]],[[-1807967204,-243032],[-243032]],[[0,0],[0]],[[-580164712,-12512],[-12512]],[[0,0],[0]],[[-138833220,-136],[-136]],[[0]],[[-24049560]],[[0]],[[-2864500]],[[0]],[[-213248]],[[0]],[[-8024]],[[0]],[[-68]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
