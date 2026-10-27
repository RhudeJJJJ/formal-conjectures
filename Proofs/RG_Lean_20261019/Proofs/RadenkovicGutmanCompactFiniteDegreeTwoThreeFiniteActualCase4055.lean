/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4055 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap4055 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap4055 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4055_checked : acceptsGraphIso
    (source (graph core4055) (root 6) 2 2) DegreeOneSmallSpectrum1972.graph sourceMap4055=true := by decide +kernel
theorem fusedMap4055_checked : acceptsGraphIso
    (fused (graph core4055) (root 6) 2 2) DegreeOneSmallSpectrum945.graph fusedMap4055=true := by decide +kernel
theorem certified4055 : Certified (graph core4055) (root 6) 2 2 :=
  of_native_maps core4055 DegreeOneSmallSpectrum1972.graph DegreeOneSmallSpectrum945.graph
    sourceMap4055 fusedMap4055 sourceMap4055_checked fusedMap4055_checked
    DegreeTwoThreeFiniteComparisons.comparison4055
#print axioms sourceMap4055_checked
#print axioms fusedMap4055_checked
#print axioms certified4055
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
