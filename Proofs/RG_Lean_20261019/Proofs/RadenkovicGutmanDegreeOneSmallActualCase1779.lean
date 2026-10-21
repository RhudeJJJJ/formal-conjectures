/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1779 : Family 10 := level10.get ⟨13,by decide⟩
def sourceMap1779 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (sourceLabel 10 0 0 v)
def fusedMap1779 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1779_checked : acceptsGraphIso
    (source (graph core1779) (root 10) 0 0) DegreeOneSmallSpectrum890.graph sourceMap1779=true := by decide +kernel
theorem fusedMap1779_checked : acceptsGraphIso
    (fused (graph core1779) (root 10) 0 0) DegreeOneSmallSpectrum894.graph fusedMap1779=true := by decide +kernel
theorem certified1779 : Certified (graph core1779) (root 10) 0 0 :=
  of_native_maps core1779 DegreeOneSmallSpectrum890.graph DegreeOneSmallSpectrum894.graph
    sourceMap1779 fusedMap1779 sourceMap1779_checked fusedMap1779_checked
    DegreeOneSmallComparisons.comparison1779
#print axioms sourceMap1779_checked
#print axioms fusedMap1779_checked
#print axioms certified1779
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
