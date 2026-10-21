/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1409 : Family 9 := level9.get ⟨152,by decide⟩
def sourceMap1409 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1409 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1409_checked : acceptsGraphIso
    (source (graph core1409) (root 9) 0 0) DegreeOneSmallSpectrum662.graph sourceMap1409=true := by decide +kernel
theorem fusedMap1409_checked : acceptsGraphIso
    (fused (graph core1409) (root 9) 0 0) DegreeOneSmallSpectrum425.graph fusedMap1409=true := by decide +kernel
theorem certified1409 : Certified (graph core1409) (root 9) 0 0 :=
  of_native_maps core1409 DegreeOneSmallSpectrum662.graph DegreeOneSmallSpectrum425.graph
    sourceMap1409 fusedMap1409 sourceMap1409_checked fusedMap1409_checked
    DegreeOneSmallComparisons.comparison1409
#print axioms sourceMap1409_checked
#print axioms fusedMap1409_checked
#print axioms certified1409
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
