/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2409 : Family 10 := level10.get ⟨1269,by decide⟩
def sourceMap2409 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2409 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2409_checked : acceptsGraphIso
    (source (graph core2409) (root 10) 0 0) DegreeOneSmallSpectrum1923.graph sourceMap2409=true := by decide +kernel
theorem fusedMap2409_checked : acceptsGraphIso
    (fused (graph core2409) (root 10) 0 0) DegreeOneSmallSpectrum1922.graph fusedMap2409=true := by decide +kernel
theorem certified2409 : Certified (graph core2409) (root 10) 0 0 :=
  of_native_maps core2409 DegreeOneSmallSpectrum1923.graph DegreeOneSmallSpectrum1922.graph
    sourceMap2409 fusedMap2409 sourceMap2409_checked fusedMap2409_checked
    DegreeOneSmallComparisons.comparison2409
#print axioms sourceMap2409_checked
#print axioms fusedMap2409_checked
#print axioms certified2409
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
