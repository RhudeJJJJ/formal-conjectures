/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0409 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0409 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 1 3 v)
def fusedMap0409 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0409_checked : acceptsGraphIso
    (source (graph core0409) (root 6) 1 3) DegreeOneSmallSpectrum1096.graph sourceMap0409=true := by decide +kernel
theorem fusedMap0409_checked : acceptsGraphIso
    (fused (graph core0409) (root 6) 1 3) DegreeOneSmallSpectrum871.graph fusedMap0409=true := by decide +kernel
theorem certified0409 : Certified (graph core0409) (root 6) 1 3 :=
  of_native_maps core0409 DegreeOneSmallSpectrum1096.graph DegreeOneSmallSpectrum871.graph
    sourceMap0409 fusedMap0409 sourceMap0409_checked fusedMap0409_checked
    DegreeOneSmallComparisons.comparison0409
#print axioms sourceMap0409_checked
#print axioms fusedMap0409_checked
#print axioms certified0409
def sourceMap0409swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,7,8] (sourceLabel 6 3 1 v)
def fusedMap0409swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0409swap_checked : acceptsGraphIso
    (source (graph core0409) (root 6) 3 1) DegreeOneSmallSpectrum1096.graph sourceMap0409swap=true := by decide +kernel
theorem fusedMap0409swap_checked : acceptsGraphIso
    (fused (graph core0409) (root 6) 3 1) DegreeOneSmallSpectrum871.graph fusedMap0409swap=true := by decide +kernel
theorem certified0409swap : Certified (graph core0409) (root 6) 3 1 :=
  of_native_maps core0409 DegreeOneSmallSpectrum1096.graph DegreeOneSmallSpectrum871.graph
    sourceMap0409swap fusedMap0409swap sourceMap0409swap_checked fusedMap0409swap_checked
    DegreeOneSmallComparisons.comparison0409
#print axioms sourceMap0409swap_checked
#print axioms fusedMap0409swap_checked
#print axioms certified0409swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
