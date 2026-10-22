/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0409 : Family 10 := level10.get ⟨66,by decide⟩
def sourceMap0409 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0409 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0409_checked : acceptsGraphIso
    (source (graph core0409) (root 10) 0 0) DegreeOneSmallSpectrum1063.graph sourceMap0409=true := by decide +kernel
theorem fusedMap0409_checked : acceptsGraphIso
    (fused (graph core0409) (root 10) 0 0) DegreeOneSmallSpectrum876.graph fusedMap0409=true := by decide +kernel
theorem certified0409 : Certified (graph core0409) (root 10) 0 0 :=
  of_native_maps core0409 DegreeOneSmallSpectrum1063.graph DegreeOneSmallSpectrum876.graph
    sourceMap0409 fusedMap0409 sourceMap0409_checked fusedMap0409_checked
    DegreeTwoThreeFiniteComparisons.comparison0409
#print axioms sourceMap0409_checked
#print axioms fusedMap0409_checked
#print axioms certified0409
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
