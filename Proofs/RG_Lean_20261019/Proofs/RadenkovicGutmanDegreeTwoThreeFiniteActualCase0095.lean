/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0095 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap0095 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0095 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0095_checked : acceptsGraphIso
    (source (graph core0095) (root 8) 0 0) DegreeOneSmallSpectrum260.graph sourceMap0095=true := by decide +kernel
theorem fusedMap0095_checked : acceptsGraphIso
    (fused (graph core0095) (root 8) 0 0) DegreeOneSmallSpectrum290.graph fusedMap0095=true := by decide +kernel
theorem certified0095 : Certified (graph core0095) (root 8) 0 0 :=
  of_native_maps core0095 DegreeOneSmallSpectrum260.graph DegreeOneSmallSpectrum290.graph
    sourceMap0095 fusedMap0095 sourceMap0095_checked fusedMap0095_checked
    DegreeTwoThreeFiniteComparisons.comparison0095
#print axioms sourceMap0095_checked
#print axioms fusedMap0095_checked
#print axioms certified0095
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
