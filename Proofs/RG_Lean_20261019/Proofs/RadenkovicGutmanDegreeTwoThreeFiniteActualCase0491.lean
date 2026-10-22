/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0491 : Family 10 := level10.get ⟨364,by decide⟩
def sourceMap0491 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0491 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0491_checked : acceptsGraphIso
    (source (graph core0491) (root 10) 0 0) DegreeOneSmallSpectrum1131.graph sourceMap0491=true := by decide +kernel
theorem fusedMap0491_checked : acceptsGraphIso
    (fused (graph core0491) (root 10) 0 0) DegreeOneSmallSpectrum1108.graph fusedMap0491=true := by decide +kernel
theorem certified0491 : Certified (graph core0491) (root 10) 0 0 :=
  of_native_maps core0491 DegreeOneSmallSpectrum1131.graph DegreeOneSmallSpectrum1108.graph
    sourceMap0491 fusedMap0491 sourceMap0491_checked fusedMap0491_checked
    DegreeTwoThreeFiniteComparisons.comparison0491
#print axioms sourceMap0491_checked
#print axioms fusedMap0491_checked
#print axioms certified0491
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
