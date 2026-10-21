/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0585 : Family 7 := level7.get ⟨31,by decide⟩
def sourceMap0585 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (sourceLabel 7 0 0 v)
def fusedMap0585 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0585_checked : acceptsGraphIso
    (source (graph core0585) (root 7) 0 0) DegreeOneSmallSpectrum113.graph sourceMap0585=true := by decide +kernel
theorem fusedMap0585_checked : acceptsGraphIso
    (fused (graph core0585) (root 7) 0 0) DegreeOneSmallSpectrum115.graph fusedMap0585=true := by decide +kernel
theorem certified0585 : Certified (graph core0585) (root 7) 0 0 :=
  of_native_maps core0585 DegreeOneSmallSpectrum113.graph DegreeOneSmallSpectrum115.graph
    sourceMap0585 fusedMap0585 sourceMap0585_checked fusedMap0585_checked
    DegreeOneSmallComparisons.comparison0585
#print axioms sourceMap0585_checked
#print axioms fusedMap0585_checked
#print axioms certified0585
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
