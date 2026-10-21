/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0929 : Family 8 := level8.get ⟨65,by decide⟩
def sourceMap0929 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,10,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap0929 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0929_checked : acceptsGraphIso
    (source (graph core0929) (root 8) 0 2) DegreeOneSmallSpectrum1450.graph sourceMap0929=true := by decide +kernel
theorem fusedMap0929_checked : acceptsGraphIso
    (fused (graph core0929) (root 8) 0 2) DegreeOneSmallSpectrum930.graph fusedMap0929=true := by decide +kernel
theorem certified0929 : Certified (graph core0929) (root 8) 0 2 :=
  of_native_maps core0929 DegreeOneSmallSpectrum1450.graph DegreeOneSmallSpectrum930.graph
    sourceMap0929 fusedMap0929 sourceMap0929_checked fusedMap0929_checked
    DegreeOneSmallComparisons.comparison0929
#print axioms sourceMap0929_checked
#print axioms fusedMap0929_checked
#print axioms certified0929
def sourceMap0929swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 8 2 0 v)
def fusedMap0929swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0929swap_checked : acceptsGraphIso
    (source (graph core0929) (root 8) 2 0) DegreeOneSmallSpectrum1450.graph sourceMap0929swap=true := by decide +kernel
theorem fusedMap0929swap_checked : acceptsGraphIso
    (fused (graph core0929) (root 8) 2 0) DegreeOneSmallSpectrum930.graph fusedMap0929swap=true := by decide +kernel
theorem certified0929swap : Certified (graph core0929) (root 8) 2 0 :=
  of_native_maps core0929 DegreeOneSmallSpectrum1450.graph DegreeOneSmallSpectrum930.graph
    sourceMap0929swap fusedMap0929swap sourceMap0929swap_checked fusedMap0929swap_checked
    DegreeOneSmallComparisons.comparison0929
#print axioms sourceMap0929swap_checked
#print axioms fusedMap0929swap_checked
#print axioms certified0929swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
