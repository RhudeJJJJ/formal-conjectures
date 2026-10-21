/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0710 : Family 7 := level7.get ⟨73,by decide⟩
def sourceMap0710 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0710 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0710_checked : acceptsGraphIso
    (source (graph core0710) (root 7) 1 2) DegreeOneSmallSpectrum1792.graph sourceMap0710=true := by decide +kernel
theorem fusedMap0710_checked : acceptsGraphIso
    (fused (graph core0710) (root 7) 1 2) DegreeOneSmallSpectrum1118.graph fusedMap0710=true := by decide +kernel
theorem certified0710 : Certified (graph core0710) (root 7) 1 2 :=
  of_native_maps core0710 DegreeOneSmallSpectrum1792.graph DegreeOneSmallSpectrum1118.graph
    sourceMap0710 fusedMap0710 sourceMap0710_checked fusedMap0710_checked
    DegreeOneSmallComparisons.comparison0710
#print axioms sourceMap0710_checked
#print axioms fusedMap0710_checked
#print axioms certified0710
def sourceMap0710swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0710swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0710swap_checked : acceptsGraphIso
    (source (graph core0710) (root 7) 2 1) DegreeOneSmallSpectrum1792.graph sourceMap0710swap=true := by decide +kernel
theorem fusedMap0710swap_checked : acceptsGraphIso
    (fused (graph core0710) (root 7) 2 1) DegreeOneSmallSpectrum1118.graph fusedMap0710swap=true := by decide +kernel
theorem certified0710swap : Certified (graph core0710) (root 7) 2 1 :=
  of_native_maps core0710 DegreeOneSmallSpectrum1792.graph DegreeOneSmallSpectrum1118.graph
    sourceMap0710swap fusedMap0710swap sourceMap0710swap_checked fusedMap0710swap_checked
    DegreeOneSmallComparisons.comparison0710
#print axioms sourceMap0710swap_checked
#print axioms fusedMap0710swap_checked
#print axioms certified0710swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
