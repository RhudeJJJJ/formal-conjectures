/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0327 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0327 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0327 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0327_checked : acceptsGraphIso
    (source (graph core0327) (root 6) 1 2) DegreeOneSmallSpectrum454.graph sourceMap0327=true := by decide +kernel
theorem fusedMap0327_checked : acceptsGraphIso
    (fused (graph core0327) (root 6) 1 2) DegreeOneSmallSpectrum371.graph fusedMap0327=true := by decide +kernel
theorem certified0327 : Certified (graph core0327) (root 6) 1 2 :=
  of_native_maps core0327 DegreeOneSmallSpectrum454.graph DegreeOneSmallSpectrum371.graph
    sourceMap0327 fusedMap0327 sourceMap0327_checked fusedMap0327_checked
    DegreeOneSmallComparisons.comparison0327
#print axioms sourceMap0327_checked
#print axioms fusedMap0327_checked
#print axioms certified0327
def sourceMap0327swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0327swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0327swap_checked : acceptsGraphIso
    (source (graph core0327) (root 6) 2 1) DegreeOneSmallSpectrum454.graph sourceMap0327swap=true := by decide +kernel
theorem fusedMap0327swap_checked : acceptsGraphIso
    (fused (graph core0327) (root 6) 2 1) DegreeOneSmallSpectrum371.graph fusedMap0327swap=true := by decide +kernel
theorem certified0327swap : Certified (graph core0327) (root 6) 2 1 :=
  of_native_maps core0327 DegreeOneSmallSpectrum454.graph DegreeOneSmallSpectrum371.graph
    sourceMap0327swap fusedMap0327swap sourceMap0327swap_checked fusedMap0327swap_checked
    DegreeOneSmallComparisons.comparison0327
#print axioms sourceMap0327swap_checked
#print axioms fusedMap0327swap_checked
#print axioms certified0327swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
