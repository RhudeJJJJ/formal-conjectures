/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0128 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0128 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,4,5,6,7,3,1,2] (sourceLabel 4 0 1 v)
def fusedMap0128 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 0 1 v)
theorem sourceMap0128_checked : acceptsGraphIso
    (source (graph core0128) (root 4) 0 1) DegreeOneSmallSpectrum024.graph sourceMap0128=true := by decide +kernel
theorem fusedMap0128_checked : acceptsGraphIso
    (fused (graph core0128) (root 4) 0 1) DegreeOneSmallSpectrum025.graph fusedMap0128=true := by decide +kernel
theorem certified0128 : Certified (graph core0128) (root 4) 0 1 :=
  of_native_maps core0128 DegreeOneSmallSpectrum024.graph DegreeOneSmallSpectrum025.graph
    sourceMap0128 fusedMap0128 sourceMap0128_checked fusedMap0128_checked
    DegreeOneSmallComparisons.comparison0128
#print axioms sourceMap0128_checked
#print axioms fusedMap0128_checked
#print axioms certified0128
def sourceMap0128swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,4,5,6,7,1,2,3] (sourceLabel 4 1 0 v)
def fusedMap0128swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 1 0 v)
theorem sourceMap0128swap_checked : acceptsGraphIso
    (source (graph core0128) (root 4) 1 0) DegreeOneSmallSpectrum024.graph sourceMap0128swap=true := by decide +kernel
theorem fusedMap0128swap_checked : acceptsGraphIso
    (fused (graph core0128) (root 4) 1 0) DegreeOneSmallSpectrum025.graph fusedMap0128swap=true := by decide +kernel
theorem certified0128swap : Certified (graph core0128) (root 4) 1 0 :=
  of_native_maps core0128 DegreeOneSmallSpectrum024.graph DegreeOneSmallSpectrum025.graph
    sourceMap0128swap fusedMap0128swap sourceMap0128swap_checked fusedMap0128swap_checked
    DegreeOneSmallComparisons.comparison0128
#print axioms sourceMap0128swap_checked
#print axioms fusedMap0128swap_checked
#print axioms certified0128swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
