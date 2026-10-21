/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0472 : Family 7 := level7.get ⟨4,by decide⟩
def sourceMap0472 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 7 0 1 v)
def fusedMap0472 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0472_checked : acceptsGraphIso
    (source (graph core0472) (root 7) 0 1) DegreeOneSmallSpectrum217.graph sourceMap0472=true := by decide +kernel
theorem fusedMap0472_checked : acceptsGraphIso
    (fused (graph core0472) (root 7) 0 1) DegreeOneSmallSpectrum167.graph fusedMap0472=true := by decide +kernel
theorem certified0472 : Certified (graph core0472) (root 7) 0 1 :=
  of_native_maps core0472 DegreeOneSmallSpectrum217.graph DegreeOneSmallSpectrum167.graph
    sourceMap0472 fusedMap0472 sourceMap0472_checked fusedMap0472_checked
    DegreeOneSmallComparisons.comparison0472
#print axioms sourceMap0472_checked
#print axioms fusedMap0472_checked
#print axioms certified0472
def sourceMap0472swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 7 1 0 v)
def fusedMap0472swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0472swap_checked : acceptsGraphIso
    (source (graph core0472) (root 7) 1 0) DegreeOneSmallSpectrum217.graph sourceMap0472swap=true := by decide +kernel
theorem fusedMap0472swap_checked : acceptsGraphIso
    (fused (graph core0472) (root 7) 1 0) DegreeOneSmallSpectrum167.graph fusedMap0472swap=true := by decide +kernel
theorem certified0472swap : Certified (graph core0472) (root 7) 1 0 :=
  of_native_maps core0472 DegreeOneSmallSpectrum217.graph DegreeOneSmallSpectrum167.graph
    sourceMap0472swap fusedMap0472swap sourceMap0472swap_checked fusedMap0472swap_checked
    DegreeOneSmallComparisons.comparison0472
#print axioms sourceMap0472swap_checked
#print axioms fusedMap0472swap_checked
#print axioms certified0472swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
