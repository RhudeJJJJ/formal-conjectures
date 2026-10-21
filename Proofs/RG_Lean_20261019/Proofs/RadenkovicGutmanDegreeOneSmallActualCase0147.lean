/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0147 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0147 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap0147 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap0147_checked : acceptsGraphIso
    (source (graph core0147) (root 4) 0 4) DegreeOneSmallSpectrum170.graph sourceMap0147=true := by decide +kernel
theorem fusedMap0147_checked : acceptsGraphIso
    (fused (graph core0147) (root 4) 0 4) DegreeOneSmallSpectrum175.graph fusedMap0147=true := by decide +kernel
theorem certified0147 : Certified (graph core0147) (root 4) 0 4 :=
  of_native_maps core0147 DegreeOneSmallSpectrum170.graph DegreeOneSmallSpectrum175.graph
    sourceMap0147 fusedMap0147 sourceMap0147_checked fusedMap0147_checked
    DegreeOneSmallComparisons.comparison0147
#print axioms sourceMap0147_checked
#print axioms fusedMap0147_checked
#print axioms certified0147
def sourceMap0147swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,6] (sourceLabel 4 4 0 v)
def fusedMap0147swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap0147swap_checked : acceptsGraphIso
    (source (graph core0147) (root 4) 4 0) DegreeOneSmallSpectrum170.graph sourceMap0147swap=true := by decide +kernel
theorem fusedMap0147swap_checked : acceptsGraphIso
    (fused (graph core0147) (root 4) 4 0) DegreeOneSmallSpectrum175.graph fusedMap0147swap=true := by decide +kernel
theorem certified0147swap : Certified (graph core0147) (root 4) 4 0 :=
  of_native_maps core0147 DegreeOneSmallSpectrum170.graph DegreeOneSmallSpectrum175.graph
    sourceMap0147swap fusedMap0147swap sourceMap0147swap_checked fusedMap0147swap_checked
    DegreeOneSmallComparisons.comparison0147
#print axioms sourceMap0147swap_checked
#print axioms fusedMap0147swap_checked
#print axioms certified0147swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
