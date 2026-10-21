/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0841 : Family 8 := level8.get ⟨34,by decide⟩
def sourceMap0841 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0841 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0841_checked : acceptsGraphIso
    (source (graph core0841) (root 8) 0 2) DegreeOneSmallSpectrum1007.graph sourceMap0841=true := by decide +kernel
theorem fusedMap0841_checked : acceptsGraphIso
    (fused (graph core0841) (root 8) 0 2) DegreeOneSmallSpectrum862.graph fusedMap0841=true := by decide +kernel
theorem certified0841 : Certified (graph core0841) (root 8) 0 2 :=
  of_native_maps core0841 DegreeOneSmallSpectrum1007.graph DegreeOneSmallSpectrum862.graph
    sourceMap0841 fusedMap0841 sourceMap0841_checked fusedMap0841_checked
    DegreeOneSmallComparisons.comparison0841
#print axioms sourceMap0841_checked
#print axioms fusedMap0841_checked
#print axioms certified0841
def sourceMap0841swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0841swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0841swap_checked : acceptsGraphIso
    (source (graph core0841) (root 8) 2 0) DegreeOneSmallSpectrum1007.graph sourceMap0841swap=true := by decide +kernel
theorem fusedMap0841swap_checked : acceptsGraphIso
    (fused (graph core0841) (root 8) 2 0) DegreeOneSmallSpectrum862.graph fusedMap0841swap=true := by decide +kernel
theorem certified0841swap : Certified (graph core0841) (root 8) 2 0 :=
  of_native_maps core0841 DegreeOneSmallSpectrum1007.graph DegreeOneSmallSpectrum862.graph
    sourceMap0841swap fusedMap0841swap sourceMap0841swap_checked fusedMap0841swap_checked
    DegreeOneSmallComparisons.comparison0841
#print axioms sourceMap0841swap_checked
#print axioms fusedMap0841swap_checked
#print axioms certified0841swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
