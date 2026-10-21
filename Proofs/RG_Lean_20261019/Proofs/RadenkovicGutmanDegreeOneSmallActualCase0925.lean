/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0925 : Family 8 := level8.get ⟨63,by decide⟩
def sourceMap0925 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0925 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0925_checked : acceptsGraphIso
    (source (graph core0925) (root 8) 0 2) DegreeOneSmallSpectrum1433.graph sourceMap0925=true := by decide +kernel
theorem fusedMap0925_checked : acceptsGraphIso
    (fused (graph core0925) (root 8) 0 2) DegreeOneSmallSpectrum925.graph fusedMap0925=true := by decide +kernel
theorem certified0925 : Certified (graph core0925) (root 8) 0 2 :=
  of_native_maps core0925 DegreeOneSmallSpectrum1433.graph DegreeOneSmallSpectrum925.graph
    sourceMap0925 fusedMap0925 sourceMap0925_checked fusedMap0925_checked
    DegreeOneSmallComparisons.comparison0925
#print axioms sourceMap0925_checked
#print axioms fusedMap0925_checked
#print axioms certified0925
def sourceMap0925swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0925swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0925swap_checked : acceptsGraphIso
    (source (graph core0925) (root 8) 2 0) DegreeOneSmallSpectrum1433.graph sourceMap0925swap=true := by decide +kernel
theorem fusedMap0925swap_checked : acceptsGraphIso
    (fused (graph core0925) (root 8) 2 0) DegreeOneSmallSpectrum925.graph fusedMap0925swap=true := by decide +kernel
theorem certified0925swap : Certified (graph core0925) (root 8) 2 0 :=
  of_native_maps core0925 DegreeOneSmallSpectrum1433.graph DegreeOneSmallSpectrum925.graph
    sourceMap0925swap fusedMap0925swap sourceMap0925swap_checked fusedMap0925swap_checked
    DegreeOneSmallComparisons.comparison0925
#print axioms sourceMap0925swap_checked
#print axioms fusedMap0925swap_checked
#print axioms certified0925swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
