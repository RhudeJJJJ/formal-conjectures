/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0630 : Family 7 := level7.get ⟨43,by decide⟩
def sourceMap0630 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0630 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0630_checked : acceptsGraphIso
    (source (graph core0630) (root 7) 0 3) DegreeOneSmallSpectrum1380.graph sourceMap0630=true := by decide +kernel
theorem fusedMap0630_checked : acceptsGraphIso
    (fused (graph core0630) (root 7) 0 3) DegreeOneSmallSpectrum917.graph fusedMap0630=true := by decide +kernel
theorem certified0630 : Certified (graph core0630) (root 7) 0 3 :=
  of_native_maps core0630 DegreeOneSmallSpectrum1380.graph DegreeOneSmallSpectrum917.graph
    sourceMap0630 fusedMap0630 sourceMap0630_checked fusedMap0630_checked
    DegreeOneSmallComparisons.comparison0630
#print axioms sourceMap0630_checked
#print axioms fusedMap0630_checked
#print axioms certified0630
def sourceMap0630swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0630swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0630swap_checked : acceptsGraphIso
    (source (graph core0630) (root 7) 3 0) DegreeOneSmallSpectrum1380.graph sourceMap0630swap=true := by decide +kernel
theorem fusedMap0630swap_checked : acceptsGraphIso
    (fused (graph core0630) (root 7) 3 0) DegreeOneSmallSpectrum917.graph fusedMap0630swap=true := by decide +kernel
theorem certified0630swap : Certified (graph core0630) (root 7) 3 0 :=
  of_native_maps core0630 DegreeOneSmallSpectrum1380.graph DegreeOneSmallSpectrum917.graph
    sourceMap0630swap fusedMap0630swap sourceMap0630swap_checked fusedMap0630swap_checked
    DegreeOneSmallComparisons.comparison0630
#print axioms sourceMap0630swap_checked
#print axioms fusedMap0630swap_checked
#print axioms certified0630swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
