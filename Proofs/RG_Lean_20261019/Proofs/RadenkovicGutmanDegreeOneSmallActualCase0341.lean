/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0341 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0341 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0341 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0341_checked : acceptsGraphIso
    (source (graph core0341) (root 6) 0 2) DegreeOneSmallSpectrum201.graph sourceMap0341=true := by decide +kernel
theorem fusedMap0341_checked : acceptsGraphIso
    (fused (graph core0341) (root 6) 0 2) DegreeOneSmallSpectrum202.graph fusedMap0341=true := by decide +kernel
theorem certified0341 : Certified (graph core0341) (root 6) 0 2 :=
  of_native_maps core0341 DegreeOneSmallSpectrum201.graph DegreeOneSmallSpectrum202.graph
    sourceMap0341 fusedMap0341 sourceMap0341_checked fusedMap0341_checked
    DegreeOneSmallComparisons.comparison0341
#print axioms sourceMap0341_checked
#print axioms fusedMap0341_checked
#print axioms certified0341
def sourceMap0341swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0341swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0341swap_checked : acceptsGraphIso
    (source (graph core0341) (root 6) 2 0) DegreeOneSmallSpectrum201.graph sourceMap0341swap=true := by decide +kernel
theorem fusedMap0341swap_checked : acceptsGraphIso
    (fused (graph core0341) (root 6) 2 0) DegreeOneSmallSpectrum202.graph fusedMap0341swap=true := by decide +kernel
theorem certified0341swap : Certified (graph core0341) (root 6) 2 0 :=
  of_native_maps core0341 DegreeOneSmallSpectrum201.graph DegreeOneSmallSpectrum202.graph
    sourceMap0341swap fusedMap0341swap sourceMap0341swap_checked fusedMap0341swap_checked
    DegreeOneSmallComparisons.comparison0341
#print axioms sourceMap0341swap_checked
#print axioms fusedMap0341swap_checked
#print axioms certified0341swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
