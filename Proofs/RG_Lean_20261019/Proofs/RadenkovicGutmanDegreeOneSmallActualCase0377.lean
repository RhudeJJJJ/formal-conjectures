/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0377 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0377 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0377 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0377_checked : acceptsGraphIso
    (source (graph core0377) (root 6) 0 2) DegreeOneSmallSpectrum224.graph sourceMap0377=true := by decide +kernel
theorem fusedMap0377_checked : acceptsGraphIso
    (fused (graph core0377) (root 6) 0 2) DegreeOneSmallSpectrum225.graph fusedMap0377=true := by decide +kernel
theorem certified0377 : Certified (graph core0377) (root 6) 0 2 :=
  of_native_maps core0377 DegreeOneSmallSpectrum224.graph DegreeOneSmallSpectrum225.graph
    sourceMap0377 fusedMap0377 sourceMap0377_checked fusedMap0377_checked
    DegreeOneSmallComparisons.comparison0377
#print axioms sourceMap0377_checked
#print axioms fusedMap0377_checked
#print axioms certified0377
def sourceMap0377swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0377swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0377swap_checked : acceptsGraphIso
    (source (graph core0377) (root 6) 2 0) DegreeOneSmallSpectrum224.graph sourceMap0377swap=true := by decide +kernel
theorem fusedMap0377swap_checked : acceptsGraphIso
    (fused (graph core0377) (root 6) 2 0) DegreeOneSmallSpectrum225.graph fusedMap0377swap=true := by decide +kernel
theorem certified0377swap : Certified (graph core0377) (root 6) 2 0 :=
  of_native_maps core0377 DegreeOneSmallSpectrum224.graph DegreeOneSmallSpectrum225.graph
    sourceMap0377swap fusedMap0377swap sourceMap0377swap_checked fusedMap0377swap_checked
    DegreeOneSmallComparisons.comparison0377
#print axioms sourceMap0377swap_checked
#print axioms fusedMap0377swap_checked
#print axioms certified0377swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
