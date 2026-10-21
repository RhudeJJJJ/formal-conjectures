/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1578 : Family 9 := level9.get ⟨321,by decide⟩
def sourceMap1578 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1578 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1578_checked : acceptsGraphIso
    (source (graph core1578) (root 9) 0 1) DegreeOneSmallSpectrum1567.graph sourceMap1578=true := by decide +kernel
theorem fusedMap1578_checked : acceptsGraphIso
    (fused (graph core1578) (root 9) 0 1) DegreeOneSmallSpectrum986.graph fusedMap1578=true := by decide +kernel
theorem certified1578 : Certified (graph core1578) (root 9) 0 1 :=
  of_native_maps core1578 DegreeOneSmallSpectrum1567.graph DegreeOneSmallSpectrum986.graph
    sourceMap1578 fusedMap1578 sourceMap1578_checked fusedMap1578_checked
    DegreeOneSmallComparisons.comparison1578
#print axioms sourceMap1578_checked
#print axioms fusedMap1578_checked
#print axioms certified1578
def sourceMap1578swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1578swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1578swap_checked : acceptsGraphIso
    (source (graph core1578) (root 9) 1 0) DegreeOneSmallSpectrum1567.graph sourceMap1578swap=true := by decide +kernel
theorem fusedMap1578swap_checked : acceptsGraphIso
    (fused (graph core1578) (root 9) 1 0) DegreeOneSmallSpectrum986.graph fusedMap1578swap=true := by decide +kernel
theorem certified1578swap : Certified (graph core1578) (root 9) 1 0 :=
  of_native_maps core1578 DegreeOneSmallSpectrum1567.graph DegreeOneSmallSpectrum986.graph
    sourceMap1578swap fusedMap1578swap sourceMap1578swap_checked fusedMap1578swap_checked
    DegreeOneSmallComparisons.comparison1578
#print axioms sourceMap1578swap_checked
#print axioms fusedMap1578swap_checked
#print axioms certified1578swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
