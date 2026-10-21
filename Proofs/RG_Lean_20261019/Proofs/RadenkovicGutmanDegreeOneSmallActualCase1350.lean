/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1350 : Family 9 := level9.get ⟨101,by decide⟩
def sourceMap1350 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1350 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1350_checked : acceptsGraphIso
    (source (graph core1350) (root 9) 0 1) DegreeOneSmallSpectrum1432.graph sourceMap1350=true := by decide +kernel
theorem fusedMap1350_checked : acceptsGraphIso
    (fused (graph core1350) (root 9) 0 1) DegreeOneSmallSpectrum955.graph fusedMap1350=true := by decide +kernel
theorem certified1350 : Certified (graph core1350) (root 9) 0 1 :=
  of_native_maps core1350 DegreeOneSmallSpectrum1432.graph DegreeOneSmallSpectrum955.graph
    sourceMap1350 fusedMap1350 sourceMap1350_checked fusedMap1350_checked
    DegreeOneSmallComparisons.comparison1350
#print axioms sourceMap1350_checked
#print axioms fusedMap1350_checked
#print axioms certified1350
def sourceMap1350swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1350swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1350swap_checked : acceptsGraphIso
    (source (graph core1350) (root 9) 1 0) DegreeOneSmallSpectrum1432.graph sourceMap1350swap=true := by decide +kernel
theorem fusedMap1350swap_checked : acceptsGraphIso
    (fused (graph core1350) (root 9) 1 0) DegreeOneSmallSpectrum955.graph fusedMap1350swap=true := by decide +kernel
theorem certified1350swap : Certified (graph core1350) (root 9) 1 0 :=
  of_native_maps core1350 DegreeOneSmallSpectrum1432.graph DegreeOneSmallSpectrum955.graph
    sourceMap1350swap fusedMap1350swap sourceMap1350swap_checked fusedMap1350swap_checked
    DegreeOneSmallComparisons.comparison1350
#print axioms sourceMap1350swap_checked
#print axioms fusedMap1350swap_checked
#print axioms certified1350swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
