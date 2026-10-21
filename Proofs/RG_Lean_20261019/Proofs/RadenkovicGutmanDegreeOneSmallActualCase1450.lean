/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1450 : Family 9 := level9.get ⟨183,by decide⟩
def sourceMap1450 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1450 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1450_checked : acceptsGraphIso
    (source (graph core1450) (root 9) 0 1) DegreeOneSmallSpectrum1236.graph sourceMap1450=true := by decide +kernel
theorem fusedMap1450_checked : acceptsGraphIso
    (fused (graph core1450) (root 9) 0 1) DegreeOneSmallSpectrum1247.graph fusedMap1450=true := by decide +kernel
theorem certified1450 : Certified (graph core1450) (root 9) 0 1 :=
  of_native_maps core1450 DegreeOneSmallSpectrum1236.graph DegreeOneSmallSpectrum1247.graph
    sourceMap1450 fusedMap1450 sourceMap1450_checked fusedMap1450_checked
    DegreeOneSmallComparisons.comparison1450
#print axioms sourceMap1450_checked
#print axioms fusedMap1450_checked
#print axioms certified1450
def sourceMap1450swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1450swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1450swap_checked : acceptsGraphIso
    (source (graph core1450) (root 9) 1 0) DegreeOneSmallSpectrum1236.graph sourceMap1450swap=true := by decide +kernel
theorem fusedMap1450swap_checked : acceptsGraphIso
    (fused (graph core1450) (root 9) 1 0) DegreeOneSmallSpectrum1247.graph fusedMap1450swap=true := by decide +kernel
theorem certified1450swap : Certified (graph core1450) (root 9) 1 0 :=
  of_native_maps core1450 DegreeOneSmallSpectrum1236.graph DegreeOneSmallSpectrum1247.graph
    sourceMap1450swap fusedMap1450swap sourceMap1450swap_checked fusedMap1450swap_checked
    DegreeOneSmallComparisons.comparison1450
#print axioms sourceMap1450swap_checked
#print axioms fusedMap1450swap_checked
#print axioms certified1450swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
