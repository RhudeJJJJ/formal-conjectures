/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1392 : Family 9 := level9.get ⟨140,by decide⟩
def sourceMap1392 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1392 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1392_checked : acceptsGraphIso
    (source (graph core1392) (root 9) 0 1) DegreeOneSmallSpectrum1003.graph sourceMap1392=true := by decide +kernel
theorem fusedMap1392_checked : acceptsGraphIso
    (fused (graph core1392) (root 9) 0 1) DegreeOneSmallSpectrum1008.graph fusedMap1392=true := by decide +kernel
theorem certified1392 : Certified (graph core1392) (root 9) 0 1 :=
  of_native_maps core1392 DegreeOneSmallSpectrum1003.graph DegreeOneSmallSpectrum1008.graph
    sourceMap1392 fusedMap1392 sourceMap1392_checked fusedMap1392_checked
    DegreeOneSmallComparisons.comparison1392
#print axioms sourceMap1392_checked
#print axioms fusedMap1392_checked
#print axioms certified1392
def sourceMap1392swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1392swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1392swap_checked : acceptsGraphIso
    (source (graph core1392) (root 9) 1 0) DegreeOneSmallSpectrum1003.graph sourceMap1392swap=true := by decide +kernel
theorem fusedMap1392swap_checked : acceptsGraphIso
    (fused (graph core1392) (root 9) 1 0) DegreeOneSmallSpectrum1008.graph fusedMap1392swap=true := by decide +kernel
theorem certified1392swap : Certified (graph core1392) (root 9) 1 0 :=
  of_native_maps core1392 DegreeOneSmallSpectrum1003.graph DegreeOneSmallSpectrum1008.graph
    sourceMap1392swap fusedMap1392swap sourceMap1392swap_checked fusedMap1392swap_checked
    DegreeOneSmallComparisons.comparison1392
#print axioms sourceMap1392swap_checked
#print axioms fusedMap1392swap_checked
#print axioms certified1392swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
