/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1376 : Family 9 := level9.get ⟨121,by decide⟩
def sourceMap1376 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1376 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1376_checked : acceptsGraphIso
    (source (graph core1376) (root 9) 0 1) DegreeOneSmallSpectrum1424.graph sourceMap1376=true := by decide +kernel
theorem fusedMap1376_checked : acceptsGraphIso
    (fused (graph core1376) (root 9) 0 1) DegreeOneSmallSpectrum973.graph fusedMap1376=true := by decide +kernel
theorem certified1376 : Certified (graph core1376) (root 9) 0 1 :=
  of_native_maps core1376 DegreeOneSmallSpectrum1424.graph DegreeOneSmallSpectrum973.graph
    sourceMap1376 fusedMap1376 sourceMap1376_checked fusedMap1376_checked
    DegreeOneSmallComparisons.comparison1376
#print axioms sourceMap1376_checked
#print axioms fusedMap1376_checked
#print axioms certified1376
def sourceMap1376swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1376swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1376swap_checked : acceptsGraphIso
    (source (graph core1376) (root 9) 1 0) DegreeOneSmallSpectrum1424.graph sourceMap1376swap=true := by decide +kernel
theorem fusedMap1376swap_checked : acceptsGraphIso
    (fused (graph core1376) (root 9) 1 0) DegreeOneSmallSpectrum973.graph fusedMap1376swap=true := by decide +kernel
theorem certified1376swap : Certified (graph core1376) (root 9) 1 0 :=
  of_native_maps core1376 DegreeOneSmallSpectrum1424.graph DegreeOneSmallSpectrum973.graph
    sourceMap1376swap fusedMap1376swap sourceMap1376swap_checked fusedMap1376swap_checked
    DegreeOneSmallComparisons.comparison1376
#print axioms sourceMap1376swap_checked
#print axioms fusedMap1376swap_checked
#print axioms certified1376swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
