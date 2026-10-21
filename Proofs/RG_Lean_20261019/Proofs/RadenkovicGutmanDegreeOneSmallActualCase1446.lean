/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1446 : Family 9 := level9.get ⟨180,by decide⟩
def sourceMap1446 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1446 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1446_checked : acceptsGraphIso
    (source (graph core1446) (root 9) 0 1) DegreeOneSmallSpectrum1221.graph sourceMap1446=true := by decide +kernel
theorem fusedMap1446_checked : acceptsGraphIso
    (fused (graph core1446) (root 9) 0 1) DegreeOneSmallSpectrum1226.graph fusedMap1446=true := by decide +kernel
theorem certified1446 : Certified (graph core1446) (root 9) 0 1 :=
  of_native_maps core1446 DegreeOneSmallSpectrum1221.graph DegreeOneSmallSpectrum1226.graph
    sourceMap1446 fusedMap1446 sourceMap1446_checked fusedMap1446_checked
    DegreeOneSmallComparisons.comparison1446
#print axioms sourceMap1446_checked
#print axioms fusedMap1446_checked
#print axioms certified1446
def sourceMap1446swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1446swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1446swap_checked : acceptsGraphIso
    (source (graph core1446) (root 9) 1 0) DegreeOneSmallSpectrum1221.graph sourceMap1446swap=true := by decide +kernel
theorem fusedMap1446swap_checked : acceptsGraphIso
    (fused (graph core1446) (root 9) 1 0) DegreeOneSmallSpectrum1226.graph fusedMap1446swap=true := by decide +kernel
theorem certified1446swap : Certified (graph core1446) (root 9) 1 0 :=
  of_native_maps core1446 DegreeOneSmallSpectrum1221.graph DegreeOneSmallSpectrum1226.graph
    sourceMap1446swap fusedMap1446swap sourceMap1446swap_checked fusedMap1446swap_checked
    DegreeOneSmallComparisons.comparison1446
#print axioms sourceMap1446swap_checked
#print axioms fusedMap1446swap_checked
#print axioms certified1446swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
