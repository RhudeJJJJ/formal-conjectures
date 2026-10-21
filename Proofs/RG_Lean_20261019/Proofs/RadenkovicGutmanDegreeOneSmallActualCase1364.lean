/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1364 : Family 9 := level9.get ⟨113,by decide⟩
def sourceMap1364 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1364 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1364_checked : acceptsGraphIso
    (source (graph core1364) (root 9) 0 1) DegreeOneSmallSpectrum1453.graph sourceMap1364=true := by decide +kernel
theorem fusedMap1364_checked : acceptsGraphIso
    (fused (graph core1364) (root 9) 0 1) DegreeOneSmallSpectrum968.graph fusedMap1364=true := by decide +kernel
theorem certified1364 : Certified (graph core1364) (root 9) 0 1 :=
  of_native_maps core1364 DegreeOneSmallSpectrum1453.graph DegreeOneSmallSpectrum968.graph
    sourceMap1364 fusedMap1364 sourceMap1364_checked fusedMap1364_checked
    DegreeOneSmallComparisons.comparison1364
#print axioms sourceMap1364_checked
#print axioms fusedMap1364_checked
#print axioms certified1364
def sourceMap1364swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1364swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1364swap_checked : acceptsGraphIso
    (source (graph core1364) (root 9) 1 0) DegreeOneSmallSpectrum1453.graph sourceMap1364swap=true := by decide +kernel
theorem fusedMap1364swap_checked : acceptsGraphIso
    (fused (graph core1364) (root 9) 1 0) DegreeOneSmallSpectrum968.graph fusedMap1364swap=true := by decide +kernel
theorem certified1364swap : Certified (graph core1364) (root 9) 1 0 :=
  of_native_maps core1364 DegreeOneSmallSpectrum1453.graph DegreeOneSmallSpectrum968.graph
    sourceMap1364swap fusedMap1364swap sourceMap1364swap_checked fusedMap1364swap_checked
    DegreeOneSmallComparisons.comparison1364
#print axioms sourceMap1364swap_checked
#print axioms fusedMap1364swap_checked
#print axioms certified1364swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
