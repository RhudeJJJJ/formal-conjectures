/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1384 : Family 9 := level9.get ⟨129,by decide⟩
def sourceMap1384 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1384 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1384_checked : acceptsGraphIso
    (source (graph core1384) (root 9) 0 1) DegreeOneSmallSpectrum1418.graph sourceMap1384=true := by decide +kernel
theorem fusedMap1384_checked : acceptsGraphIso
    (fused (graph core1384) (root 9) 0 1) DegreeOneSmallSpectrum972.graph fusedMap1384=true := by decide +kernel
theorem certified1384 : Certified (graph core1384) (root 9) 0 1 :=
  of_native_maps core1384 DegreeOneSmallSpectrum1418.graph DegreeOneSmallSpectrum972.graph
    sourceMap1384 fusedMap1384 sourceMap1384_checked fusedMap1384_checked
    DegreeOneSmallComparisons.comparison1384
#print axioms sourceMap1384_checked
#print axioms fusedMap1384_checked
#print axioms certified1384
def sourceMap1384swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1384swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1384swap_checked : acceptsGraphIso
    (source (graph core1384) (root 9) 1 0) DegreeOneSmallSpectrum1418.graph sourceMap1384swap=true := by decide +kernel
theorem fusedMap1384swap_checked : acceptsGraphIso
    (fused (graph core1384) (root 9) 1 0) DegreeOneSmallSpectrum972.graph fusedMap1384swap=true := by decide +kernel
theorem certified1384swap : Certified (graph core1384) (root 9) 1 0 :=
  of_native_maps core1384 DegreeOneSmallSpectrum1418.graph DegreeOneSmallSpectrum972.graph
    sourceMap1384swap fusedMap1384swap sourceMap1384swap_checked fusedMap1384swap_checked
    DegreeOneSmallComparisons.comparison1384
#print axioms sourceMap1384swap_checked
#print axioms fusedMap1384swap_checked
#print axioms certified1384swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
