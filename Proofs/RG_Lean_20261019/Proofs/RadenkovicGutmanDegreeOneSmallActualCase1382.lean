/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1382 : Family 9 := level9.get ⟨127,by decide⟩
def sourceMap1382 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1382 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1382_checked : acceptsGraphIso
    (source (graph core1382) (root 9) 0 1) DegreeOneSmallSpectrum1408.graph sourceMap1382=true := by decide +kernel
theorem fusedMap1382_checked : acceptsGraphIso
    (fused (graph core1382) (root 9) 0 1) DegreeOneSmallSpectrum969.graph fusedMap1382=true := by decide +kernel
theorem certified1382 : Certified (graph core1382) (root 9) 0 1 :=
  of_native_maps core1382 DegreeOneSmallSpectrum1408.graph DegreeOneSmallSpectrum969.graph
    sourceMap1382 fusedMap1382 sourceMap1382_checked fusedMap1382_checked
    DegreeOneSmallComparisons.comparison1382
#print axioms sourceMap1382_checked
#print axioms fusedMap1382_checked
#print axioms certified1382
def sourceMap1382swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1382swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1382swap_checked : acceptsGraphIso
    (source (graph core1382) (root 9) 1 0) DegreeOneSmallSpectrum1408.graph sourceMap1382swap=true := by decide +kernel
theorem fusedMap1382swap_checked : acceptsGraphIso
    (fused (graph core1382) (root 9) 1 0) DegreeOneSmallSpectrum969.graph fusedMap1382swap=true := by decide +kernel
theorem certified1382swap : Certified (graph core1382) (root 9) 1 0 :=
  of_native_maps core1382 DegreeOneSmallSpectrum1408.graph DegreeOneSmallSpectrum969.graph
    sourceMap1382swap fusedMap1382swap sourceMap1382swap_checked fusedMap1382swap_checked
    DegreeOneSmallComparisons.comparison1382
#print axioms sourceMap1382swap_checked
#print axioms fusedMap1382swap_checked
#print axioms certified1382swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
