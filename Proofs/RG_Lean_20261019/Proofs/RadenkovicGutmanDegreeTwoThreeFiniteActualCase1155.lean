/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1155 : Family 8 := level8.get ⟨180,by decide⟩
def sourceMap1155 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,8,5,6,7] (sourceLabel 8 0 2 v)
def fusedMap1155 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,9,10,11,12,5,6,7,8] (fusedLabel 8 0 2 v)
theorem sourceMap1155_checked : acceptsGraphIso
    (source (graph core1155) (root 8) 0 2) DegreeOneSmallSpectrum1185.graph sourceMap1155=true := by decide +kernel
theorem fusedMap1155_checked : acceptsGraphIso
    (fused (graph core1155) (root 8) 0 2) DegreeOneSmallSpectrum1509.graph fusedMap1155=true := by decide +kernel
theorem certified1155 : Certified (graph core1155) (root 8) 0 2 :=
  of_native_maps core1155 DegreeOneSmallSpectrum1185.graph DegreeOneSmallSpectrum1509.graph
    sourceMap1155 fusedMap1155 sourceMap1155_checked fusedMap1155_checked
    DegreeTwoThreeFiniteComparisons.comparison1155
#print axioms sourceMap1155_checked
#print axioms fusedMap1155_checked
#print axioms certified1155
def sourceMap1155swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 8 2 0 v)
def fusedMap1155swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,9,10,11,12,5,6,7,8] (fusedLabel 8 2 0 v)
theorem sourceMap1155swap_checked : acceptsGraphIso
    (source (graph core1155) (root 8) 2 0) DegreeOneSmallSpectrum1185.graph sourceMap1155swap=true := by decide +kernel
theorem fusedMap1155swap_checked : acceptsGraphIso
    (fused (graph core1155) (root 8) 2 0) DegreeOneSmallSpectrum1509.graph fusedMap1155swap=true := by decide +kernel
theorem certified1155swap : Certified (graph core1155) (root 8) 2 0 :=
  of_native_maps core1155 DegreeOneSmallSpectrum1185.graph DegreeOneSmallSpectrum1509.graph
    sourceMap1155swap fusedMap1155swap sourceMap1155swap_checked fusedMap1155swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1155
#print axioms sourceMap1155swap_checked
#print axioms fusedMap1155swap_checked
#print axioms certified1155swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
