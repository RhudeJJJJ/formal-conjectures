/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1071 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap1071 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1071 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1071_checked : acceptsGraphIso
    (source (graph core1071) (root 7) 0 2) DegreeOneSmallSpectrum548.graph sourceMap1071=true := by decide +kernel
theorem fusedMap1071_checked : acceptsGraphIso
    (fused (graph core1071) (root 7) 0 2) DegreeOneSmallSpectrum550.graph fusedMap1071=true := by decide +kernel
theorem certified1071 : Certified (graph core1071) (root 7) 0 2 :=
  of_native_maps core1071 DegreeOneSmallSpectrum548.graph DegreeOneSmallSpectrum550.graph
    sourceMap1071 fusedMap1071 sourceMap1071_checked fusedMap1071_checked
    DegreeTwoThreeFiniteComparisons.comparison1071
#print axioms sourceMap1071_checked
#print axioms fusedMap1071_checked
#print axioms certified1071
def sourceMap1071swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1071swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1071swap_checked : acceptsGraphIso
    (source (graph core1071) (root 7) 2 0) DegreeOneSmallSpectrum548.graph sourceMap1071swap=true := by decide +kernel
theorem fusedMap1071swap_checked : acceptsGraphIso
    (fused (graph core1071) (root 7) 2 0) DegreeOneSmallSpectrum550.graph fusedMap1071swap=true := by decide +kernel
theorem certified1071swap : Certified (graph core1071) (root 7) 2 0 :=
  of_native_maps core1071 DegreeOneSmallSpectrum548.graph DegreeOneSmallSpectrum550.graph
    sourceMap1071swap fusedMap1071swap sourceMap1071swap_checked fusedMap1071swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1071
#print axioms sourceMap1071swap_checked
#print axioms fusedMap1071swap_checked
#print axioms certified1071swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
