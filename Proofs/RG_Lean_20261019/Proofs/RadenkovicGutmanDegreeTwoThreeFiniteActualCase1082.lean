/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1082 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap1082 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1082 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1082_checked : acceptsGraphIso
    (source (graph core1082) (root 7) 0 2) DegreeOneSmallSpectrum728.graph sourceMap1082=true := by decide +kernel
theorem fusedMap1082_checked : acceptsGraphIso
    (fused (graph core1082) (root 7) 0 2) DegreeOneSmallSpectrum436.graph fusedMap1082=true := by decide +kernel
theorem certified1082 : Certified (graph core1082) (root 7) 0 2 :=
  of_native_maps core1082 DegreeOneSmallSpectrum728.graph DegreeOneSmallSpectrum436.graph
    sourceMap1082 fusedMap1082 sourceMap1082_checked fusedMap1082_checked
    DegreeTwoThreeFiniteComparisons.comparison1082
#print axioms sourceMap1082_checked
#print axioms fusedMap1082_checked
#print axioms certified1082
def sourceMap1082swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1082swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1082swap_checked : acceptsGraphIso
    (source (graph core1082) (root 7) 2 0) DegreeOneSmallSpectrum728.graph sourceMap1082swap=true := by decide +kernel
theorem fusedMap1082swap_checked : acceptsGraphIso
    (fused (graph core1082) (root 7) 2 0) DegreeOneSmallSpectrum436.graph fusedMap1082swap=true := by decide +kernel
theorem certified1082swap : Certified (graph core1082) (root 7) 2 0 :=
  of_native_maps core1082 DegreeOneSmallSpectrum728.graph DegreeOneSmallSpectrum436.graph
    sourceMap1082swap fusedMap1082swap sourceMap1082swap_checked fusedMap1082swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1082
#print axioms sourceMap1082swap_checked
#print axioms fusedMap1082swap_checked
#print axioms certified1082swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
