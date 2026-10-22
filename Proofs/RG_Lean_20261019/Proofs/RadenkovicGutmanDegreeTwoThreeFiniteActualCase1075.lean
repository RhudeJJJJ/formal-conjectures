/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1075 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap1075 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,4,5,6,1,2,3] (sourceLabel 7 0 2 v)
def fusedMap1075 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (fusedLabel 7 0 2 v)
theorem sourceMap1075_checked : acceptsGraphIso
    (source (graph core1075) (root 7) 0 2) DegreeOneSmallSpectrum570.graph sourceMap1075=true := by decide +kernel
theorem fusedMap1075_checked : acceptsGraphIso
    (fused (graph core1075) (root 7) 0 2) DegreeOneSmallSpectrum583.graph fusedMap1075=true := by decide +kernel
theorem certified1075 : Certified (graph core1075) (root 7) 0 2 :=
  of_native_maps core1075 DegreeOneSmallSpectrum570.graph DegreeOneSmallSpectrum583.graph
    sourceMap1075 fusedMap1075 sourceMap1075_checked fusedMap1075_checked
    DegreeTwoThreeFiniteComparisons.comparison1075
#print axioms sourceMap1075_checked
#print axioms fusedMap1075_checked
#print axioms certified1075
def sourceMap1075swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,4,5,1,2,3,6] (sourceLabel 7 2 0 v)
def fusedMap1075swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (fusedLabel 7 2 0 v)
theorem sourceMap1075swap_checked : acceptsGraphIso
    (source (graph core1075) (root 7) 2 0) DegreeOneSmallSpectrum570.graph sourceMap1075swap=true := by decide +kernel
theorem fusedMap1075swap_checked : acceptsGraphIso
    (fused (graph core1075) (root 7) 2 0) DegreeOneSmallSpectrum583.graph fusedMap1075swap=true := by decide +kernel
theorem certified1075swap : Certified (graph core1075) (root 7) 2 0 :=
  of_native_maps core1075 DegreeOneSmallSpectrum570.graph DegreeOneSmallSpectrum583.graph
    sourceMap1075swap fusedMap1075swap sourceMap1075swap_checked fusedMap1075swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1075
#print axioms sourceMap1075swap_checked
#print axioms fusedMap1075swap_checked
#print axioms certified1075swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
