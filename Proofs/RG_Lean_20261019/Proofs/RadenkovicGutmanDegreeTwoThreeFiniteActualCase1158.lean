/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1158 : Family 8 := level8.get ⟨190,by decide⟩
def sourceMap1158 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1158 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1158_checked : acceptsGraphIso
    (source (graph core1158) (root 8) 0 2) DegreeOneSmallSpectrum1553.graph sourceMap1158=true := by decide +kernel
theorem fusedMap1158_checked : acceptsGraphIso
    (fused (graph core1158) (root 8) 0 2) DegreeOneSmallSpectrum981.graph fusedMap1158=true := by decide +kernel
theorem certified1158 : Certified (graph core1158) (root 8) 0 2 :=
  of_native_maps core1158 DegreeOneSmallSpectrum1553.graph DegreeOneSmallSpectrum981.graph
    sourceMap1158 fusedMap1158 sourceMap1158_checked fusedMap1158_checked
    DegreeTwoThreeFiniteComparisons.comparison1158
#print axioms sourceMap1158_checked
#print axioms fusedMap1158_checked
#print axioms certified1158
def sourceMap1158swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1158swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1158swap_checked : acceptsGraphIso
    (source (graph core1158) (root 8) 2 0) DegreeOneSmallSpectrum1553.graph sourceMap1158swap=true := by decide +kernel
theorem fusedMap1158swap_checked : acceptsGraphIso
    (fused (graph core1158) (root 8) 2 0) DegreeOneSmallSpectrum981.graph fusedMap1158swap=true := by decide +kernel
theorem certified1158swap : Certified (graph core1158) (root 8) 2 0 :=
  of_native_maps core1158 DegreeOneSmallSpectrum1553.graph DegreeOneSmallSpectrum981.graph
    sourceMap1158swap fusedMap1158swap sourceMap1158swap_checked fusedMap1158swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1158
#print axioms sourceMap1158swap_checked
#print axioms fusedMap1158swap_checked
#print axioms certified1158swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
