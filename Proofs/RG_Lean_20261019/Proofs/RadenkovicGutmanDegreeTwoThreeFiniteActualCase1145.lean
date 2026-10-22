/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1145 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap1145 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 8 0 2 v)
def fusedMap1145 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 0 2 v)
theorem sourceMap1145_checked : acceptsGraphIso
    (source (graph core1145) (root 8) 0 2) DegreeOneSmallSpectrum1441.graph sourceMap1145=true := by decide +kernel
theorem fusedMap1145_checked : acceptsGraphIso
    (fused (graph core1145) (root 8) 0 2) DegreeOneSmallSpectrum1453.graph fusedMap1145=true := by decide +kernel
theorem certified1145 : Certified (graph core1145) (root 8) 0 2 :=
  of_native_maps core1145 DegreeOneSmallSpectrum1441.graph DegreeOneSmallSpectrum1453.graph
    sourceMap1145 fusedMap1145 sourceMap1145_checked fusedMap1145_checked
    DegreeTwoThreeFiniteComparisons.comparison1145
#print axioms sourceMap1145_checked
#print axioms fusedMap1145_checked
#print axioms certified1145
def sourceMap1145swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8,12] (sourceLabel 8 2 0 v)
def fusedMap1145swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 2 0 v)
theorem sourceMap1145swap_checked : acceptsGraphIso
    (source (graph core1145) (root 8) 2 0) DegreeOneSmallSpectrum1441.graph sourceMap1145swap=true := by decide +kernel
theorem fusedMap1145swap_checked : acceptsGraphIso
    (fused (graph core1145) (root 8) 2 0) DegreeOneSmallSpectrum1453.graph fusedMap1145swap=true := by decide +kernel
theorem certified1145swap : Certified (graph core1145) (root 8) 2 0 :=
  of_native_maps core1145 DegreeOneSmallSpectrum1441.graph DegreeOneSmallSpectrum1453.graph
    sourceMap1145swap fusedMap1145swap sourceMap1145swap_checked fusedMap1145swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1145
#print axioms sourceMap1145swap_checked
#print axioms fusedMap1145swap_checked
#print axioms certified1145swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
