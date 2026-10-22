/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1156 : Family 8 := level8.get ⟨181,by decide⟩
def sourceMap1156 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,8,5,6,7] (sourceLabel 8 0 2 v)
def fusedMap1156 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,9,10,11,12,5,6,7,8] (fusedLabel 8 0 2 v)
theorem sourceMap1156_checked : acceptsGraphIso
    (source (graph core1156) (root 8) 0 2) DegreeOneSmallSpectrum1395.graph sourceMap1156=true := by decide +kernel
theorem fusedMap1156_checked : acceptsGraphIso
    (fused (graph core1156) (root 8) 0 2) DegreeOneSmallSpectrum1510.graph fusedMap1156=true := by decide +kernel
theorem certified1156 : Certified (graph core1156) (root 8) 0 2 :=
  of_native_maps core1156 DegreeOneSmallSpectrum1395.graph DegreeOneSmallSpectrum1510.graph
    sourceMap1156 fusedMap1156 sourceMap1156_checked fusedMap1156_checked
    DegreeTwoThreeFiniteComparisons.comparison1156
#print axioms sourceMap1156_checked
#print axioms fusedMap1156_checked
#print axioms certified1156
def sourceMap1156swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 8 2 0 v)
def fusedMap1156swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,9,10,11,12,5,6,7,8] (fusedLabel 8 2 0 v)
theorem sourceMap1156swap_checked : acceptsGraphIso
    (source (graph core1156) (root 8) 2 0) DegreeOneSmallSpectrum1395.graph sourceMap1156swap=true := by decide +kernel
theorem fusedMap1156swap_checked : acceptsGraphIso
    (fused (graph core1156) (root 8) 2 0) DegreeOneSmallSpectrum1510.graph fusedMap1156swap=true := by decide +kernel
theorem certified1156swap : Certified (graph core1156) (root 8) 2 0 :=
  of_native_maps core1156 DegreeOneSmallSpectrum1395.graph DegreeOneSmallSpectrum1510.graph
    sourceMap1156swap fusedMap1156swap sourceMap1156swap_checked fusedMap1156swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1156
#print axioms sourceMap1156swap_checked
#print axioms fusedMap1156swap_checked
#print axioms certified1156swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
