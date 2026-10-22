/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1184 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap1184 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8] (sourceLabel 8 0 2 v)
def fusedMap1184 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1184_checked : acceptsGraphIso
    (source (graph core1184) (root 8) 0 2) DegreeOneSmallSpectrum1952.graph sourceMap1184=true := by decide +kernel
theorem fusedMap1184_checked : acceptsGraphIso
    (fused (graph core1184) (root 8) 0 2) DegreeOneSmallSpectrum1366.graph fusedMap1184=true := by decide +kernel
theorem certified1184 : Certified (graph core1184) (root 8) 0 2 :=
  of_native_maps core1184 DegreeOneSmallSpectrum1952.graph DegreeOneSmallSpectrum1366.graph
    sourceMap1184 fusedMap1184 sourceMap1184_checked fusedMap1184_checked
    DegreeTwoThreeFiniteComparisons.comparison1184
#print axioms sourceMap1184_checked
#print axioms fusedMap1184_checked
#print axioms certified1184
def sourceMap1184swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8,12] (sourceLabel 8 2 0 v)
def fusedMap1184swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1184swap_checked : acceptsGraphIso
    (source (graph core1184) (root 8) 2 0) DegreeOneSmallSpectrum1952.graph sourceMap1184swap=true := by decide +kernel
theorem fusedMap1184swap_checked : acceptsGraphIso
    (fused (graph core1184) (root 8) 2 0) DegreeOneSmallSpectrum1366.graph fusedMap1184swap=true := by decide +kernel
theorem certified1184swap : Certified (graph core1184) (root 8) 2 0 :=
  of_native_maps core1184 DegreeOneSmallSpectrum1952.graph DegreeOneSmallSpectrum1366.graph
    sourceMap1184swap fusedMap1184swap sourceMap1184swap_checked fusedMap1184swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1184
#print axioms sourceMap1184swap_checked
#print axioms fusedMap1184swap_checked
#print axioms certified1184swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
