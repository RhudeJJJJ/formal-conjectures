/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1040 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap1040 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,7,8,9,4,5,6] (sourceLabel 5 0 2 v)
def fusedMap1040 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap1040_checked : acceptsGraphIso
    (source (graph core1040) (root 5) 0 2) DegreeOneSmallSpectrum148.graph sourceMap1040=true := by decide +kernel
theorem fusedMap1040_checked : acceptsGraphIso
    (fused (graph core1040) (root 5) 0 2) DegreeOneSmallSpectrum087.graph fusedMap1040=true := by decide +kernel
theorem certified1040 : Certified (graph core1040) (root 5) 0 2 :=
  of_native_maps core1040 DegreeOneSmallSpectrum148.graph DegreeOneSmallSpectrum087.graph
    sourceMap1040 fusedMap1040 sourceMap1040_checked fusedMap1040_checked
    DegreeTwoThreeFiniteComparisons.comparison1040
#print axioms sourceMap1040_checked
#print axioms fusedMap1040_checked
#print axioms certified1040
def sourceMap1040swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,7,8,4,5,6,9] (sourceLabel 5 2 0 v)
def fusedMap1040swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap1040swap_checked : acceptsGraphIso
    (source (graph core1040) (root 5) 2 0) DegreeOneSmallSpectrum148.graph sourceMap1040swap=true := by decide +kernel
theorem fusedMap1040swap_checked : acceptsGraphIso
    (fused (graph core1040) (root 5) 2 0) DegreeOneSmallSpectrum087.graph fusedMap1040swap=true := by decide +kernel
theorem certified1040swap : Certified (graph core1040) (root 5) 2 0 :=
  of_native_maps core1040 DegreeOneSmallSpectrum148.graph DegreeOneSmallSpectrum087.graph
    sourceMap1040swap fusedMap1040swap sourceMap1040swap_checked fusedMap1040swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1040
#print axioms sourceMap1040swap_checked
#print axioms fusedMap1040swap_checked
#print axioms certified1040swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
