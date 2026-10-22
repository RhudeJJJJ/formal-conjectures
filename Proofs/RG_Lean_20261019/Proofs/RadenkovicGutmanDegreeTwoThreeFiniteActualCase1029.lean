/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1029 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap1029 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,6,7,8,1,2,5,3,4] (sourceLabel 5 0 1 v)
def fusedMap1029 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,7,8,4,5,6] (fusedLabel 5 0 1 v)
theorem sourceMap1029_checked : acceptsGraphIso
    (source (graph core1029) (root 5) 0 1) DegreeOneSmallSpectrum053.graph sourceMap1029=true := by decide +kernel
theorem fusedMap1029_checked : acceptsGraphIso
    (fused (graph core1029) (root 5) 0 1) DegreeOneSmallSpectrum061.graph fusedMap1029=true := by decide +kernel
theorem certified1029 : Certified (graph core1029) (root 5) 0 1 :=
  of_native_maps core1029 DegreeOneSmallSpectrum053.graph DegreeOneSmallSpectrum061.graph
    sourceMap1029 fusedMap1029 sourceMap1029_checked fusedMap1029_checked
    DegreeTwoThreeFiniteComparisons.comparison1029
#print axioms sourceMap1029_checked
#print axioms fusedMap1029_checked
#print axioms certified1029
def sourceMap1029swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,6,7,8,1,2,3,4,5] (sourceLabel 5 1 0 v)
def fusedMap1029swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,7,8,4,5,6] (fusedLabel 5 1 0 v)
theorem sourceMap1029swap_checked : acceptsGraphIso
    (source (graph core1029) (root 5) 1 0) DegreeOneSmallSpectrum053.graph sourceMap1029swap=true := by decide +kernel
theorem fusedMap1029swap_checked : acceptsGraphIso
    (fused (graph core1029) (root 5) 1 0) DegreeOneSmallSpectrum061.graph fusedMap1029swap=true := by decide +kernel
theorem certified1029swap : Certified (graph core1029) (root 5) 1 0 :=
  of_native_maps core1029 DegreeOneSmallSpectrum053.graph DegreeOneSmallSpectrum061.graph
    sourceMap1029swap fusedMap1029swap sourceMap1029swap_checked fusedMap1029swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1029
#print axioms sourceMap1029swap_checked
#print axioms fusedMap1029swap_checked
#print axioms certified1029swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
