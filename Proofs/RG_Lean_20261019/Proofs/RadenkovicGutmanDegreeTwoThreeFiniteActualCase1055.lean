/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1055 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap1055 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (sourceLabel 6 0 2 v)
def fusedMap1055 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1055_checked : acceptsGraphIso
    (source (graph core1055) (root 6) 0 2) DegreeOneSmallSpectrum347.graph sourceMap1055=true := by decide +kernel
theorem fusedMap1055_checked : acceptsGraphIso
    (fused (graph core1055) (root 6) 0 2) DegreeOneSmallSpectrum219.graph fusedMap1055=true := by decide +kernel
theorem certified1055 : Certified (graph core1055) (root 6) 0 2 :=
  of_native_maps core1055 DegreeOneSmallSpectrum347.graph DegreeOneSmallSpectrum219.graph
    sourceMap1055 fusedMap1055 sourceMap1055_checked fusedMap1055_checked
    DegreeTwoThreeFiniteComparisons.comparison1055
#print axioms sourceMap1055_checked
#print axioms fusedMap1055_checked
#print axioms certified1055
def sourceMap1055swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,4,5,6,10] (sourceLabel 6 2 0 v)
def fusedMap1055swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1055swap_checked : acceptsGraphIso
    (source (graph core1055) (root 6) 2 0) DegreeOneSmallSpectrum347.graph sourceMap1055swap=true := by decide +kernel
theorem fusedMap1055swap_checked : acceptsGraphIso
    (fused (graph core1055) (root 6) 2 0) DegreeOneSmallSpectrum219.graph fusedMap1055swap=true := by decide +kernel
theorem certified1055swap : Certified (graph core1055) (root 6) 2 0 :=
  of_native_maps core1055 DegreeOneSmallSpectrum347.graph DegreeOneSmallSpectrum219.graph
    sourceMap1055swap fusedMap1055swap sourceMap1055swap_checked fusedMap1055swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1055
#print axioms sourceMap1055swap_checked
#print axioms fusedMap1055swap_checked
#print axioms certified1055swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
