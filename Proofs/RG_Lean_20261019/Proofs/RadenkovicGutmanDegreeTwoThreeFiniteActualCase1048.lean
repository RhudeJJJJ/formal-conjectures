/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1048 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap1048 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 6 0 2 v)
def fusedMap1048 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1048_checked : acceptsGraphIso
    (source (graph core1048) (root 6) 0 2) DegreeOneSmallSpectrum266.graph sourceMap1048=true := by decide +kernel
theorem fusedMap1048_checked : acceptsGraphIso
    (fused (graph core1048) (root 6) 0 2) DegreeOneSmallSpectrum171.graph fusedMap1048=true := by decide +kernel
theorem certified1048 : Certified (graph core1048) (root 6) 0 2 :=
  of_native_maps core1048 DegreeOneSmallSpectrum266.graph DegreeOneSmallSpectrum171.graph
    sourceMap1048 fusedMap1048 sourceMap1048_checked fusedMap1048_checked
    DegreeTwoThreeFiniteComparisons.comparison1048
#print axioms sourceMap1048_checked
#print axioms fusedMap1048_checked
#print axioms certified1048
def sourceMap1048swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10] (sourceLabel 6 2 0 v)
def fusedMap1048swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1048swap_checked : acceptsGraphIso
    (source (graph core1048) (root 6) 2 0) DegreeOneSmallSpectrum266.graph sourceMap1048swap=true := by decide +kernel
theorem fusedMap1048swap_checked : acceptsGraphIso
    (fused (graph core1048) (root 6) 2 0) DegreeOneSmallSpectrum171.graph fusedMap1048swap=true := by decide +kernel
theorem certified1048swap : Certified (graph core1048) (root 6) 2 0 :=
  of_native_maps core1048 DegreeOneSmallSpectrum266.graph DegreeOneSmallSpectrum171.graph
    sourceMap1048swap fusedMap1048swap sourceMap1048swap_checked fusedMap1048swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1048
#print axioms sourceMap1048swap_checked
#print axioms fusedMap1048swap_checked
#print axioms certified1048swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
