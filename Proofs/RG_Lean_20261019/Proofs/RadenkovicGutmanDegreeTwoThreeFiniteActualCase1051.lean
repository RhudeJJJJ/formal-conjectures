/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1051 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap1051 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 6 0 2 v)
def fusedMap1051 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1051_checked : acceptsGraphIso
    (source (graph core1051) (root 6) 0 2) DegreeOneSmallSpectrum330.graph sourceMap1051=true := by decide +kernel
theorem fusedMap1051_checked : acceptsGraphIso
    (fused (graph core1051) (root 6) 0 2) DegreeOneSmallSpectrum199.graph fusedMap1051=true := by decide +kernel
theorem certified1051 : Certified (graph core1051) (root 6) 0 2 :=
  of_native_maps core1051 DegreeOneSmallSpectrum330.graph DegreeOneSmallSpectrum199.graph
    sourceMap1051 fusedMap1051 sourceMap1051_checked fusedMap1051_checked
    DegreeTwoThreeFiniteComparisons.comparison1051
#print axioms sourceMap1051_checked
#print axioms fusedMap1051_checked
#print axioms certified1051
def sourceMap1051swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10] (sourceLabel 6 2 0 v)
def fusedMap1051swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1051swap_checked : acceptsGraphIso
    (source (graph core1051) (root 6) 2 0) DegreeOneSmallSpectrum330.graph sourceMap1051swap=true := by decide +kernel
theorem fusedMap1051swap_checked : acceptsGraphIso
    (fused (graph core1051) (root 6) 2 0) DegreeOneSmallSpectrum199.graph fusedMap1051swap=true := by decide +kernel
theorem certified1051swap : Certified (graph core1051) (root 6) 2 0 :=
  of_native_maps core1051 DegreeOneSmallSpectrum330.graph DegreeOneSmallSpectrum199.graph
    sourceMap1051swap fusedMap1051swap sourceMap1051swap_checked fusedMap1051swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1051
#print axioms sourceMap1051swap_checked
#print axioms fusedMap1051swap_checked
#print axioms certified1051swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
