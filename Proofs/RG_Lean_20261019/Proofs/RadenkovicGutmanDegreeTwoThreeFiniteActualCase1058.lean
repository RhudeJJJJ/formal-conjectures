/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1058 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap1058 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap1058 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1058_checked : acceptsGraphIso
    (source (graph core1058) (root 6) 0 2) DegreeOneSmallSpectrum267.graph sourceMap1058=true := by decide +kernel
theorem fusedMap1058_checked : acceptsGraphIso
    (fused (graph core1058) (root 6) 0 2) DegreeOneSmallSpectrum270.graph fusedMap1058=true := by decide +kernel
theorem certified1058 : Certified (graph core1058) (root 6) 0 2 :=
  of_native_maps core1058 DegreeOneSmallSpectrum267.graph DegreeOneSmallSpectrum270.graph
    sourceMap1058 fusedMap1058 sourceMap1058_checked fusedMap1058_checked
    DegreeTwoThreeFiniteComparisons.comparison1058
#print axioms sourceMap1058_checked
#print axioms fusedMap1058_checked
#print axioms certified1058
def sourceMap1058swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap1058swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1058swap_checked : acceptsGraphIso
    (source (graph core1058) (root 6) 2 0) DegreeOneSmallSpectrum267.graph sourceMap1058swap=true := by decide +kernel
theorem fusedMap1058swap_checked : acceptsGraphIso
    (fused (graph core1058) (root 6) 2 0) DegreeOneSmallSpectrum270.graph fusedMap1058swap=true := by decide +kernel
theorem certified1058swap : Certified (graph core1058) (root 6) 2 0 :=
  of_native_maps core1058 DegreeOneSmallSpectrum267.graph DegreeOneSmallSpectrum270.graph
    sourceMap1058swap fusedMap1058swap sourceMap1058swap_checked fusedMap1058swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1058
#print axioms sourceMap1058swap_checked
#print axioms fusedMap1058swap_checked
#print axioms certified1058swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
