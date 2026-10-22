/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1034 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap1034 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,7,8,4,5,6] (sourceLabel 4 0 2 v)
def fusedMap1034 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap1034_checked : acceptsGraphIso
    (source (graph core1034) (root 4) 0 2) DegreeOneSmallSpectrum062.graph sourceMap1034=true := by decide +kernel
theorem fusedMap1034_checked : acceptsGraphIso
    (fused (graph core1034) (root 4) 0 2) DegreeOneSmallSpectrum036.graph fusedMap1034=true := by decide +kernel
theorem certified1034 : Certified (graph core1034) (root 4) 0 2 :=
  of_native_maps core1034 DegreeOneSmallSpectrum062.graph DegreeOneSmallSpectrum036.graph
    sourceMap1034 fusedMap1034 sourceMap1034_checked fusedMap1034_checked
    DegreeTwoThreeFiniteComparisons.comparison1034
#print axioms sourceMap1034_checked
#print axioms fusedMap1034_checked
#print axioms certified1034
def sourceMap1034swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,7,4,5,6,8] (sourceLabel 4 2 0 v)
def fusedMap1034swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap1034swap_checked : acceptsGraphIso
    (source (graph core1034) (root 4) 2 0) DegreeOneSmallSpectrum062.graph sourceMap1034swap=true := by decide +kernel
theorem fusedMap1034swap_checked : acceptsGraphIso
    (fused (graph core1034) (root 4) 2 0) DegreeOneSmallSpectrum036.graph fusedMap1034swap=true := by decide +kernel
theorem certified1034swap : Certified (graph core1034) (root 4) 2 0 :=
  of_native_maps core1034 DegreeOneSmallSpectrum062.graph DegreeOneSmallSpectrum036.graph
    sourceMap1034swap fusedMap1034swap sourceMap1034swap_checked fusedMap1034swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1034
#print axioms sourceMap1034swap_checked
#print axioms fusedMap1034swap_checked
#print axioms certified1034swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
