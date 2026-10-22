/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1090 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap1090 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap1090 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1090_checked : acceptsGraphIso
    (source (graph core1090) (root 7) 0 2) DegreeOneSmallSpectrum816.graph sourceMap1090=true := by decide +kernel
theorem fusedMap1090_checked : acceptsGraphIso
    (fused (graph core1090) (root 7) 0 2) DegreeOneSmallSpectrum535.graph fusedMap1090=true := by decide +kernel
theorem certified1090 : Certified (graph core1090) (root 7) 0 2 :=
  of_native_maps core1090 DegreeOneSmallSpectrum816.graph DegreeOneSmallSpectrum535.graph
    sourceMap1090 fusedMap1090 sourceMap1090_checked fusedMap1090_checked
    DegreeTwoThreeFiniteComparisons.comparison1090
#print axioms sourceMap1090_checked
#print axioms fusedMap1090_checked
#print axioms certified1090
def sourceMap1090swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap1090swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1090swap_checked : acceptsGraphIso
    (source (graph core1090) (root 7) 2 0) DegreeOneSmallSpectrum816.graph sourceMap1090swap=true := by decide +kernel
theorem fusedMap1090swap_checked : acceptsGraphIso
    (fused (graph core1090) (root 7) 2 0) DegreeOneSmallSpectrum535.graph fusedMap1090swap=true := by decide +kernel
theorem certified1090swap : Certified (graph core1090) (root 7) 2 0 :=
  of_native_maps core1090 DegreeOneSmallSpectrum816.graph DegreeOneSmallSpectrum535.graph
    sourceMap1090swap fusedMap1090swap sourceMap1090swap_checked fusedMap1090swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1090
#print axioms sourceMap1090swap_checked
#print axioms fusedMap1090swap_checked
#print axioms certified1090swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
