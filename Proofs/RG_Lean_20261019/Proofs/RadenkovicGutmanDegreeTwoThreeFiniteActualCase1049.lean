/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1049 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap1049 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 6 0 2 v)
def fusedMap1049 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1049_checked : acceptsGraphIso
    (source (graph core1049) (root 6) 0 2) DegreeOneSmallSpectrum300.graph sourceMap1049=true := by decide +kernel
theorem fusedMap1049_checked : acceptsGraphIso
    (fused (graph core1049) (root 6) 0 2) DegreeOneSmallSpectrum178.graph fusedMap1049=true := by decide +kernel
theorem certified1049 : Certified (graph core1049) (root 6) 0 2 :=
  of_native_maps core1049 DegreeOneSmallSpectrum300.graph DegreeOneSmallSpectrum178.graph
    sourceMap1049 fusedMap1049 sourceMap1049_checked fusedMap1049_checked
    DegreeTwoThreeFiniteComparisons.comparison1049
#print axioms sourceMap1049_checked
#print axioms fusedMap1049_checked
#print axioms certified1049
def sourceMap1049swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10] (sourceLabel 6 2 0 v)
def fusedMap1049swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1049swap_checked : acceptsGraphIso
    (source (graph core1049) (root 6) 2 0) DegreeOneSmallSpectrum300.graph sourceMap1049swap=true := by decide +kernel
theorem fusedMap1049swap_checked : acceptsGraphIso
    (fused (graph core1049) (root 6) 2 0) DegreeOneSmallSpectrum178.graph fusedMap1049swap=true := by decide +kernel
theorem certified1049swap : Certified (graph core1049) (root 6) 2 0 :=
  of_native_maps core1049 DegreeOneSmallSpectrum300.graph DegreeOneSmallSpectrum178.graph
    sourceMap1049swap fusedMap1049swap sourceMap1049swap_checked fusedMap1049swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1049
#print axioms sourceMap1049swap_checked
#print axioms fusedMap1049swap_checked
#print axioms certified1049swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
