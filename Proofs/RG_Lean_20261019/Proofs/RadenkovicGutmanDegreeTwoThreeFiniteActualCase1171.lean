/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1171 : Family 8 := level8.get ⟨218,by decide⟩
def sourceMap1171 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1171 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1171_checked : acceptsGraphIso
    (source (graph core1171) (root 8) 0 2) DegreeOneSmallSpectrum1833.graph sourceMap1171=true := by decide +kernel
theorem fusedMap1171_checked : acceptsGraphIso
    (fused (graph core1171) (root 8) 0 2) DegreeOneSmallSpectrum1136.graph fusedMap1171=true := by decide +kernel
theorem certified1171 : Certified (graph core1171) (root 8) 0 2 :=
  of_native_maps core1171 DegreeOneSmallSpectrum1833.graph DegreeOneSmallSpectrum1136.graph
    sourceMap1171 fusedMap1171 sourceMap1171_checked fusedMap1171_checked
    DegreeTwoThreeFiniteComparisons.comparison1171
#print axioms sourceMap1171_checked
#print axioms fusedMap1171_checked
#print axioms certified1171
def sourceMap1171swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1171swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1171swap_checked : acceptsGraphIso
    (source (graph core1171) (root 8) 2 0) DegreeOneSmallSpectrum1833.graph sourceMap1171swap=true := by decide +kernel
theorem fusedMap1171swap_checked : acceptsGraphIso
    (fused (graph core1171) (root 8) 2 0) DegreeOneSmallSpectrum1136.graph fusedMap1171swap=true := by decide +kernel
theorem certified1171swap : Certified (graph core1171) (root 8) 2 0 :=
  of_native_maps core1171 DegreeOneSmallSpectrum1833.graph DegreeOneSmallSpectrum1136.graph
    sourceMap1171swap fusedMap1171swap sourceMap1171swap_checked fusedMap1171swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1171
#print axioms sourceMap1171swap_checked
#print axioms fusedMap1171swap_checked
#print axioms certified1171swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
