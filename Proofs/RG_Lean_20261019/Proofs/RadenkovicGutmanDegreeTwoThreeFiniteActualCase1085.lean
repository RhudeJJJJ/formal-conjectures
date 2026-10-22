/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1085 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap1085 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (sourceLabel 7 0 2 v)
def fusedMap1085 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1085_checked : acceptsGraphIso
    (source (graph core1085) (root 7) 0 2) DegreeOneSmallSpectrum767.graph sourceMap1085=true := by decide +kernel
theorem fusedMap1085_checked : acceptsGraphIso
    (fused (graph core1085) (root 7) 0 2) DegreeOneSmallSpectrum459.graph fusedMap1085=true := by decide +kernel
theorem certified1085 : Certified (graph core1085) (root 7) 0 2 :=
  of_native_maps core1085 DegreeOneSmallSpectrum767.graph DegreeOneSmallSpectrum459.graph
    sourceMap1085 fusedMap1085 sourceMap1085_checked fusedMap1085_checked
    DegreeTwoThreeFiniteComparisons.comparison1085
#print axioms sourceMap1085_checked
#print axioms fusedMap1085_checked
#print axioms certified1085
def sourceMap1085swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7,11] (sourceLabel 7 2 0 v)
def fusedMap1085swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1085swap_checked : acceptsGraphIso
    (source (graph core1085) (root 7) 2 0) DegreeOneSmallSpectrum767.graph sourceMap1085swap=true := by decide +kernel
theorem fusedMap1085swap_checked : acceptsGraphIso
    (fused (graph core1085) (root 7) 2 0) DegreeOneSmallSpectrum459.graph fusedMap1085swap=true := by decide +kernel
theorem certified1085swap : Certified (graph core1085) (root 7) 2 0 :=
  of_native_maps core1085 DegreeOneSmallSpectrum767.graph DegreeOneSmallSpectrum459.graph
    sourceMap1085swap fusedMap1085swap sourceMap1085swap_checked fusedMap1085swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1085
#print axioms sourceMap1085swap_checked
#print axioms fusedMap1085swap_checked
#print axioms certified1085swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
