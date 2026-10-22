/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1031 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap1031 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,8,6,7] (sourceLabel 5 0 1 v)
def fusedMap1031 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap1031_checked : acceptsGraphIso
    (source (graph core1031) (root 5) 0 1) DegreeOneSmallSpectrum071.graph sourceMap1031=true := by decide +kernel
theorem fusedMap1031_checked : acceptsGraphIso
    (fused (graph core1031) (root 5) 0 1) DegreeOneSmallSpectrum043.graph fusedMap1031=true := by decide +kernel
theorem certified1031 : Certified (graph core1031) (root 5) 0 1 :=
  of_native_maps core1031 DegreeOneSmallSpectrum071.graph DegreeOneSmallSpectrum043.graph
    sourceMap1031 fusedMap1031 sourceMap1031_checked fusedMap1031_checked
    DegreeTwoThreeFiniteComparisons.comparison1031
#print axioms sourceMap1031_checked
#print axioms fusedMap1031_checked
#print axioms certified1031
def sourceMap1031swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 5 1 0 v)
def fusedMap1031swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap1031swap_checked : acceptsGraphIso
    (source (graph core1031) (root 5) 1 0) DegreeOneSmallSpectrum071.graph sourceMap1031swap=true := by decide +kernel
theorem fusedMap1031swap_checked : acceptsGraphIso
    (fused (graph core1031) (root 5) 1 0) DegreeOneSmallSpectrum043.graph fusedMap1031swap=true := by decide +kernel
theorem certified1031swap : Certified (graph core1031) (root 5) 1 0 :=
  of_native_maps core1031 DegreeOneSmallSpectrum071.graph DegreeOneSmallSpectrum043.graph
    sourceMap1031swap fusedMap1031swap sourceMap1031swap_checked fusedMap1031swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1031
#print axioms sourceMap1031swap_checked
#print axioms fusedMap1031swap_checked
#print axioms certified1031swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
