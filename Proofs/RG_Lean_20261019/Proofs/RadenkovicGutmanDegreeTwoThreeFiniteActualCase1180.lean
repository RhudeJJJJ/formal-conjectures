/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1180 : Family 8 := level8.get ⟨237,by decide⟩
def sourceMap1180 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8] (sourceLabel 8 0 2 v)
def fusedMap1180 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1180_checked : acceptsGraphIso
    (source (graph core1180) (root 8) 0 2) DegreeOneSmallSpectrum1928.graph sourceMap1180=true := by decide +kernel
theorem fusedMap1180_checked : acceptsGraphIso
    (fused (graph core1180) (root 8) 0 2) DegreeOneSmallSpectrum1315.graph fusedMap1180=true := by decide +kernel
theorem certified1180 : Certified (graph core1180) (root 8) 0 2 :=
  of_native_maps core1180 DegreeOneSmallSpectrum1928.graph DegreeOneSmallSpectrum1315.graph
    sourceMap1180 fusedMap1180 sourceMap1180_checked fusedMap1180_checked
    DegreeTwoThreeFiniteComparisons.comparison1180
#print axioms sourceMap1180_checked
#print axioms fusedMap1180_checked
#print axioms certified1180
def sourceMap1180swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8,12] (sourceLabel 8 2 0 v)
def fusedMap1180swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1180swap_checked : acceptsGraphIso
    (source (graph core1180) (root 8) 2 0) DegreeOneSmallSpectrum1928.graph sourceMap1180swap=true := by decide +kernel
theorem fusedMap1180swap_checked : acceptsGraphIso
    (fused (graph core1180) (root 8) 2 0) DegreeOneSmallSpectrum1315.graph fusedMap1180swap=true := by decide +kernel
theorem certified1180swap : Certified (graph core1180) (root 8) 2 0 :=
  of_native_maps core1180 DegreeOneSmallSpectrum1928.graph DegreeOneSmallSpectrum1315.graph
    sourceMap1180swap fusedMap1180swap sourceMap1180swap_checked fusedMap1180swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1180
#print axioms sourceMap1180swap_checked
#print axioms fusedMap1180swap_checked
#print axioms certified1180swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
