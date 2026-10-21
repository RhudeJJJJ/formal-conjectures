/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1730 : Family 9 := level9.get ⟨546,by decide⟩
def sourceMap1730 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1730 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1730_checked : acceptsGraphIso
    (source (graph core1730) (root 9) 0 1) DegreeOneSmallSpectrum1539.graph sourceMap1730=true := by decide +kernel
theorem fusedMap1730_checked : acceptsGraphIso
    (fused (graph core1730) (root 9) 0 1) DegreeOneSmallSpectrum1540.graph fusedMap1730=true := by decide +kernel
theorem certified1730 : Certified (graph core1730) (root 9) 0 1 :=
  of_native_maps core1730 DegreeOneSmallSpectrum1539.graph DegreeOneSmallSpectrum1540.graph
    sourceMap1730 fusedMap1730 sourceMap1730_checked fusedMap1730_checked
    DegreeOneSmallComparisons.comparison1730
#print axioms sourceMap1730_checked
#print axioms fusedMap1730_checked
#print axioms certified1730
def sourceMap1730swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1730swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1730swap_checked : acceptsGraphIso
    (source (graph core1730) (root 9) 1 0) DegreeOneSmallSpectrum1539.graph sourceMap1730swap=true := by decide +kernel
theorem fusedMap1730swap_checked : acceptsGraphIso
    (fused (graph core1730) (root 9) 1 0) DegreeOneSmallSpectrum1540.graph fusedMap1730swap=true := by decide +kernel
theorem certified1730swap : Certified (graph core1730) (root 9) 1 0 :=
  of_native_maps core1730 DegreeOneSmallSpectrum1539.graph DegreeOneSmallSpectrum1540.graph
    sourceMap1730swap fusedMap1730swap sourceMap1730swap_checked fusedMap1730swap_checked
    DegreeOneSmallComparisons.comparison1730
#print axioms sourceMap1730swap_checked
#print axioms fusedMap1730swap_checked
#print axioms certified1730swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
