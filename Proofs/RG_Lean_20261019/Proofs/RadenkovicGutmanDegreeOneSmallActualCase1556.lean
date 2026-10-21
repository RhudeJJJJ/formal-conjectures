/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1556 : Family 9 := level9.get ⟨288,by decide⟩
def sourceMap1556 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (sourceLabel 9 0 1 v)
def fusedMap1556 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1556_checked : acceptsGraphIso
    (source (graph core1556) (root 9) 0 1) DegreeOneSmallSpectrum1184.graph sourceMap1556=true := by decide +kernel
theorem fusedMap1556_checked : acceptsGraphIso
    (fused (graph core1556) (root 9) 0 1) DegreeOneSmallSpectrum1509.graph fusedMap1556=true := by decide +kernel
theorem certified1556 : Certified (graph core1556) (root 9) 0 1 :=
  of_native_maps core1556 DegreeOneSmallSpectrum1184.graph DegreeOneSmallSpectrum1509.graph
    sourceMap1556 fusedMap1556 sourceMap1556_checked fusedMap1556_checked
    DegreeOneSmallComparisons.comparison1556
#print axioms sourceMap1556_checked
#print axioms fusedMap1556_checked
#print axioms certified1556
def sourceMap1556swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,6,7,8] (sourceLabel 9 1 0 v)
def fusedMap1556swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1556swap_checked : acceptsGraphIso
    (source (graph core1556) (root 9) 1 0) DegreeOneSmallSpectrum1184.graph sourceMap1556swap=true := by decide +kernel
theorem fusedMap1556swap_checked : acceptsGraphIso
    (fused (graph core1556) (root 9) 1 0) DegreeOneSmallSpectrum1509.graph fusedMap1556swap=true := by decide +kernel
theorem certified1556swap : Certified (graph core1556) (root 9) 1 0 :=
  of_native_maps core1556 DegreeOneSmallSpectrum1184.graph DegreeOneSmallSpectrum1509.graph
    sourceMap1556swap fusedMap1556swap sourceMap1556swap_checked fusedMap1556swap_checked
    DegreeOneSmallComparisons.comparison1556
#print axioms sourceMap1556swap_checked
#print axioms fusedMap1556swap_checked
#print axioms certified1556swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
