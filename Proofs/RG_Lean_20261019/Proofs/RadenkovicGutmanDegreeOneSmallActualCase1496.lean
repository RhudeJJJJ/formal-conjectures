/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1496 : Family 9 := level9.get ⟨227,by decide⟩
def sourceMap1496 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1496 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1496_checked : acceptsGraphIso
    (source (graph core1496) (root 9) 0 1) DegreeOneSmallSpectrum1401.graph sourceMap1496=true := by decide +kernel
theorem fusedMap1496_checked : acceptsGraphIso
    (fused (graph core1496) (root 9) 0 1) DegreeOneSmallSpectrum1403.graph fusedMap1496=true := by decide +kernel
theorem certified1496 : Certified (graph core1496) (root 9) 0 1 :=
  of_native_maps core1496 DegreeOneSmallSpectrum1401.graph DegreeOneSmallSpectrum1403.graph
    sourceMap1496 fusedMap1496 sourceMap1496_checked fusedMap1496_checked
    DegreeOneSmallComparisons.comparison1496
#print axioms sourceMap1496_checked
#print axioms fusedMap1496_checked
#print axioms certified1496
def sourceMap1496swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1496swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1496swap_checked : acceptsGraphIso
    (source (graph core1496) (root 9) 1 0) DegreeOneSmallSpectrum1401.graph sourceMap1496swap=true := by decide +kernel
theorem fusedMap1496swap_checked : acceptsGraphIso
    (fused (graph core1496) (root 9) 1 0) DegreeOneSmallSpectrum1403.graph fusedMap1496swap=true := by decide +kernel
theorem certified1496swap : Certified (graph core1496) (root 9) 1 0 :=
  of_native_maps core1496 DegreeOneSmallSpectrum1401.graph DegreeOneSmallSpectrum1403.graph
    sourceMap1496swap fusedMap1496swap sourceMap1496swap_checked fusedMap1496swap_checked
    DegreeOneSmallComparisons.comparison1496
#print axioms sourceMap1496swap_checked
#print axioms fusedMap1496swap_checked
#print axioms certified1496swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
