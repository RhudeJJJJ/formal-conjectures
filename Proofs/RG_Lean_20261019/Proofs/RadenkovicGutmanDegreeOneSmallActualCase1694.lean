/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1694 : Family 9 := level9.get ⟨459,by decide⟩
def sourceMap1694 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1694 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1694_checked : acceptsGraphIso
    (source (graph core1694) (root 9) 0 1) DegreeOneSmallSpectrum1957.graph sourceMap1694=true := by decide +kernel
theorem fusedMap1694_checked : acceptsGraphIso
    (fused (graph core1694) (root 9) 0 1) DegreeOneSmallSpectrum1395.graph fusedMap1694=true := by decide +kernel
theorem certified1694 : Certified (graph core1694) (root 9) 0 1 :=
  of_native_maps core1694 DegreeOneSmallSpectrum1957.graph DegreeOneSmallSpectrum1395.graph
    sourceMap1694 fusedMap1694 sourceMap1694_checked fusedMap1694_checked
    DegreeOneSmallComparisons.comparison1694
#print axioms sourceMap1694_checked
#print axioms fusedMap1694_checked
#print axioms certified1694
def sourceMap1694swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1694swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1694swap_checked : acceptsGraphIso
    (source (graph core1694) (root 9) 1 0) DegreeOneSmallSpectrum1957.graph sourceMap1694swap=true := by decide +kernel
theorem fusedMap1694swap_checked : acceptsGraphIso
    (fused (graph core1694) (root 9) 1 0) DegreeOneSmallSpectrum1395.graph fusedMap1694swap=true := by decide +kernel
theorem certified1694swap : Certified (graph core1694) (root 9) 1 0 :=
  of_native_maps core1694 DegreeOneSmallSpectrum1957.graph DegreeOneSmallSpectrum1395.graph
    sourceMap1694swap fusedMap1694swap sourceMap1694swap_checked fusedMap1694swap_checked
    DegreeOneSmallComparisons.comparison1694
#print axioms sourceMap1694swap_checked
#print axioms fusedMap1694swap_checked
#print axioms certified1694swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
