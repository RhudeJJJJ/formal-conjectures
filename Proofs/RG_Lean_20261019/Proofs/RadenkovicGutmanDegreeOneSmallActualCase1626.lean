/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1626 : Family 9 := level9.get ⟨367,by decide⟩
def sourceMap1626 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1626 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1626_checked : acceptsGraphIso
    (source (graph core1626) (root 9) 0 1) DegreeOneSmallSpectrum1791.graph sourceMap1626=true := by decide +kernel
theorem fusedMap1626_checked : acceptsGraphIso
    (fused (graph core1626) (root 9) 0 1) DegreeOneSmallSpectrum1114.graph fusedMap1626=true := by decide +kernel
theorem certified1626 : Certified (graph core1626) (root 9) 0 1 :=
  of_native_maps core1626 DegreeOneSmallSpectrum1791.graph DegreeOneSmallSpectrum1114.graph
    sourceMap1626 fusedMap1626 sourceMap1626_checked fusedMap1626_checked
    DegreeOneSmallComparisons.comparison1626
#print axioms sourceMap1626_checked
#print axioms fusedMap1626_checked
#print axioms certified1626
def sourceMap1626swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1626swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1626swap_checked : acceptsGraphIso
    (source (graph core1626) (root 9) 1 0) DegreeOneSmallSpectrum1791.graph sourceMap1626swap=true := by decide +kernel
theorem fusedMap1626swap_checked : acceptsGraphIso
    (fused (graph core1626) (root 9) 1 0) DegreeOneSmallSpectrum1114.graph fusedMap1626swap=true := by decide +kernel
theorem certified1626swap : Certified (graph core1626) (root 9) 1 0 :=
  of_native_maps core1626 DegreeOneSmallSpectrum1791.graph DegreeOneSmallSpectrum1114.graph
    sourceMap1626swap fusedMap1626swap sourceMap1626swap_checked fusedMap1626swap_checked
    DegreeOneSmallComparisons.comparison1626
#print axioms sourceMap1626swap_checked
#print axioms fusedMap1626swap_checked
#print axioms certified1626swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
