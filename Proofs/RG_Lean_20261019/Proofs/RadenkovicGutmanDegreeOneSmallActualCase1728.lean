/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1728 : Family 9 := level9.get ⟨545,by decide⟩
def sourceMap1728 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1728 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1728_checked : acceptsGraphIso
    (source (graph core1728) (root 9) 0 1) DegreeOneSmallSpectrum1535.graph sourceMap1728=true := by decide +kernel
theorem fusedMap1728_checked : acceptsGraphIso
    (fused (graph core1728) (root 9) 0 1) DegreeOneSmallSpectrum1536.graph fusedMap1728=true := by decide +kernel
theorem certified1728 : Certified (graph core1728) (root 9) 0 1 :=
  of_native_maps core1728 DegreeOneSmallSpectrum1535.graph DegreeOneSmallSpectrum1536.graph
    sourceMap1728 fusedMap1728 sourceMap1728_checked fusedMap1728_checked
    DegreeOneSmallComparisons.comparison1728
#print axioms sourceMap1728_checked
#print axioms fusedMap1728_checked
#print axioms certified1728
def sourceMap1728swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1728swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1728swap_checked : acceptsGraphIso
    (source (graph core1728) (root 9) 1 0) DegreeOneSmallSpectrum1535.graph sourceMap1728swap=true := by decide +kernel
theorem fusedMap1728swap_checked : acceptsGraphIso
    (fused (graph core1728) (root 9) 1 0) DegreeOneSmallSpectrum1536.graph fusedMap1728swap=true := by decide +kernel
theorem certified1728swap : Certified (graph core1728) (root 9) 1 0 :=
  of_native_maps core1728 DegreeOneSmallSpectrum1535.graph DegreeOneSmallSpectrum1536.graph
    sourceMap1728swap fusedMap1728swap sourceMap1728swap_checked fusedMap1728swap_checked
    DegreeOneSmallComparisons.comparison1728
#print axioms sourceMap1728swap_checked
#print axioms fusedMap1728swap_checked
#print axioms certified1728swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
