/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1592 : Family 9 := level9.get ⟨332,by decide⟩
def sourceMap1592 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1592 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1592_checked : acceptsGraphIso
    (source (graph core1592) (root 9) 0 1) DegreeOneSmallSpectrum1635.graph sourceMap1592=true := by decide +kernel
theorem fusedMap1592_checked : acceptsGraphIso
    (fused (graph core1592) (root 9) 0 1) DegreeOneSmallSpectrum1011.graph fusedMap1592=true := by decide +kernel
theorem certified1592 : Certified (graph core1592) (root 9) 0 1 :=
  of_native_maps core1592 DegreeOneSmallSpectrum1635.graph DegreeOneSmallSpectrum1011.graph
    sourceMap1592 fusedMap1592 sourceMap1592_checked fusedMap1592_checked
    DegreeOneSmallComparisons.comparison1592
#print axioms sourceMap1592_checked
#print axioms fusedMap1592_checked
#print axioms certified1592
def sourceMap1592swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1592swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1592swap_checked : acceptsGraphIso
    (source (graph core1592) (root 9) 1 0) DegreeOneSmallSpectrum1635.graph sourceMap1592swap=true := by decide +kernel
theorem fusedMap1592swap_checked : acceptsGraphIso
    (fused (graph core1592) (root 9) 1 0) DegreeOneSmallSpectrum1011.graph fusedMap1592swap=true := by decide +kernel
theorem certified1592swap : Certified (graph core1592) (root 9) 1 0 :=
  of_native_maps core1592 DegreeOneSmallSpectrum1635.graph DegreeOneSmallSpectrum1011.graph
    sourceMap1592swap fusedMap1592swap sourceMap1592swap_checked fusedMap1592swap_checked
    DegreeOneSmallComparisons.comparison1592
#print axioms sourceMap1592swap_checked
#print axioms fusedMap1592swap_checked
#print axioms certified1592swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
