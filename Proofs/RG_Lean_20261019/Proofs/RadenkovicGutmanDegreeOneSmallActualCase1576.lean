/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1576 : Family 9 := level9.get ⟨319,by decide⟩
def sourceMap1576 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1576 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1576_checked : acceptsGraphIso
    (source (graph core1576) (root 9) 0 1) DegreeOneSmallSpectrum1551.graph sourceMap1576=true := by decide +kernel
theorem fusedMap1576_checked : acceptsGraphIso
    (fused (graph core1576) (root 9) 0 1) DegreeOneSmallSpectrum981.graph fusedMap1576=true := by decide +kernel
theorem certified1576 : Certified (graph core1576) (root 9) 0 1 :=
  of_native_maps core1576 DegreeOneSmallSpectrum1551.graph DegreeOneSmallSpectrum981.graph
    sourceMap1576 fusedMap1576 sourceMap1576_checked fusedMap1576_checked
    DegreeOneSmallComparisons.comparison1576
#print axioms sourceMap1576_checked
#print axioms fusedMap1576_checked
#print axioms certified1576
def sourceMap1576swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1576swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1576swap_checked : acceptsGraphIso
    (source (graph core1576) (root 9) 1 0) DegreeOneSmallSpectrum1551.graph sourceMap1576swap=true := by decide +kernel
theorem fusedMap1576swap_checked : acceptsGraphIso
    (fused (graph core1576) (root 9) 1 0) DegreeOneSmallSpectrum981.graph fusedMap1576swap=true := by decide +kernel
theorem certified1576swap : Certified (graph core1576) (root 9) 1 0 :=
  of_native_maps core1576 DegreeOneSmallSpectrum1551.graph DegreeOneSmallSpectrum981.graph
    sourceMap1576swap fusedMap1576swap sourceMap1576swap_checked fusedMap1576swap_checked
    DegreeOneSmallComparisons.comparison1576
#print axioms sourceMap1576swap_checked
#print axioms fusedMap1576swap_checked
#print axioms certified1576swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
