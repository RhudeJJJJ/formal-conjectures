/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1690 : Family 9 := level9.get ⟨450,by decide⟩
def sourceMap1690 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1690 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1690_checked : acceptsGraphIso
    (source (graph core1690) (root 9) 0 1) DegreeOneSmallSpectrum1949.graph sourceMap1690=true := by decide +kernel
theorem fusedMap1690_checked : acceptsGraphIso
    (fused (graph core1690) (root 9) 0 1) DegreeOneSmallSpectrum1371.graph fusedMap1690=true := by decide +kernel
theorem certified1690 : Certified (graph core1690) (root 9) 0 1 :=
  of_native_maps core1690 DegreeOneSmallSpectrum1949.graph DegreeOneSmallSpectrum1371.graph
    sourceMap1690 fusedMap1690 sourceMap1690_checked fusedMap1690_checked
    DegreeOneSmallComparisons.comparison1690
#print axioms sourceMap1690_checked
#print axioms fusedMap1690_checked
#print axioms certified1690
def sourceMap1690swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1690swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1690swap_checked : acceptsGraphIso
    (source (graph core1690) (root 9) 1 0) DegreeOneSmallSpectrum1949.graph sourceMap1690swap=true := by decide +kernel
theorem fusedMap1690swap_checked : acceptsGraphIso
    (fused (graph core1690) (root 9) 1 0) DegreeOneSmallSpectrum1371.graph fusedMap1690swap=true := by decide +kernel
theorem certified1690swap : Certified (graph core1690) (root 9) 1 0 :=
  of_native_maps core1690 DegreeOneSmallSpectrum1949.graph DegreeOneSmallSpectrum1371.graph
    sourceMap1690swap fusedMap1690swap sourceMap1690swap_checked fusedMap1690swap_checked
    DegreeOneSmallComparisons.comparison1690
#print axioms sourceMap1690swap_checked
#print axioms fusedMap1690swap_checked
#print axioms certified1690swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
