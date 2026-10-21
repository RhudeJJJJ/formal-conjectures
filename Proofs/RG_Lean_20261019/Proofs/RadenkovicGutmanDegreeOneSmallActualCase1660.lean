/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1660 : Family 9 := level9.get ⟨418,by decide⟩
def sourceMap1660 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1660 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1660_checked : acceptsGraphIso
    (source (graph core1660) (root 9) 0 1) DegreeOneSmallSpectrum1902.graph sourceMap1660=true := by decide +kernel
theorem fusedMap1660_checked : acceptsGraphIso
    (fused (graph core1660) (root 9) 0 1) DegreeOneSmallSpectrum1297.graph fusedMap1660=true := by decide +kernel
theorem certified1660 : Certified (graph core1660) (root 9) 0 1 :=
  of_native_maps core1660 DegreeOneSmallSpectrum1902.graph DegreeOneSmallSpectrum1297.graph
    sourceMap1660 fusedMap1660 sourceMap1660_checked fusedMap1660_checked
    DegreeOneSmallComparisons.comparison1660
#print axioms sourceMap1660_checked
#print axioms fusedMap1660_checked
#print axioms certified1660
def sourceMap1660swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1660swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1660swap_checked : acceptsGraphIso
    (source (graph core1660) (root 9) 1 0) DegreeOneSmallSpectrum1902.graph sourceMap1660swap=true := by decide +kernel
theorem fusedMap1660swap_checked : acceptsGraphIso
    (fused (graph core1660) (root 9) 1 0) DegreeOneSmallSpectrum1297.graph fusedMap1660swap=true := by decide +kernel
theorem certified1660swap : Certified (graph core1660) (root 9) 1 0 :=
  of_native_maps core1660 DegreeOneSmallSpectrum1902.graph DegreeOneSmallSpectrum1297.graph
    sourceMap1660swap fusedMap1660swap sourceMap1660swap_checked fusedMap1660swap_checked
    DegreeOneSmallComparisons.comparison1660
#print axioms sourceMap1660swap_checked
#print axioms fusedMap1660swap_checked
#print axioms certified1660swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
