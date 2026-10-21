/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1564 : Family 9 := level9.get ⟨293,by decide⟩
def sourceMap1564 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1564 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1564_checked : acceptsGraphIso
    (source (graph core1564) (root 9) 0 1) DegreeOneSmallSpectrum1400.graph sourceMap1564=true := by decide +kernel
theorem fusedMap1564_checked : acceptsGraphIso
    (fused (graph core1564) (root 9) 0 1) DegreeOneSmallSpectrum1513.graph fusedMap1564=true := by decide +kernel
theorem certified1564 : Certified (graph core1564) (root 9) 0 1 :=
  of_native_maps core1564 DegreeOneSmallSpectrum1400.graph DegreeOneSmallSpectrum1513.graph
    sourceMap1564 fusedMap1564 sourceMap1564_checked fusedMap1564_checked
    DegreeOneSmallComparisons.comparison1564
#print axioms sourceMap1564_checked
#print axioms fusedMap1564_checked
#print axioms certified1564
def sourceMap1564swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1564swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1564swap_checked : acceptsGraphIso
    (source (graph core1564) (root 9) 1 0) DegreeOneSmallSpectrum1400.graph sourceMap1564swap=true := by decide +kernel
theorem fusedMap1564swap_checked : acceptsGraphIso
    (fused (graph core1564) (root 9) 1 0) DegreeOneSmallSpectrum1513.graph fusedMap1564swap=true := by decide +kernel
theorem certified1564swap : Certified (graph core1564) (root 9) 1 0 :=
  of_native_maps core1564 DegreeOneSmallSpectrum1400.graph DegreeOneSmallSpectrum1513.graph
    sourceMap1564swap fusedMap1564swap sourceMap1564swap_checked fusedMap1564swap_checked
    DegreeOneSmallComparisons.comparison1564
#print axioms sourceMap1564swap_checked
#print axioms fusedMap1564swap_checked
#print axioms certified1564swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
