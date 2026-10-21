/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1492 : Family 9 := level9.get ⟨222,by decide⟩
def sourceMap1492 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1492 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1492_checked : acceptsGraphIso
    (source (graph core1492) (root 9) 0 1) DegreeOneSmallSpectrum1382.graph sourceMap1492=true := by decide +kernel
theorem fusedMap1492_checked : acceptsGraphIso
    (fused (graph core1492) (root 9) 0 1) DegreeOneSmallSpectrum1393.graph fusedMap1492=true := by decide +kernel
theorem certified1492 : Certified (graph core1492) (root 9) 0 1 :=
  of_native_maps core1492 DegreeOneSmallSpectrum1382.graph DegreeOneSmallSpectrum1393.graph
    sourceMap1492 fusedMap1492 sourceMap1492_checked fusedMap1492_checked
    DegreeOneSmallComparisons.comparison1492
#print axioms sourceMap1492_checked
#print axioms fusedMap1492_checked
#print axioms certified1492
def sourceMap1492swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1492swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1492swap_checked : acceptsGraphIso
    (source (graph core1492) (root 9) 1 0) DegreeOneSmallSpectrum1382.graph sourceMap1492swap=true := by decide +kernel
theorem fusedMap1492swap_checked : acceptsGraphIso
    (fused (graph core1492) (root 9) 1 0) DegreeOneSmallSpectrum1393.graph fusedMap1492swap=true := by decide +kernel
theorem certified1492swap : Certified (graph core1492) (root 9) 1 0 :=
  of_native_maps core1492 DegreeOneSmallSpectrum1382.graph DegreeOneSmallSpectrum1393.graph
    sourceMap1492swap fusedMap1492swap sourceMap1492swap_checked fusedMap1492swap_checked
    DegreeOneSmallComparisons.comparison1492
#print axioms sourceMap1492swap_checked
#print axioms fusedMap1492swap_checked
#print axioms certified1492swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
