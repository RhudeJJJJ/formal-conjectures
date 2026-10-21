/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1666 : Family 9 := level9.get ⟨422,by decide⟩
def sourceMap1666 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1666 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1666_checked : acceptsGraphIso
    (source (graph core1666) (root 9) 0 1) DegreeOneSmallSpectrum1910.graph sourceMap1666=true := by decide +kernel
theorem fusedMap1666_checked : acceptsGraphIso
    (fused (graph core1666) (root 9) 0 1) DegreeOneSmallSpectrum1303.graph fusedMap1666=true := by decide +kernel
theorem certified1666 : Certified (graph core1666) (root 9) 0 1 :=
  of_native_maps core1666 DegreeOneSmallSpectrum1910.graph DegreeOneSmallSpectrum1303.graph
    sourceMap1666 fusedMap1666 sourceMap1666_checked fusedMap1666_checked
    DegreeOneSmallComparisons.comparison1666
#print axioms sourceMap1666_checked
#print axioms fusedMap1666_checked
#print axioms certified1666
def sourceMap1666swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1666swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1666swap_checked : acceptsGraphIso
    (source (graph core1666) (root 9) 1 0) DegreeOneSmallSpectrum1910.graph sourceMap1666swap=true := by decide +kernel
theorem fusedMap1666swap_checked : acceptsGraphIso
    (fused (graph core1666) (root 9) 1 0) DegreeOneSmallSpectrum1303.graph fusedMap1666swap=true := by decide +kernel
theorem certified1666swap : Certified (graph core1666) (root 9) 1 0 :=
  of_native_maps core1666 DegreeOneSmallSpectrum1910.graph DegreeOneSmallSpectrum1303.graph
    sourceMap1666swap fusedMap1666swap sourceMap1666swap_checked fusedMap1666swap_checked
    DegreeOneSmallComparisons.comparison1666
#print axioms sourceMap1666swap_checked
#print axioms fusedMap1666swap_checked
#print axioms certified1666swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
