/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1630 : Family 9 := level9.get ⟨370,by decide⟩
def sourceMap1630 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1630 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1630_checked : acceptsGraphIso
    (source (graph core1630) (root 9) 0 1) DegreeOneSmallSpectrum1806.graph sourceMap1630=true := by decide +kernel
theorem fusedMap1630_checked : acceptsGraphIso
    (fused (graph core1630) (root 9) 0 1) DegreeOneSmallSpectrum1120.graph fusedMap1630=true := by decide +kernel
theorem certified1630 : Certified (graph core1630) (root 9) 0 1 :=
  of_native_maps core1630 DegreeOneSmallSpectrum1806.graph DegreeOneSmallSpectrum1120.graph
    sourceMap1630 fusedMap1630 sourceMap1630_checked fusedMap1630_checked
    DegreeOneSmallComparisons.comparison1630
#print axioms sourceMap1630_checked
#print axioms fusedMap1630_checked
#print axioms certified1630
def sourceMap1630swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1630swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1630swap_checked : acceptsGraphIso
    (source (graph core1630) (root 9) 1 0) DegreeOneSmallSpectrum1806.graph sourceMap1630swap=true := by decide +kernel
theorem fusedMap1630swap_checked : acceptsGraphIso
    (fused (graph core1630) (root 9) 1 0) DegreeOneSmallSpectrum1120.graph fusedMap1630swap=true := by decide +kernel
theorem certified1630swap : Certified (graph core1630) (root 9) 1 0 :=
  of_native_maps core1630 DegreeOneSmallSpectrum1806.graph DegreeOneSmallSpectrum1120.graph
    sourceMap1630swap fusedMap1630swap sourceMap1630swap_checked fusedMap1630swap_checked
    DegreeOneSmallComparisons.comparison1630
#print axioms sourceMap1630swap_checked
#print axioms fusedMap1630swap_checked
#print axioms certified1630swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
