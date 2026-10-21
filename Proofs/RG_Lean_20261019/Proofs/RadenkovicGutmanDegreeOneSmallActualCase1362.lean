/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1362 : Family 9 := level9.get ⟨112,by decide⟩
def sourceMap1362 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1362 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1362_checked : acceptsGraphIso
    (source (graph core1362) (root 9) 0 1) DegreeOneSmallSpectrum1452.graph sourceMap1362=true := by decide +kernel
theorem fusedMap1362_checked : acceptsGraphIso
    (fused (graph core1362) (root 9) 0 1) DegreeOneSmallSpectrum967.graph fusedMap1362=true := by decide +kernel
theorem certified1362 : Certified (graph core1362) (root 9) 0 1 :=
  of_native_maps core1362 DegreeOneSmallSpectrum1452.graph DegreeOneSmallSpectrum967.graph
    sourceMap1362 fusedMap1362 sourceMap1362_checked fusedMap1362_checked
    DegreeOneSmallComparisons.comparison1362
#print axioms sourceMap1362_checked
#print axioms fusedMap1362_checked
#print axioms certified1362
def sourceMap1362swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1362swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1362swap_checked : acceptsGraphIso
    (source (graph core1362) (root 9) 1 0) DegreeOneSmallSpectrum1452.graph sourceMap1362swap=true := by decide +kernel
theorem fusedMap1362swap_checked : acceptsGraphIso
    (fused (graph core1362) (root 9) 1 0) DegreeOneSmallSpectrum967.graph fusedMap1362swap=true := by decide +kernel
theorem certified1362swap : Certified (graph core1362) (root 9) 1 0 :=
  of_native_maps core1362 DegreeOneSmallSpectrum1452.graph DegreeOneSmallSpectrum967.graph
    sourceMap1362swap fusedMap1362swap sourceMap1362swap_checked fusedMap1362swap_checked
    DegreeOneSmallComparisons.comparison1362
#print axioms sourceMap1362swap_checked
#print axioms fusedMap1362swap_checked
#print axioms certified1362swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
