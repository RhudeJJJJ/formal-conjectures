/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1338 : Family 9 := level9.get ⟨94,by decide⟩
def sourceMap1338 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1338 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1338_checked : acceptsGraphIso
    (source (graph core1338) (root 9) 0 1) DegreeOneSmallSpectrum1442.graph sourceMap1338=true := by decide +kernel
theorem fusedMap1338_checked : acceptsGraphIso
    (fused (graph core1338) (root 9) 0 1) DegreeOneSmallSpectrum946.graph fusedMap1338=true := by decide +kernel
theorem certified1338 : Certified (graph core1338) (root 9) 0 1 :=
  of_native_maps core1338 DegreeOneSmallSpectrum1442.graph DegreeOneSmallSpectrum946.graph
    sourceMap1338 fusedMap1338 sourceMap1338_checked fusedMap1338_checked
    DegreeOneSmallComparisons.comparison1338
#print axioms sourceMap1338_checked
#print axioms fusedMap1338_checked
#print axioms certified1338
def sourceMap1338swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1338swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1338swap_checked : acceptsGraphIso
    (source (graph core1338) (root 9) 1 0) DegreeOneSmallSpectrum1442.graph sourceMap1338swap=true := by decide +kernel
theorem fusedMap1338swap_checked : acceptsGraphIso
    (fused (graph core1338) (root 9) 1 0) DegreeOneSmallSpectrum946.graph fusedMap1338swap=true := by decide +kernel
theorem certified1338swap : Certified (graph core1338) (root 9) 1 0 :=
  of_native_maps core1338 DegreeOneSmallSpectrum1442.graph DegreeOneSmallSpectrum946.graph
    sourceMap1338swap fusedMap1338swap sourceMap1338swap_checked fusedMap1338swap_checked
    DegreeOneSmallComparisons.comparison1338
#print axioms sourceMap1338swap_checked
#print axioms fusedMap1338swap_checked
#print axioms certified1338swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
