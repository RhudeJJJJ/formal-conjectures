/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1242 : Family 9 := level9.get ⟨26,by decide⟩
def sourceMap1242 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1242 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1242_checked : acceptsGraphIso
    (source (graph core1242) (root 9) 0 1) DegreeOneSmallSpectrum933.graph sourceMap1242=true := by decide +kernel
theorem fusedMap1242_checked : acceptsGraphIso
    (fused (graph core1242) (root 9) 0 1) DegreeOneSmallSpectrum966.graph fusedMap1242=true := by decide +kernel
theorem certified1242 : Certified (graph core1242) (root 9) 0 1 :=
  of_native_maps core1242 DegreeOneSmallSpectrum933.graph DegreeOneSmallSpectrum966.graph
    sourceMap1242 fusedMap1242 sourceMap1242_checked fusedMap1242_checked
    DegreeOneSmallComparisons.comparison1242
#print axioms sourceMap1242_checked
#print axioms fusedMap1242_checked
#print axioms certified1242
def sourceMap1242swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1242swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1242swap_checked : acceptsGraphIso
    (source (graph core1242) (root 9) 1 0) DegreeOneSmallSpectrum933.graph sourceMap1242swap=true := by decide +kernel
theorem fusedMap1242swap_checked : acceptsGraphIso
    (fused (graph core1242) (root 9) 1 0) DegreeOneSmallSpectrum966.graph fusedMap1242swap=true := by decide +kernel
theorem certified1242swap : Certified (graph core1242) (root 9) 1 0 :=
  of_native_maps core1242 DegreeOneSmallSpectrum933.graph DegreeOneSmallSpectrum966.graph
    sourceMap1242swap fusedMap1242swap sourceMap1242swap_checked fusedMap1242swap_checked
    DegreeOneSmallComparisons.comparison1242
#print axioms sourceMap1242swap_checked
#print axioms fusedMap1242swap_checked
#print axioms certified1242swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
