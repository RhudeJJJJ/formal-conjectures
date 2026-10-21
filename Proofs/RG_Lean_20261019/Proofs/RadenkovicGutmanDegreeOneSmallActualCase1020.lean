/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1020 : Family 8 := level8.get ⟨109,by decide⟩
def sourceMap1020 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1020 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1020_checked : acceptsGraphIso
    (source (graph core1020) (root 8) 0 1) DegreeOneSmallSpectrum696.graph sourceMap1020=true := by decide +kernel
theorem fusedMap1020_checked : acceptsGraphIso
    (fused (graph core1020) (root 8) 0 1) DegreeOneSmallSpectrum429.graph fusedMap1020=true := by decide +kernel
theorem certified1020 : Certified (graph core1020) (root 8) 0 1 :=
  of_native_maps core1020 DegreeOneSmallSpectrum696.graph DegreeOneSmallSpectrum429.graph
    sourceMap1020 fusedMap1020 sourceMap1020_checked fusedMap1020_checked
    DegreeOneSmallComparisons.comparison1020
#print axioms sourceMap1020_checked
#print axioms fusedMap1020_checked
#print axioms certified1020
def sourceMap1020swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1020swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1020swap_checked : acceptsGraphIso
    (source (graph core1020) (root 8) 1 0) DegreeOneSmallSpectrum696.graph sourceMap1020swap=true := by decide +kernel
theorem fusedMap1020swap_checked : acceptsGraphIso
    (fused (graph core1020) (root 8) 1 0) DegreeOneSmallSpectrum429.graph fusedMap1020swap=true := by decide +kernel
theorem certified1020swap : Certified (graph core1020) (root 8) 1 0 :=
  of_native_maps core1020 DegreeOneSmallSpectrum696.graph DegreeOneSmallSpectrum429.graph
    sourceMap1020swap fusedMap1020swap sourceMap1020swap_checked fusedMap1020swap_checked
    DegreeOneSmallComparisons.comparison1020
#print axioms sourceMap1020swap_checked
#print axioms fusedMap1020swap_checked
#print axioms certified1020swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
