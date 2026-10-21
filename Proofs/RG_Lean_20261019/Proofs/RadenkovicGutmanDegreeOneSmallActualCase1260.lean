/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1260 : Family 9 := level9.get ⟨38,by decide⟩
def sourceMap1260 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1260 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1260_checked : acceptsGraphIso
    (source (graph core1260) (root 9) 0 1) DegreeOneSmallSpectrum923.graph sourceMap1260=true := by decide +kernel
theorem fusedMap1260_checked : acceptsGraphIso
    (fused (graph core1260) (root 9) 0 1) DegreeOneSmallSpectrum971.graph fusedMap1260=true := by decide +kernel
theorem certified1260 : Certified (graph core1260) (root 9) 0 1 :=
  of_native_maps core1260 DegreeOneSmallSpectrum923.graph DegreeOneSmallSpectrum971.graph
    sourceMap1260 fusedMap1260 sourceMap1260_checked fusedMap1260_checked
    DegreeOneSmallComparisons.comparison1260
#print axioms sourceMap1260_checked
#print axioms fusedMap1260_checked
#print axioms certified1260
def sourceMap1260swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1260swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1260swap_checked : acceptsGraphIso
    (source (graph core1260) (root 9) 1 0) DegreeOneSmallSpectrum923.graph sourceMap1260swap=true := by decide +kernel
theorem fusedMap1260swap_checked : acceptsGraphIso
    (fused (graph core1260) (root 9) 1 0) DegreeOneSmallSpectrum971.graph fusedMap1260swap=true := by decide +kernel
theorem certified1260swap : Certified (graph core1260) (root 9) 1 0 :=
  of_native_maps core1260 DegreeOneSmallSpectrum923.graph DegreeOneSmallSpectrum971.graph
    sourceMap1260swap fusedMap1260swap sourceMap1260swap_checked fusedMap1260swap_checked
    DegreeOneSmallComparisons.comparison1260
#print axioms sourceMap1260swap_checked
#print axioms fusedMap1260swap_checked
#print axioms certified1260swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
