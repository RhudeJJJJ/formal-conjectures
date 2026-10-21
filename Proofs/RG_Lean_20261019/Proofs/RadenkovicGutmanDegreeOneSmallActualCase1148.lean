/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1148 : Family 8 := level8.get ⟨192,by decide⟩
def sourceMap1148 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1148 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1148_checked : acceptsGraphIso
    (source (graph core1148) (root 8) 0 1) DegreeOneSmallSpectrum611.graph sourceMap1148=true := by decide +kernel
theorem fusedMap1148_checked : acceptsGraphIso
    (fused (graph core1148) (root 8) 0 1) DegreeOneSmallSpectrum612.graph fusedMap1148=true := by decide +kernel
theorem certified1148 : Certified (graph core1148) (root 8) 0 1 :=
  of_native_maps core1148 DegreeOneSmallSpectrum611.graph DegreeOneSmallSpectrum612.graph
    sourceMap1148 fusedMap1148 sourceMap1148_checked fusedMap1148_checked
    DegreeOneSmallComparisons.comparison1148
#print axioms sourceMap1148_checked
#print axioms fusedMap1148_checked
#print axioms certified1148
def sourceMap1148swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1148swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1148swap_checked : acceptsGraphIso
    (source (graph core1148) (root 8) 1 0) DegreeOneSmallSpectrum611.graph sourceMap1148swap=true := by decide +kernel
theorem fusedMap1148swap_checked : acceptsGraphIso
    (fused (graph core1148) (root 8) 1 0) DegreeOneSmallSpectrum612.graph fusedMap1148swap=true := by decide +kernel
theorem certified1148swap : Certified (graph core1148) (root 8) 1 0 :=
  of_native_maps core1148 DegreeOneSmallSpectrum611.graph DegreeOneSmallSpectrum612.graph
    sourceMap1148swap fusedMap1148swap sourceMap1148swap_checked fusedMap1148swap_checked
    DegreeOneSmallComparisons.comparison1148
#print axioms sourceMap1148swap_checked
#print axioms fusedMap1148swap_checked
#print axioms certified1148swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
