/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1153 : Family 8 := level8.get ⟨196,by decide⟩
def sourceMap1153 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1153 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1153_checked : acceptsGraphIso
    (source (graph core1153) (root 8) 0 2) DegreeOneSmallSpectrum1616.graph sourceMap1153=true := by decide +kernel
theorem fusedMap1153_checked : acceptsGraphIso
    (fused (graph core1153) (root 8) 0 2) DegreeOneSmallSpectrum1009.graph fusedMap1153=true := by decide +kernel
theorem certified1153 : Certified (graph core1153) (root 8) 0 2 :=
  of_native_maps core1153 DegreeOneSmallSpectrum1616.graph DegreeOneSmallSpectrum1009.graph
    sourceMap1153 fusedMap1153 sourceMap1153_checked fusedMap1153_checked
    DegreeOneSmallComparisons.comparison1153
#print axioms sourceMap1153_checked
#print axioms fusedMap1153_checked
#print axioms certified1153
def sourceMap1153swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1153swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1153swap_checked : acceptsGraphIso
    (source (graph core1153) (root 8) 2 0) DegreeOneSmallSpectrum1616.graph sourceMap1153swap=true := by decide +kernel
theorem fusedMap1153swap_checked : acceptsGraphIso
    (fused (graph core1153) (root 8) 2 0) DegreeOneSmallSpectrum1009.graph fusedMap1153swap=true := by decide +kernel
theorem certified1153swap : Certified (graph core1153) (root 8) 2 0 :=
  of_native_maps core1153 DegreeOneSmallSpectrum1616.graph DegreeOneSmallSpectrum1009.graph
    sourceMap1153swap fusedMap1153swap sourceMap1153swap_checked fusedMap1153swap_checked
    DegreeOneSmallComparisons.comparison1153
#print axioms sourceMap1153swap_checked
#print axioms fusedMap1153swap_checked
#print axioms certified1153swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
