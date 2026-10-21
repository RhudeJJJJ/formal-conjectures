/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1678 : Family 9 := level9.get ⟨439,by decide⟩
def sourceMap1678 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1678 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1678_checked : acceptsGraphIso
    (source (graph core1678) (root 9) 0 1) DegreeOneSmallSpectrum1937.graph sourceMap1678=true := by decide +kernel
theorem fusedMap1678_checked : acceptsGraphIso
    (fused (graph core1678) (root 9) 0 1) DegreeOneSmallSpectrum1350.graph fusedMap1678=true := by decide +kernel
theorem certified1678 : Certified (graph core1678) (root 9) 0 1 :=
  of_native_maps core1678 DegreeOneSmallSpectrum1937.graph DegreeOneSmallSpectrum1350.graph
    sourceMap1678 fusedMap1678 sourceMap1678_checked fusedMap1678_checked
    DegreeOneSmallComparisons.comparison1678
#print axioms sourceMap1678_checked
#print axioms fusedMap1678_checked
#print axioms certified1678
def sourceMap1678swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1678swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1678swap_checked : acceptsGraphIso
    (source (graph core1678) (root 9) 1 0) DegreeOneSmallSpectrum1937.graph sourceMap1678swap=true := by decide +kernel
theorem fusedMap1678swap_checked : acceptsGraphIso
    (fused (graph core1678) (root 9) 1 0) DegreeOneSmallSpectrum1350.graph fusedMap1678swap=true := by decide +kernel
theorem certified1678swap : Certified (graph core1678) (root 9) 1 0 :=
  of_native_maps core1678 DegreeOneSmallSpectrum1937.graph DegreeOneSmallSpectrum1350.graph
    sourceMap1678swap fusedMap1678swap sourceMap1678swap_checked fusedMap1678swap_checked
    DegreeOneSmallComparisons.comparison1678
#print axioms sourceMap1678swap_checked
#print axioms fusedMap1678swap_checked
#print axioms certified1678swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
