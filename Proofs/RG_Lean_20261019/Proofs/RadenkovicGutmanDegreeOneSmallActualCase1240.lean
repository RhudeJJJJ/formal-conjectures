/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1240 : Family 9 := level9.get ⟨25,by decide⟩
def sourceMap1240 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1240 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1240_checked : acceptsGraphIso
    (source (graph core1240) (root 9) 0 1) DegreeOneSmallSpectrum939.graph sourceMap1240=true := by decide +kernel
theorem fusedMap1240_checked : acceptsGraphIso
    (fused (graph core1240) (root 9) 0 1) DegreeOneSmallSpectrum961.graph fusedMap1240=true := by decide +kernel
theorem certified1240 : Certified (graph core1240) (root 9) 0 1 :=
  of_native_maps core1240 DegreeOneSmallSpectrum939.graph DegreeOneSmallSpectrum961.graph
    sourceMap1240 fusedMap1240 sourceMap1240_checked fusedMap1240_checked
    DegreeOneSmallComparisons.comparison1240
#print axioms sourceMap1240_checked
#print axioms fusedMap1240_checked
#print axioms certified1240
def sourceMap1240swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1240swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1240swap_checked : acceptsGraphIso
    (source (graph core1240) (root 9) 1 0) DegreeOneSmallSpectrum939.graph sourceMap1240swap=true := by decide +kernel
theorem fusedMap1240swap_checked : acceptsGraphIso
    (fused (graph core1240) (root 9) 1 0) DegreeOneSmallSpectrum961.graph fusedMap1240swap=true := by decide +kernel
theorem certified1240swap : Certified (graph core1240) (root 9) 1 0 :=
  of_native_maps core1240 DegreeOneSmallSpectrum939.graph DegreeOneSmallSpectrum961.graph
    sourceMap1240swap fusedMap1240swap sourceMap1240swap_checked fusedMap1240swap_checked
    DegreeOneSmallComparisons.comparison1240
#print axioms sourceMap1240swap_checked
#print axioms fusedMap1240swap_checked
#print axioms certified1240swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
