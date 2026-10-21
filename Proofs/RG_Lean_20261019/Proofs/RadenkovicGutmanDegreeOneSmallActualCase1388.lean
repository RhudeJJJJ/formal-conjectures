/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1388 : Family 9 := level9.get ⟨138,by decide⟩
def sourceMap1388 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1388 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1388_checked : acceptsGraphIso
    (source (graph core1388) (root 9) 0 1) DegreeOneSmallSpectrum990.graph sourceMap1388=true := by decide +kernel
theorem fusedMap1388_checked : acceptsGraphIso
    (fused (graph core1388) (root 9) 0 1) DegreeOneSmallSpectrum992.graph fusedMap1388=true := by decide +kernel
theorem certified1388 : Certified (graph core1388) (root 9) 0 1 :=
  of_native_maps core1388 DegreeOneSmallSpectrum990.graph DegreeOneSmallSpectrum992.graph
    sourceMap1388 fusedMap1388 sourceMap1388_checked fusedMap1388_checked
    DegreeOneSmallComparisons.comparison1388
#print axioms sourceMap1388_checked
#print axioms fusedMap1388_checked
#print axioms certified1388
def sourceMap1388swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1388swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1388swap_checked : acceptsGraphIso
    (source (graph core1388) (root 9) 1 0) DegreeOneSmallSpectrum990.graph sourceMap1388swap=true := by decide +kernel
theorem fusedMap1388swap_checked : acceptsGraphIso
    (fused (graph core1388) (root 9) 1 0) DegreeOneSmallSpectrum992.graph fusedMap1388swap=true := by decide +kernel
theorem certified1388swap : Certified (graph core1388) (root 9) 1 0 :=
  of_native_maps core1388 DegreeOneSmallSpectrum990.graph DegreeOneSmallSpectrum992.graph
    sourceMap1388swap fusedMap1388swap sourceMap1388swap_checked fusedMap1388swap_checked
    DegreeOneSmallComparisons.comparison1388
#print axioms sourceMap1388swap_checked
#print axioms fusedMap1388swap_checked
#print axioms certified1388swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
