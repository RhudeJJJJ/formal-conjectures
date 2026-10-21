/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1292 : Family 9 := level9.get ⟨60,by decide⟩
def sourceMap1292 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1292 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1292_checked : acceptsGraphIso
    (source (graph core1292) (root 9) 0 1) DegreeOneSmallSpectrum1272.graph sourceMap1292=true := by decide +kernel
theorem fusedMap1292_checked : acceptsGraphIso
    (fused (graph core1292) (root 9) 0 1) DegreeOneSmallSpectrum888.graph fusedMap1292=true := by decide +kernel
theorem certified1292 : Certified (graph core1292) (root 9) 0 1 :=
  of_native_maps core1292 DegreeOneSmallSpectrum1272.graph DegreeOneSmallSpectrum888.graph
    sourceMap1292 fusedMap1292 sourceMap1292_checked fusedMap1292_checked
    DegreeOneSmallComparisons.comparison1292
#print axioms sourceMap1292_checked
#print axioms fusedMap1292_checked
#print axioms certified1292
def sourceMap1292swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1292swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1292swap_checked : acceptsGraphIso
    (source (graph core1292) (root 9) 1 0) DegreeOneSmallSpectrum1272.graph sourceMap1292swap=true := by decide +kernel
theorem fusedMap1292swap_checked : acceptsGraphIso
    (fused (graph core1292) (root 9) 1 0) DegreeOneSmallSpectrum888.graph fusedMap1292swap=true := by decide +kernel
theorem certified1292swap : Certified (graph core1292) (root 9) 1 0 :=
  of_native_maps core1292 DegreeOneSmallSpectrum1272.graph DegreeOneSmallSpectrum888.graph
    sourceMap1292swap fusedMap1292swap sourceMap1292swap_checked fusedMap1292swap_checked
    DegreeOneSmallComparisons.comparison1292
#print axioms sourceMap1292swap_checked
#print axioms fusedMap1292swap_checked
#print axioms certified1292swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
