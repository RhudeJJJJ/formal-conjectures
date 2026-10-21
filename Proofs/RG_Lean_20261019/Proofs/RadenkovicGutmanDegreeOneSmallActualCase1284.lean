/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1284 : Family 9 := level9.get ⟨55,by decide⟩
def sourceMap1284 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1284 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1284_checked : acceptsGraphIso
    (source (graph core1284) (root 9) 0 1) DegreeOneSmallSpectrum1207.graph sourceMap1284=true := by decide +kernel
theorem fusedMap1284_checked : acceptsGraphIso
    (fused (graph core1284) (root 9) 0 1) DegreeOneSmallSpectrum880.graph fusedMap1284=true := by decide +kernel
theorem certified1284 : Certified (graph core1284) (root 9) 0 1 :=
  of_native_maps core1284 DegreeOneSmallSpectrum1207.graph DegreeOneSmallSpectrum880.graph
    sourceMap1284 fusedMap1284 sourceMap1284_checked fusedMap1284_checked
    DegreeOneSmallComparisons.comparison1284
#print axioms sourceMap1284_checked
#print axioms fusedMap1284_checked
#print axioms certified1284
def sourceMap1284swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1284swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1284swap_checked : acceptsGraphIso
    (source (graph core1284) (root 9) 1 0) DegreeOneSmallSpectrum1207.graph sourceMap1284swap=true := by decide +kernel
theorem fusedMap1284swap_checked : acceptsGraphIso
    (fused (graph core1284) (root 9) 1 0) DegreeOneSmallSpectrum880.graph fusedMap1284swap=true := by decide +kernel
theorem certified1284swap : Certified (graph core1284) (root 9) 1 0 :=
  of_native_maps core1284 DegreeOneSmallSpectrum1207.graph DegreeOneSmallSpectrum880.graph
    sourceMap1284swap fusedMap1284swap sourceMap1284swap_checked fusedMap1284swap_checked
    DegreeOneSmallComparisons.comparison1284
#print axioms sourceMap1284swap_checked
#print axioms fusedMap1284swap_checked
#print axioms certified1284swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
