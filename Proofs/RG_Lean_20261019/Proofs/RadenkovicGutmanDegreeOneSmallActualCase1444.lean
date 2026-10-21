/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1444 : Family 9 := level9.get ⟨179,by decide⟩
def sourceMap1444 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1444 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1444_checked : acceptsGraphIso
    (source (graph core1444) (root 9) 0 1) DegreeOneSmallSpectrum1214.graph sourceMap1444=true := by decide +kernel
theorem fusedMap1444_checked : acceptsGraphIso
    (fused (graph core1444) (root 9) 0 1) DegreeOneSmallSpectrum1216.graph fusedMap1444=true := by decide +kernel
theorem certified1444 : Certified (graph core1444) (root 9) 0 1 :=
  of_native_maps core1444 DegreeOneSmallSpectrum1214.graph DegreeOneSmallSpectrum1216.graph
    sourceMap1444 fusedMap1444 sourceMap1444_checked fusedMap1444_checked
    DegreeOneSmallComparisons.comparison1444
#print axioms sourceMap1444_checked
#print axioms fusedMap1444_checked
#print axioms certified1444
def sourceMap1444swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1444swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1444swap_checked : acceptsGraphIso
    (source (graph core1444) (root 9) 1 0) DegreeOneSmallSpectrum1214.graph sourceMap1444swap=true := by decide +kernel
theorem fusedMap1444swap_checked : acceptsGraphIso
    (fused (graph core1444) (root 9) 1 0) DegreeOneSmallSpectrum1216.graph fusedMap1444swap=true := by decide +kernel
theorem certified1444swap : Certified (graph core1444) (root 9) 1 0 :=
  of_native_maps core1444 DegreeOneSmallSpectrum1214.graph DegreeOneSmallSpectrum1216.graph
    sourceMap1444swap fusedMap1444swap sourceMap1444swap_checked fusedMap1444swap_checked
    DegreeOneSmallComparisons.comparison1444
#print axioms sourceMap1444swap_checked
#print axioms fusedMap1444swap_checked
#print axioms certified1444swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
