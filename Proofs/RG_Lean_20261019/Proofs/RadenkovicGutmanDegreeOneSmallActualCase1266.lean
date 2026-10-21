/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1266 : Family 9 := level9.get ⟨44,by decide⟩
def sourceMap1266 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1266 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1266_checked : acceptsGraphIso
    (source (graph core1266) (root 9) 0 1) DegreeOneSmallSpectrum1033.graph sourceMap1266=true := by decide +kernel
theorem fusedMap1266_checked : acceptsGraphIso
    (fused (graph core1266) (root 9) 0 1) DegreeOneSmallSpectrum863.graph fusedMap1266=true := by decide +kernel
theorem certified1266 : Certified (graph core1266) (root 9) 0 1 :=
  of_native_maps core1266 DegreeOneSmallSpectrum1033.graph DegreeOneSmallSpectrum863.graph
    sourceMap1266 fusedMap1266 sourceMap1266_checked fusedMap1266_checked
    DegreeOneSmallComparisons.comparison1266
#print axioms sourceMap1266_checked
#print axioms fusedMap1266_checked
#print axioms certified1266
def sourceMap1266swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1266swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1266swap_checked : acceptsGraphIso
    (source (graph core1266) (root 9) 1 0) DegreeOneSmallSpectrum1033.graph sourceMap1266swap=true := by decide +kernel
theorem fusedMap1266swap_checked : acceptsGraphIso
    (fused (graph core1266) (root 9) 1 0) DegreeOneSmallSpectrum863.graph fusedMap1266swap=true := by decide +kernel
theorem certified1266swap : Certified (graph core1266) (root 9) 1 0 :=
  of_native_maps core1266 DegreeOneSmallSpectrum1033.graph DegreeOneSmallSpectrum863.graph
    sourceMap1266swap fusedMap1266swap sourceMap1266swap_checked fusedMap1266swap_checked
    DegreeOneSmallComparisons.comparison1266
#print axioms sourceMap1266swap_checked
#print axioms fusedMap1266swap_checked
#print axioms certified1266swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
