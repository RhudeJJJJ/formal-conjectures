/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1286 : Family 9 := level9.get ⟨56,by decide⟩
def sourceMap1286 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1286 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1286_checked : acceptsGraphIso
    (source (graph core1286) (root 9) 0 1) DegreeOneSmallSpectrum1222.graph sourceMap1286=true := by decide +kernel
theorem fusedMap1286_checked : acceptsGraphIso
    (fused (graph core1286) (root 9) 0 1) DegreeOneSmallSpectrum881.graph fusedMap1286=true := by decide +kernel
theorem certified1286 : Certified (graph core1286) (root 9) 0 1 :=
  of_native_maps core1286 DegreeOneSmallSpectrum1222.graph DegreeOneSmallSpectrum881.graph
    sourceMap1286 fusedMap1286 sourceMap1286_checked fusedMap1286_checked
    DegreeOneSmallComparisons.comparison1286
#print axioms sourceMap1286_checked
#print axioms fusedMap1286_checked
#print axioms certified1286
def sourceMap1286swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1286swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1286swap_checked : acceptsGraphIso
    (source (graph core1286) (root 9) 1 0) DegreeOneSmallSpectrum1222.graph sourceMap1286swap=true := by decide +kernel
theorem fusedMap1286swap_checked : acceptsGraphIso
    (fused (graph core1286) (root 9) 1 0) DegreeOneSmallSpectrum881.graph fusedMap1286swap=true := by decide +kernel
theorem certified1286swap : Certified (graph core1286) (root 9) 1 0 :=
  of_native_maps core1286 DegreeOneSmallSpectrum1222.graph DegreeOneSmallSpectrum881.graph
    sourceMap1286swap fusedMap1286swap sourceMap1286swap_checked fusedMap1286swap_checked
    DegreeOneSmallComparisons.comparison1286
#print axioms sourceMap1286swap_checked
#print axioms fusedMap1286swap_checked
#print axioms certified1286swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
