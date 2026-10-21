/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1318 : Family 9 := level9.get ⟨79,by decide⟩
def sourceMap1318 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1318 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1318_checked : acceptsGraphIso
    (source (graph core1318) (root 9) 0 1) DegreeOneSmallSpectrum1410.graph sourceMap1318=true := by decide +kernel
theorem fusedMap1318_checked : acceptsGraphIso
    (fused (graph core1318) (root 9) 0 1) DegreeOneSmallSpectrum923.graph fusedMap1318=true := by decide +kernel
theorem certified1318 : Certified (graph core1318) (root 9) 0 1 :=
  of_native_maps core1318 DegreeOneSmallSpectrum1410.graph DegreeOneSmallSpectrum923.graph
    sourceMap1318 fusedMap1318 sourceMap1318_checked fusedMap1318_checked
    DegreeOneSmallComparisons.comparison1318
#print axioms sourceMap1318_checked
#print axioms fusedMap1318_checked
#print axioms certified1318
def sourceMap1318swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1318swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1318swap_checked : acceptsGraphIso
    (source (graph core1318) (root 9) 1 0) DegreeOneSmallSpectrum1410.graph sourceMap1318swap=true := by decide +kernel
theorem fusedMap1318swap_checked : acceptsGraphIso
    (fused (graph core1318) (root 9) 1 0) DegreeOneSmallSpectrum923.graph fusedMap1318swap=true := by decide +kernel
theorem certified1318swap : Certified (graph core1318) (root 9) 1 0 :=
  of_native_maps core1318 DegreeOneSmallSpectrum1410.graph DegreeOneSmallSpectrum923.graph
    sourceMap1318swap fusedMap1318swap sourceMap1318swap_checked fusedMap1318swap_checked
    DegreeOneSmallComparisons.comparison1318
#print axioms sourceMap1318swap_checked
#print axioms fusedMap1318swap_checked
#print axioms certified1318swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
