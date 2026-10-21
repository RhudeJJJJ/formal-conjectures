/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1412 : Family 9 := level9.get ⟨156,by decide⟩
def sourceMap1412 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1412 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1412_checked : acceptsGraphIso
    (source (graph core1412) (root 9) 0 1) DegreeOneSmallSpectrum1086.graph sourceMap1412=true := by decide +kernel
theorem fusedMap1412_checked : acceptsGraphIso
    (fused (graph core1412) (root 9) 0 1) DegreeOneSmallSpectrum1088.graph fusedMap1412=true := by decide +kernel
theorem certified1412 : Certified (graph core1412) (root 9) 0 1 :=
  of_native_maps core1412 DegreeOneSmallSpectrum1086.graph DegreeOneSmallSpectrum1088.graph
    sourceMap1412 fusedMap1412 sourceMap1412_checked fusedMap1412_checked
    DegreeOneSmallComparisons.comparison1412
#print axioms sourceMap1412_checked
#print axioms fusedMap1412_checked
#print axioms certified1412
def sourceMap1412swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1412swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1412swap_checked : acceptsGraphIso
    (source (graph core1412) (root 9) 1 0) DegreeOneSmallSpectrum1086.graph sourceMap1412swap=true := by decide +kernel
theorem fusedMap1412swap_checked : acceptsGraphIso
    (fused (graph core1412) (root 9) 1 0) DegreeOneSmallSpectrum1088.graph fusedMap1412swap=true := by decide +kernel
theorem certified1412swap : Certified (graph core1412) (root 9) 1 0 :=
  of_native_maps core1412 DegreeOneSmallSpectrum1086.graph DegreeOneSmallSpectrum1088.graph
    sourceMap1412swap fusedMap1412swap sourceMap1412swap_checked fusedMap1412swap_checked
    DegreeOneSmallComparisons.comparison1412
#print axioms sourceMap1412swap_checked
#print axioms fusedMap1412swap_checked
#print axioms certified1412swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
