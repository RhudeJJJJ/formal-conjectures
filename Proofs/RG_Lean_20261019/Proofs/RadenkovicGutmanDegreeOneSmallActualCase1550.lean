/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1550 : Family 9 := level9.get ⟨277,by decide⟩
def sourceMap1550 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1550 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1550_checked : acceptsGraphIso
    (source (graph core1550) (root 9) 0 1) DegreeOneSmallSpectrum1407.graph sourceMap1550=true := by decide +kernel
theorem fusedMap1550_checked : acceptsGraphIso
    (fused (graph core1550) (root 9) 0 1) DegreeOneSmallSpectrum1506.graph fusedMap1550=true := by decide +kernel
theorem certified1550 : Certified (graph core1550) (root 9) 0 1 :=
  of_native_maps core1550 DegreeOneSmallSpectrum1407.graph DegreeOneSmallSpectrum1506.graph
    sourceMap1550 fusedMap1550 sourceMap1550_checked fusedMap1550_checked
    DegreeOneSmallComparisons.comparison1550
#print axioms sourceMap1550_checked
#print axioms fusedMap1550_checked
#print axioms certified1550
def sourceMap1550swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1550swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1550swap_checked : acceptsGraphIso
    (source (graph core1550) (root 9) 1 0) DegreeOneSmallSpectrum1407.graph sourceMap1550swap=true := by decide +kernel
theorem fusedMap1550swap_checked : acceptsGraphIso
    (fused (graph core1550) (root 9) 1 0) DegreeOneSmallSpectrum1506.graph fusedMap1550swap=true := by decide +kernel
theorem certified1550swap : Certified (graph core1550) (root 9) 1 0 :=
  of_native_maps core1550 DegreeOneSmallSpectrum1407.graph DegreeOneSmallSpectrum1506.graph
    sourceMap1550swap fusedMap1550swap sourceMap1550swap_checked fusedMap1550swap_checked
    DegreeOneSmallComparisons.comparison1550
#print axioms sourceMap1550swap_checked
#print axioms fusedMap1550swap_checked
#print axioms certified1550swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
