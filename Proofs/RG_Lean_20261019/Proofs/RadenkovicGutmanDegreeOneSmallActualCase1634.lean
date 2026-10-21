/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1634 : Family 9 := level9.get ⟨375,by decide⟩
def sourceMap1634 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1634 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1634_checked : acceptsGraphIso
    (source (graph core1634) (root 9) 0 1) DegreeOneSmallSpectrum1830.graph sourceMap1634=true := by decide +kernel
theorem fusedMap1634_checked : acceptsGraphIso
    (fused (graph core1634) (root 9) 0 1) DegreeOneSmallSpectrum1137.graph fusedMap1634=true := by decide +kernel
theorem certified1634 : Certified (graph core1634) (root 9) 0 1 :=
  of_native_maps core1634 DegreeOneSmallSpectrum1830.graph DegreeOneSmallSpectrum1137.graph
    sourceMap1634 fusedMap1634 sourceMap1634_checked fusedMap1634_checked
    DegreeOneSmallComparisons.comparison1634
#print axioms sourceMap1634_checked
#print axioms fusedMap1634_checked
#print axioms certified1634
def sourceMap1634swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1634swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1634swap_checked : acceptsGraphIso
    (source (graph core1634) (root 9) 1 0) DegreeOneSmallSpectrum1830.graph sourceMap1634swap=true := by decide +kernel
theorem fusedMap1634swap_checked : acceptsGraphIso
    (fused (graph core1634) (root 9) 1 0) DegreeOneSmallSpectrum1137.graph fusedMap1634swap=true := by decide +kernel
theorem certified1634swap : Certified (graph core1634) (root 9) 1 0 :=
  of_native_maps core1634 DegreeOneSmallSpectrum1830.graph DegreeOneSmallSpectrum1137.graph
    sourceMap1634swap fusedMap1634swap sourceMap1634swap_checked fusedMap1634swap_checked
    DegreeOneSmallComparisons.comparison1634
#print axioms sourceMap1634swap_checked
#print axioms fusedMap1634swap_checked
#print axioms certified1634swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
