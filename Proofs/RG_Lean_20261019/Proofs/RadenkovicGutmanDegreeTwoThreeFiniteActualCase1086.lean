/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1086 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap1086 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1086 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1086_checked : acceptsGraphIso
    (source (graph core1086) (root 7) 0 2) DegreeOneSmallSpectrum787.graph sourceMap1086=true := by decide +kernel
theorem fusedMap1086_checked : acceptsGraphIso
    (fused (graph core1086) (root 7) 0 2) DegreeOneSmallSpectrum502.graph fusedMap1086=true := by decide +kernel
theorem certified1086 : Certified (graph core1086) (root 7) 0 2 :=
  of_native_maps core1086 DegreeOneSmallSpectrum787.graph DegreeOneSmallSpectrum502.graph
    sourceMap1086 fusedMap1086 sourceMap1086_checked fusedMap1086_checked
    DegreeTwoThreeFiniteComparisons.comparison1086
#print axioms sourceMap1086_checked
#print axioms fusedMap1086_checked
#print axioms certified1086
def sourceMap1086swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1086swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1086swap_checked : acceptsGraphIso
    (source (graph core1086) (root 7) 2 0) DegreeOneSmallSpectrum787.graph sourceMap1086swap=true := by decide +kernel
theorem fusedMap1086swap_checked : acceptsGraphIso
    (fused (graph core1086) (root 7) 2 0) DegreeOneSmallSpectrum502.graph fusedMap1086swap=true := by decide +kernel
theorem certified1086swap : Certified (graph core1086) (root 7) 2 0 :=
  of_native_maps core1086 DegreeOneSmallSpectrum787.graph DegreeOneSmallSpectrum502.graph
    sourceMap1086swap fusedMap1086swap sourceMap1086swap_checked fusedMap1086swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1086
#print axioms sourceMap1086swap_checked
#print axioms fusedMap1086swap_checked
#print axioms certified1086swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
