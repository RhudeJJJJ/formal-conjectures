/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1131 : Family 8 := level8.get ⟨125,by decide⟩
def sourceMap1131 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1131 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1131_checked : acceptsGraphIso
    (source (graph core1131) (root 8) 0 2) DegreeOneSmallSpectrum1224.graph sourceMap1131=true := by decide +kernel
theorem fusedMap1131_checked : acceptsGraphIso
    (fused (graph core1131) (root 8) 0 2) DegreeOneSmallSpectrum1226.graph fusedMap1131=true := by decide +kernel
theorem certified1131 : Certified (graph core1131) (root 8) 0 2 :=
  of_native_maps core1131 DegreeOneSmallSpectrum1224.graph DegreeOneSmallSpectrum1226.graph
    sourceMap1131 fusedMap1131 sourceMap1131_checked fusedMap1131_checked
    DegreeTwoThreeFiniteComparisons.comparison1131
#print axioms sourceMap1131_checked
#print axioms fusedMap1131_checked
#print axioms certified1131
def sourceMap1131swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1131swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1131swap_checked : acceptsGraphIso
    (source (graph core1131) (root 8) 2 0) DegreeOneSmallSpectrum1224.graph sourceMap1131swap=true := by decide +kernel
theorem fusedMap1131swap_checked : acceptsGraphIso
    (fused (graph core1131) (root 8) 2 0) DegreeOneSmallSpectrum1226.graph fusedMap1131swap=true := by decide +kernel
theorem certified1131swap : Certified (graph core1131) (root 8) 2 0 :=
  of_native_maps core1131 DegreeOneSmallSpectrum1224.graph DegreeOneSmallSpectrum1226.graph
    sourceMap1131swap fusedMap1131swap sourceMap1131swap_checked fusedMap1131swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1131
#print axioms sourceMap1131swap_checked
#print axioms fusedMap1131swap_checked
#print axioms certified1131swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
