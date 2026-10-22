/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0259 : Family 9 := level9.get ⟨333,by decide⟩
def sourceMap0259 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0259 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0259_checked : acceptsGraphIso
    (source (graph core0259) (root 9) 0 0) DegreeTwoThreeSpectrum544.graph sourceMap0259=true := by decide +kernel
theorem fusedMap0259_checked : acceptsGraphIso
    (fused (graph core0259) (root 9) 0 0) DegreeOneSmallSpectrum639.graph fusedMap0259=true := by decide +kernel
theorem certified0259 : Certified (graph core0259) (root 9) 0 0 :=
  of_native_maps core0259 DegreeTwoThreeSpectrum544.graph DegreeOneSmallSpectrum639.graph
    sourceMap0259 fusedMap0259 sourceMap0259_checked fusedMap0259_checked
    DegreeTwoThreeFiniteComparisons.comparison0259
#print axioms sourceMap0259_checked
#print axioms fusedMap0259_checked
#print axioms certified0259
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
