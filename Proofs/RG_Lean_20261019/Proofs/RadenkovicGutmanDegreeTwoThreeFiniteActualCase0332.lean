/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0332 : Family 9 := level9.get ⟨511,by decide⟩
def sourceMap0332 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0332 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0332_checked : acceptsGraphIso
    (source (graph core0332) (root 9) 0 0) SmallGeFourSpectrum189.graph sourceMap0332=true := by decide +kernel
theorem fusedMap0332_checked : acceptsGraphIso
    (fused (graph core0332) (root 9) 0 0) SmallGeFourSpectrum177.graph fusedMap0332=true := by decide +kernel
theorem certified0332 : Certified (graph core0332) (root 9) 0 0 :=
  of_native_maps core0332 SmallGeFourSpectrum189.graph SmallGeFourSpectrum177.graph
    sourceMap0332 fusedMap0332 sourceMap0332_checked fusedMap0332_checked
    DegreeTwoThreeFiniteComparisons.comparison0332
#print axioms sourceMap0332_checked
#print axioms fusedMap0332_checked
#print axioms certified0332
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
