/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0327 : Family 9 := level9.get ⟨502,by decide⟩
def sourceMap0327 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,5,6,7,8,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0327 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0327_checked : acceptsGraphIso
    (source (graph core0327) (root 9) 0 0) SmallGeFourSpectrum131.graph sourceMap0327=true := by decide +kernel
theorem fusedMap0327_checked : acceptsGraphIso
    (fused (graph core0327) (root 9) 0 0) SmallGeFourSpectrum190.graph fusedMap0327=true := by decide +kernel
theorem certified0327 : Certified (graph core0327) (root 9) 0 0 :=
  of_native_maps core0327 SmallGeFourSpectrum131.graph SmallGeFourSpectrum190.graph
    sourceMap0327 fusedMap0327 sourceMap0327_checked fusedMap0327_checked
    DegreeTwoThreeFiniteComparisons.comparison0327
#print axioms sourceMap0327_checked
#print axioms fusedMap0327_checked
#print axioms certified0327
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
