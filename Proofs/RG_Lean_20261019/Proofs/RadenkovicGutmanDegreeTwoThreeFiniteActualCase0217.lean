/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0217 : Family 9 := level9.get ⟨216,by decide⟩
def sourceMap0217 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0217 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0217_checked : acceptsGraphIso
    (source (graph core0217) (root 9) 0 0) SmallGeFourSpectrum137.graph sourceMap0217=true := by decide +kernel
theorem fusedMap0217_checked : acceptsGraphIso
    (fused (graph core0217) (root 9) 0 0) SmallGeFourSpectrum102.graph fusedMap0217=true := by decide +kernel
theorem certified0217 : Certified (graph core0217) (root 9) 0 0 :=
  of_native_maps core0217 SmallGeFourSpectrum137.graph SmallGeFourSpectrum102.graph
    sourceMap0217 fusedMap0217 sourceMap0217_checked fusedMap0217_checked
    DegreeTwoThreeFiniteComparisons.comparison0217
#print axioms sourceMap0217_checked
#print axioms fusedMap0217_checked
#print axioms certified0217
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
