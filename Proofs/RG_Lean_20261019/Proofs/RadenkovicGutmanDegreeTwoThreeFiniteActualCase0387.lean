/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0387 : Family 9 := level9.get ⟨650,by decide⟩
def sourceMap0387 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0387 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0387_checked : acceptsGraphIso
    (source (graph core0387) (root 9) 0 0) SmallGeFourSpectrum221.graph sourceMap0387=true := by decide +kernel
theorem fusedMap0387_checked : acceptsGraphIso
    (fused (graph core0387) (root 9) 0 0) SmallGeFourSpectrum179.graph fusedMap0387=true := by decide +kernel
theorem certified0387 : Certified (graph core0387) (root 9) 0 0 :=
  of_native_maps core0387 SmallGeFourSpectrum221.graph SmallGeFourSpectrum179.graph
    sourceMap0387 fusedMap0387 sourceMap0387_checked fusedMap0387_checked
    DegreeTwoThreeFiniteComparisons.comparison0387
#print axioms sourceMap0387_checked
#print axioms fusedMap0387_checked
#print axioms certified0387
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
