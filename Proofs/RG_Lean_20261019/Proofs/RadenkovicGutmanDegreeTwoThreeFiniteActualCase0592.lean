/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0592 : Family 10 := level10.get ⟨670,by decide⟩
def sourceMap0592 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0592 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0592_checked : acceptsGraphIso
    (source (graph core0592) (root 10) 0 0) DegreeOneSmallSpectrum1285.graph sourceMap0592=true := by decide +kernel
theorem fusedMap0592_checked : acceptsGraphIso
    (fused (graph core0592) (root 10) 0 0) DegreeOneSmallSpectrum1282.graph fusedMap0592=true := by decide +kernel
theorem certified0592 : Certified (graph core0592) (root 10) 0 0 :=
  of_native_maps core0592 DegreeOneSmallSpectrum1285.graph DegreeOneSmallSpectrum1282.graph
    sourceMap0592 fusedMap0592 sourceMap0592_checked fusedMap0592_checked
    DegreeTwoThreeFiniteComparisons.comparison0592
#print axioms sourceMap0592_checked
#print axioms fusedMap0592_checked
#print axioms certified0592
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
