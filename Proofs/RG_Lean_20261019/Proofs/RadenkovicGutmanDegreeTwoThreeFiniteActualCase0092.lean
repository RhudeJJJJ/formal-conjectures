/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0092 : Family 8 := level8.get ⟨105,by decide⟩
def sourceMap0092 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0092 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0092_checked : acceptsGraphIso
    (source (graph core0092) (root 8) 0 0) DegreeTwoThreeSpectrum229.graph sourceMap0092=true := by decide +kernel
theorem fusedMap0092_checked : acceptsGraphIso
    (fused (graph core0092) (root 8) 0 0) DegreeOneSmallSpectrum264.graph fusedMap0092=true := by decide +kernel
theorem certified0092 : Certified (graph core0092) (root 8) 0 0 :=
  of_native_maps core0092 DegreeTwoThreeSpectrum229.graph DegreeOneSmallSpectrum264.graph
    sourceMap0092 fusedMap0092 sourceMap0092_checked fusedMap0092_checked
    DegreeTwoThreeFiniteComparisons.comparison0092
#print axioms sourceMap0092_checked
#print axioms fusedMap0092_checked
#print axioms certified0092
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
