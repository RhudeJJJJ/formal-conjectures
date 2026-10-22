/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0814 : Family 10 := level10.get ⟨1246,by decide⟩
def sourceMap0814 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0814 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0814_checked : acceptsGraphIso
    (source (graph core0814) (root 10) 0 0) DegreeTwoThreeSpectrum1428.graph sourceMap0814=true := by decide +kernel
theorem fusedMap0814_checked : acceptsGraphIso
    (fused (graph core0814) (root 10) 0 0) DegreeOneSmallSpectrum1895.graph fusedMap0814=true := by decide +kernel
theorem certified0814 : Certified (graph core0814) (root 10) 0 0 :=
  of_native_maps core0814 DegreeTwoThreeSpectrum1428.graph DegreeOneSmallSpectrum1895.graph
    sourceMap0814 fusedMap0814 sourceMap0814_checked fusedMap0814_checked
    DegreeTwoThreeFiniteComparisons.comparison0814
#print axioms sourceMap0814_checked
#print axioms fusedMap0814_checked
#print axioms certified0814
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
