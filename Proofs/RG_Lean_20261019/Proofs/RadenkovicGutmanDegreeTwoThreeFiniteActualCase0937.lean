/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0937 : Family 10 := level10.get ⟨1551,by decide⟩
def sourceMap0937 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0937 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0937_checked : acceptsGraphIso
    (source (graph core0937) (root 10) 0 0) DegreeTwoThreeSpectrum1694.graph sourceMap0937=true := by decide +kernel
theorem fusedMap0937_checked : acceptsGraphIso
    (fused (graph core0937) (root 10) 0 0) DegreeOneSmallSpectrum1571.graph fusedMap0937=true := by decide +kernel
theorem certified0937 : Certified (graph core0937) (root 10) 0 0 :=
  of_native_maps core0937 DegreeTwoThreeSpectrum1694.graph DegreeOneSmallSpectrum1571.graph
    sourceMap0937 fusedMap0937 sourceMap0937_checked fusedMap0937_checked
    DegreeTwoThreeFiniteComparisons.comparison0937
#print axioms sourceMap0937_checked
#print axioms fusedMap0937_checked
#print axioms certified0937
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
