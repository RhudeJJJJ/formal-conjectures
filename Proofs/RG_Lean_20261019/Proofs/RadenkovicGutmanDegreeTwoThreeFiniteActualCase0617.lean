/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0617 : Family 10 := level10.get ⟨745,by decide⟩
def sourceMap0617 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0617 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0617_checked : acceptsGraphIso
    (source (graph core0617) (root 10) 0 0) DegreeTwoThreeSpectrum1469.graph sourceMap0617=true := by decide +kernel
theorem fusedMap0617_checked : acceptsGraphIso
    (fused (graph core0617) (root 10) 0 0) DegreeOneSmallSpectrum1372.graph fusedMap0617=true := by decide +kernel
theorem certified0617 : Certified (graph core0617) (root 10) 0 0 :=
  of_native_maps core0617 DegreeTwoThreeSpectrum1469.graph DegreeOneSmallSpectrum1372.graph
    sourceMap0617 fusedMap0617 sourceMap0617_checked fusedMap0617_checked
    DegreeTwoThreeFiniteComparisons.comparison0617
#print axioms sourceMap0617_checked
#print axioms fusedMap0617_checked
#print axioms certified0617
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
