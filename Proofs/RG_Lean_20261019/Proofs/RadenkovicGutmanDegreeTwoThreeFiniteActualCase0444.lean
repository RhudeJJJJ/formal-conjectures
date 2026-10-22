/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0444 : Family 10 := level10.get ⟨205,by decide⟩
def sourceMap0444 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0444 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0444_checked : acceptsGraphIso
    (source (graph core0444) (root 10) 0 0) DegreeTwoThreeSpectrum890.graph sourceMap0444=true := by decide +kernel
theorem fusedMap0444_checked : acceptsGraphIso
    (fused (graph core0444) (root 10) 0 0) DegreeOneSmallSpectrum1055.graph fusedMap0444=true := by decide +kernel
theorem certified0444 : Certified (graph core0444) (root 10) 0 0 :=
  of_native_maps core0444 DegreeTwoThreeSpectrum890.graph DegreeOneSmallSpectrum1055.graph
    sourceMap0444 fusedMap0444 sourceMap0444_checked fusedMap0444_checked
    DegreeTwoThreeFiniteComparisons.comparison0444
#print axioms sourceMap0444_checked
#print axioms fusedMap0444_checked
#print axioms certified0444
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
