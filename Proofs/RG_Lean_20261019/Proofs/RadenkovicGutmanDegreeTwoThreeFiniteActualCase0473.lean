/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0473 : Family 10 := level10.get ⟨308,by decide⟩
def sourceMap0473 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0473 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0473_checked : acceptsGraphIso
    (source (graph core0473) (root 10) 0 0) DegreeTwoThreeSpectrum914.graph sourceMap0473=true := by decide +kernel
theorem fusedMap0473_checked : acceptsGraphIso
    (fused (graph core0473) (root 10) 0 0) DegreeOneSmallSpectrum1360.graph fusedMap0473=true := by decide +kernel
theorem certified0473 : Certified (graph core0473) (root 10) 0 0 :=
  of_native_maps core0473 DegreeTwoThreeSpectrum914.graph DegreeOneSmallSpectrum1360.graph
    sourceMap0473 fusedMap0473 sourceMap0473_checked fusedMap0473_checked
    DegreeTwoThreeFiniteComparisons.comparison0473
#print axioms sourceMap0473_checked
#print axioms fusedMap0473_checked
#print axioms certified0473
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
