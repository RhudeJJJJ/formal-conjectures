/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0929 : Family 10 := level10.get ⟨1533,by decide⟩
def sourceMap0929 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0929 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0929_checked : acceptsGraphIso
    (source (graph core0929) (root 10) 0 0) DegreeTwoThreeSpectrum1688.graph sourceMap0929=true := by decide +kernel
theorem fusedMap0929_checked : acceptsGraphIso
    (fused (graph core0929) (root 10) 0 0) DegreeOneSmallSpectrum1535.graph fusedMap0929=true := by decide +kernel
theorem certified0929 : Certified (graph core0929) (root 10) 0 0 :=
  of_native_maps core0929 DegreeTwoThreeSpectrum1688.graph DegreeOneSmallSpectrum1535.graph
    sourceMap0929 fusedMap0929 sourceMap0929_checked fusedMap0929_checked
    DegreeTwoThreeFiniteComparisons.comparison0929
#print axioms sourceMap0929_checked
#print axioms fusedMap0929_checked
#print axioms certified0929
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
