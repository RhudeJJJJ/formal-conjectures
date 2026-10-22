/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0474 : Family 10 := level10.get ⟨313,by decide⟩
def sourceMap0474 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0474 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0474_checked : acceptsGraphIso
    (source (graph core0474) (root 10) 0 0) DegreeTwoThreeSpectrum915.graph sourceMap0474=true := by decide +kernel
theorem fusedMap0474_checked : acceptsGraphIso
    (fused (graph core0474) (root 10) 0 0) DegreeOneSmallSpectrum1376.graph fusedMap0474=true := by decide +kernel
theorem certified0474 : Certified (graph core0474) (root 10) 0 0 :=
  of_native_maps core0474 DegreeTwoThreeSpectrum915.graph DegreeOneSmallSpectrum1376.graph
    sourceMap0474 fusedMap0474 sourceMap0474_checked fusedMap0474_checked
    DegreeTwoThreeFiniteComparisons.comparison0474
#print axioms sourceMap0474_checked
#print axioms fusedMap0474_checked
#print axioms certified0474
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
