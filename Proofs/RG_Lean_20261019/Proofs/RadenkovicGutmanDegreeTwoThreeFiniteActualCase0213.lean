/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0213 : Family 9 := level9.get ⟨203,by decide⟩
def sourceMap0213 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0213 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0213_checked : acceptsGraphIso
    (source (graph core0213) (root 9) 0 0) DegreeTwoThreeSpectrum586.graph sourceMap0213=true := by decide +kernel
theorem fusedMap0213_checked : acceptsGraphIso
    (fused (graph core0213) (root 9) 0 0) DegreeOneSmallSpectrum503.graph fusedMap0213=true := by decide +kernel
theorem certified0213 : Certified (graph core0213) (root 9) 0 0 :=
  of_native_maps core0213 DegreeTwoThreeSpectrum586.graph DegreeOneSmallSpectrum503.graph
    sourceMap0213 fusedMap0213 sourceMap0213_checked fusedMap0213_checked
    DegreeTwoThreeFiniteComparisons.comparison0213
#print axioms sourceMap0213_checked
#print axioms fusedMap0213_checked
#print axioms certified0213
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
