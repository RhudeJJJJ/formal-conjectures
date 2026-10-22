/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0824 : Family 10 := level10.get ⟨1271,by decide⟩
def sourceMap0824 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0824 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0824_checked : acceptsGraphIso
    (source (graph core0824) (root 10) 0 0) DegreeOneSmallSpectrum1927.graph sourceMap0824=true := by decide +kernel
theorem fusedMap0824_checked : acceptsGraphIso
    (fused (graph core0824) (root 10) 0 0) DegreeOneSmallSpectrum1922.graph fusedMap0824=true := by decide +kernel
theorem certified0824 : Certified (graph core0824) (root 10) 0 0 :=
  of_native_maps core0824 DegreeOneSmallSpectrum1927.graph DegreeOneSmallSpectrum1922.graph
    sourceMap0824 fusedMap0824 sourceMap0824_checked fusedMap0824_checked
    DegreeTwoThreeFiniteComparisons.comparison0824
#print axioms sourceMap0824_checked
#print axioms fusedMap0824_checked
#print axioms certified0824
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
