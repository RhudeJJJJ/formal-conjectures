/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0618 : Family 10 := level10.get ⟨748,by decide⟩
def sourceMap0618 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0618 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0618_checked : acceptsGraphIso
    (source (graph core0618) (root 10) 0 0) DegreeTwoThreeSpectrum1434.graph sourceMap0618=true := by decide +kernel
theorem fusedMap0618_checked : acceptsGraphIso
    (fused (graph core0618) (root 10) 0 0) DegreeOneSmallSpectrum1375.graph fusedMap0618=true := by decide +kernel
theorem certified0618 : Certified (graph core0618) (root 10) 0 0 :=
  of_native_maps core0618 DegreeTwoThreeSpectrum1434.graph DegreeOneSmallSpectrum1375.graph
    sourceMap0618 fusedMap0618 sourceMap0618_checked fusedMap0618_checked
    DegreeTwoThreeFiniteComparisons.comparison0618
#print axioms sourceMap0618_checked
#print axioms fusedMap0618_checked
#print axioms certified0618
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
