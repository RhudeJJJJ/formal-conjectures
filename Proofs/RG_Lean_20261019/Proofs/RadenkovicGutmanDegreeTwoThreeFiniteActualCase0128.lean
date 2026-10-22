/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0128 : Family 8 := level8.get ⟨194,by decide⟩
def sourceMap0128 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0128 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0128_checked : acceptsGraphIso
    (source (graph core0128) (root 8) 0 0) DegreeTwoThreeSpectrum218.graph sourceMap0128=true := by decide +kernel
theorem fusedMap0128_checked : acceptsGraphIso
    (fused (graph core0128) (root 8) 0 0) DegreeOneSmallSpectrum242.graph fusedMap0128=true := by decide +kernel
theorem certified0128 : Certified (graph core0128) (root 8) 0 0 :=
  of_native_maps core0128 DegreeTwoThreeSpectrum218.graph DegreeOneSmallSpectrum242.graph
    sourceMap0128 fusedMap0128 sourceMap0128_checked fusedMap0128_checked
    DegreeTwoThreeFiniteComparisons.comparison0128
#print axioms sourceMap0128_checked
#print axioms fusedMap0128_checked
#print axioms certified0128
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
