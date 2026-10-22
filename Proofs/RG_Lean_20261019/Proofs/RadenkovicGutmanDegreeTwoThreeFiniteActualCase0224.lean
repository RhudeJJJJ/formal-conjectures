/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0224 : Family 9 := level9.get ⟨237,by decide⟩
def sourceMap0224 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0224 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0224_checked : acceptsGraphIso
    (source (graph core0224) (root 9) 0 0) DegreeOneSmallSpectrum529.graph sourceMap0224=true := by decide +kernel
theorem fusedMap0224_checked : acceptsGraphIso
    (fused (graph core0224) (root 9) 0 0) DegreeOneSmallSpectrum513.graph fusedMap0224=true := by decide +kernel
theorem certified0224 : Certified (graph core0224) (root 9) 0 0 :=
  of_native_maps core0224 DegreeOneSmallSpectrum529.graph DegreeOneSmallSpectrum513.graph
    sourceMap0224 fusedMap0224 sourceMap0224_checked fusedMap0224_checked
    DegreeTwoThreeFiniteComparisons.comparison0224
#print axioms sourceMap0224_checked
#print axioms fusedMap0224_checked
#print axioms certified0224
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
