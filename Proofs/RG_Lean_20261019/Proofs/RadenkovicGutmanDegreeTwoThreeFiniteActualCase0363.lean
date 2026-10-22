/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0363 : Family 9 := level9.get ⟨588,by decide⟩
def sourceMap0363 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0363 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0363_checked : acceptsGraphIso
    (source (graph core0363) (root 9) 0 0) DegreeOneSmallSpectrum681.graph sourceMap0363=true := by decide +kernel
theorem fusedMap0363_checked : acceptsGraphIso
    (fused (graph core0363) (root 9) 0 0) DegreeOneSmallSpectrum680.graph fusedMap0363=true := by decide +kernel
theorem certified0363 : Certified (graph core0363) (root 9) 0 0 :=
  of_native_maps core0363 DegreeOneSmallSpectrum681.graph DegreeOneSmallSpectrum680.graph
    sourceMap0363 fusedMap0363 sourceMap0363_checked fusedMap0363_checked
    DegreeTwoThreeFiniteComparisons.comparison0363
#print axioms sourceMap0363_checked
#print axioms fusedMap0363_checked
#print axioms certified0363
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
