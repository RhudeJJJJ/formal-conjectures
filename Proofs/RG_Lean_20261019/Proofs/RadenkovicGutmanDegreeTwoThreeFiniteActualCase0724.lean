/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0724 : Family 10 := level10.get ⟨1023,by decide⟩
def sourceMap0724 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0724 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0724_checked : acceptsGraphIso
    (source (graph core0724) (root 10) 0 0) DegreeTwoThreeSpectrum1337.graph sourceMap0724=true := by decide +kernel
theorem fusedMap0724_checked : acceptsGraphIso
    (fused (graph core0724) (root 10) 0 0) DegreeOneSmallSpectrum1595.graph fusedMap0724=true := by decide +kernel
theorem certified0724 : Certified (graph core0724) (root 10) 0 0 :=
  of_native_maps core0724 DegreeTwoThreeSpectrum1337.graph DegreeOneSmallSpectrum1595.graph
    sourceMap0724 fusedMap0724 sourceMap0724_checked fusedMap0724_checked
    DegreeTwoThreeFiniteComparisons.comparison0724
#print axioms sourceMap0724_checked
#print axioms fusedMap0724_checked
#print axioms certified0724
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
