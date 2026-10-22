/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0555 : Family 10 := level10.get ⟨562,by decide⟩
def sourceMap0555 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0555 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0555_checked : acceptsGraphIso
    (source (graph core0555) (root 10) 0 0) DegreeOneSmallSpectrum1671.graph sourceMap0555=true := by decide +kernel
theorem fusedMap0555_checked : acceptsGraphIso
    (fused (graph core0555) (root 10) 0 0) DegreeOneSmallSpectrum1086.graph fusedMap0555=true := by decide +kernel
theorem certified0555 : Certified (graph core0555) (root 10) 0 0 :=
  of_native_maps core0555 DegreeOneSmallSpectrum1671.graph DegreeOneSmallSpectrum1086.graph
    sourceMap0555 fusedMap0555 sourceMap0555_checked fusedMap0555_checked
    DegreeTwoThreeFiniteComparisons.comparison0555
#print axioms sourceMap0555_checked
#print axioms fusedMap0555_checked
#print axioms certified0555
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
