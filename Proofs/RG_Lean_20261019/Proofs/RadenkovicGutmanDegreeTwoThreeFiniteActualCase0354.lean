/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0354 : Family 9 := level9.get ⟨567,by decide⟩
def sourceMap0354 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0354 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0354_checked : acceptsGraphIso
    (source (graph core0354) (root 9) 0 0) DegreeTwoThreeSpectrum548.graph sourceMap0354=true := by decide +kernel
theorem fusedMap0354_checked : acceptsGraphIso
    (fused (graph core0354) (root 9) 0 0) DegreeOneSmallSpectrum638.graph fusedMap0354=true := by decide +kernel
theorem certified0354 : Certified (graph core0354) (root 9) 0 0 :=
  of_native_maps core0354 DegreeTwoThreeSpectrum548.graph DegreeOneSmallSpectrum638.graph
    sourceMap0354 fusedMap0354 sourceMap0354_checked fusedMap0354_checked
    DegreeTwoThreeFiniteComparisons.comparison0354
#print axioms sourceMap0354_checked
#print axioms fusedMap0354_checked
#print axioms certified0354
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
