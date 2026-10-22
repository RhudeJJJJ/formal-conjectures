/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0057 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap0057 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0057 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap0057_checked : acceptsGraphIso
    (source (graph core0057) (root 7) 0 0) DegreeTwoThreeSpectrum130.graph sourceMap0057=true := by decide +kernel
theorem fusedMap0057_checked : acceptsGraphIso
    (fused (graph core0057) (root 7) 0 0) DegreeOneSmallSpectrum135.graph fusedMap0057=true := by decide +kernel
theorem certified0057 : Certified (graph core0057) (root 7) 0 0 :=
  of_native_maps core0057 DegreeTwoThreeSpectrum130.graph DegreeOneSmallSpectrum135.graph
    sourceMap0057 fusedMap0057 sourceMap0057_checked fusedMap0057_checked
    DegreeTwoThreeFiniteComparisons.comparison0057
#print axioms sourceMap0057_checked
#print axioms fusedMap0057_checked
#print axioms certified0057
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
