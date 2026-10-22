/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0062 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap0062 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0062 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0062_checked : acceptsGraphIso
    (source (graph core0062) (root 7) 0 0) DegreeTwoThreeSpectrum144.graph sourceMap0062=true := by decide +kernel
theorem fusedMap0062_checked : acceptsGraphIso
    (fused (graph core0062) (root 7) 0 0) DegreeOneSmallSpectrum155.graph fusedMap0062=true := by decide +kernel
theorem certified0062 : Certified (graph core0062) (root 7) 0 0 :=
  of_native_maps core0062 DegreeTwoThreeSpectrum144.graph DegreeOneSmallSpectrum155.graph
    sourceMap0062 fusedMap0062 sourceMap0062_checked fusedMap0062_checked
    DegreeTwoThreeFiniteComparisons.comparison0062
#print axioms sourceMap0062_checked
#print axioms fusedMap0062_checked
#print axioms certified0062
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
