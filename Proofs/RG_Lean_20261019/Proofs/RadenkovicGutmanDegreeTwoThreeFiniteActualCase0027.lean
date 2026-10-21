/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0027 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap0027 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0027 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,5,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap0027_checked : acceptsGraphIso
    (source (graph core0027) (root 7) 0 0) DegreeOneSmallSpectrum074.graph sourceMap0027=true := by decide +kernel
theorem fusedMap0027_checked : acceptsGraphIso
    (fused (graph core0027) (root 7) 0 0) DegreeOneSmallSpectrum086.graph fusedMap0027=true := by decide +kernel
theorem certified0027 : Certified (graph core0027) (root 7) 0 0 :=
  of_native_maps core0027 DegreeOneSmallSpectrum074.graph DegreeOneSmallSpectrum086.graph
    sourceMap0027 fusedMap0027 sourceMap0027_checked fusedMap0027_checked
    DegreeTwoThreeFiniteComparisons.comparison0027
#print axioms sourceMap0027_checked
#print axioms fusedMap0027_checked
#print axioms certified0027
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
