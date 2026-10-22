/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0067 : Family 8 := level8.get ⟨24,by decide⟩
def sourceMap0067 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0067 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0067_checked : acceptsGraphIso
    (source (graph core0067) (root 8) 0 0) DegreeOneSmallSpectrum174.graph sourceMap0067=true := by decide +kernel
theorem fusedMap0067_checked : acceptsGraphIso
    (fused (graph core0067) (root 8) 0 0) DegreeOneSmallSpectrum216.graph fusedMap0067=true := by decide +kernel
theorem certified0067 : Certified (graph core0067) (root 8) 0 0 :=
  of_native_maps core0067 DegreeOneSmallSpectrum174.graph DegreeOneSmallSpectrum216.graph
    sourceMap0067 fusedMap0067 sourceMap0067_checked fusedMap0067_checked
    DegreeTwoThreeFiniteComparisons.comparison0067
#print axioms sourceMap0067_checked
#print axioms fusedMap0067_checked
#print axioms certified0067
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
