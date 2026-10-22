/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0471 : Family 10 := level10.get ⟨301,by decide⟩
def sourceMap0471 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0471 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0471_checked : acceptsGraphIso
    (source (graph core0471) (root 10) 0 0) DegreeOneSmallSpectrum1031.graph sourceMap0471=true := by decide +kernel
theorem fusedMap0471_checked : acceptsGraphIso
    (fused (graph core0471) (root 10) 0 0) DegreeOneSmallSpectrum1338.graph fusedMap0471=true := by decide +kernel
theorem certified0471 : Certified (graph core0471) (root 10) 0 0 :=
  of_native_maps core0471 DegreeOneSmallSpectrum1031.graph DegreeOneSmallSpectrum1338.graph
    sourceMap0471 fusedMap0471 sourceMap0471_checked fusedMap0471_checked
    DegreeTwoThreeFiniteComparisons.comparison0471
#print axioms sourceMap0471_checked
#print axioms fusedMap0471_checked
#print axioms certified0471
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
