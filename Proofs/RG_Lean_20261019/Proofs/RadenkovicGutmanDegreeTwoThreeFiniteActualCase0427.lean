/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0427 : Family 10 := level10.get ⟨143,by decide⟩
def sourceMap0427 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0427 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0427_checked : acceptsGraphIso
    (source (graph core0427) (root 10) 0 0) DegreeOneSmallSpectrum920.graph sourceMap0427=true := by decide +kernel
theorem fusedMap0427_checked : acceptsGraphIso
    (fused (graph core0427) (root 10) 0 0) DegreeOneSmallSpectrum913.graph fusedMap0427=true := by decide +kernel
theorem certified0427 : Certified (graph core0427) (root 10) 0 0 :=
  of_native_maps core0427 DegreeOneSmallSpectrum920.graph DegreeOneSmallSpectrum913.graph
    sourceMap0427 fusedMap0427 sourceMap0427_checked fusedMap0427_checked
    DegreeTwoThreeFiniteComparisons.comparison0427
#print axioms sourceMap0427_checked
#print axioms fusedMap0427_checked
#print axioms certified0427
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
