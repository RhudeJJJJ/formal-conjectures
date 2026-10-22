/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0979 : Family 10 := level10.get ⟨1648,by decide⟩
def sourceMap0979 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0979 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0979_checked : acceptsGraphIso
    (source (graph core0979) (root 10) 0 0) DegreeOneSmallSpectrum1781.graph sourceMap0979=true := by decide +kernel
theorem fusedMap0979_checked : acceptsGraphIso
    (fused (graph core0979) (root 10) 0 0) DegreeOneSmallSpectrum1780.graph fusedMap0979=true := by decide +kernel
theorem certified0979 : Certified (graph core0979) (root 10) 0 0 :=
  of_native_maps core0979 DegreeOneSmallSpectrum1781.graph DegreeOneSmallSpectrum1780.graph
    sourceMap0979 fusedMap0979 sourceMap0979_checked fusedMap0979_checked
    DegreeTwoThreeFiniteComparisons.comparison0979
#print axioms sourceMap0979_checked
#print axioms fusedMap0979_checked
#print axioms certified0979
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
