/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0927 : Family 10 := level10.get ⟨1528,by decide⟩
def sourceMap0927 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0927 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0927_checked : acceptsGraphIso
    (source (graph core0927) (root 10) 0 0) DegreeTwoThreeSpectrum1685.graph sourceMap0927=true := by decide +kernel
theorem fusedMap0927_checked : acceptsGraphIso
    (fused (graph core0927) (root 10) 0 0) DegreeOneSmallSpectrum1525.graph fusedMap0927=true := by decide +kernel
theorem certified0927 : Certified (graph core0927) (root 10) 0 0 :=
  of_native_maps core0927 DegreeTwoThreeSpectrum1685.graph DegreeOneSmallSpectrum1525.graph
    sourceMap0927 fusedMap0927 sourceMap0927_checked fusedMap0927_checked
    DegreeTwoThreeFiniteComparisons.comparison0927
#print axioms sourceMap0927_checked
#print axioms fusedMap0927_checked
#print axioms certified0927
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
