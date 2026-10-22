/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0912 : Family 10 := level10.get ⟨1470,by decide⟩
def sourceMap0912 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0912 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0912_checked : acceptsGraphIso
    (source (graph core0912) (root 10) 0 0) DegreeOneSmallSpectrum1654.graph sourceMap0912=true := by decide +kernel
theorem fusedMap0912_checked : acceptsGraphIso
    (fused (graph core0912) (root 10) 0 0) DegreeOneSmallSpectrum1637.graph fusedMap0912=true := by decide +kernel
theorem certified0912 : Certified (graph core0912) (root 10) 0 0 :=
  of_native_maps core0912 DegreeOneSmallSpectrum1654.graph DegreeOneSmallSpectrum1637.graph
    sourceMap0912 fusedMap0912 sourceMap0912_checked fusedMap0912_checked
    DegreeTwoThreeFiniteComparisons.comparison0912
#print axioms sourceMap0912_checked
#print axioms fusedMap0912_checked
#print axioms certified0912
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
