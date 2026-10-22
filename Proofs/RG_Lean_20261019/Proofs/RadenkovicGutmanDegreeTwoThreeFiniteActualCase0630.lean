/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0630 : Family 10 := level10.get ⟨782,by decide⟩
def sourceMap0630 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0630 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0630_checked : acceptsGraphIso
    (source (graph core0630) (root 10) 0 0) DegreeOneSmallSpectrum1690.graph sourceMap0630=true := by decide +kernel
theorem fusedMap0630_checked : acceptsGraphIso
    (fused (graph core0630) (root 10) 0 0) DegreeOneSmallSpectrum1416.graph fusedMap0630=true := by decide +kernel
theorem certified0630 : Certified (graph core0630) (root 10) 0 0 :=
  of_native_maps core0630 DegreeOneSmallSpectrum1690.graph DegreeOneSmallSpectrum1416.graph
    sourceMap0630 fusedMap0630 sourceMap0630_checked fusedMap0630_checked
    DegreeTwoThreeFiniteComparisons.comparison0630
#print axioms sourceMap0630_checked
#print axioms fusedMap0630_checked
#print axioms certified0630
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
