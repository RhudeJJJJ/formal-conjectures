/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0920 : Family 10 := level10.get ⟨1495,by decide⟩
def sourceMap0920 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0920 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0920_checked : acceptsGraphIso
    (source (graph core0920) (root 10) 0 0) DegreeOneSmallSpectrum1023.graph sourceMap0920=true := by decide +kernel
theorem fusedMap0920_checked : acceptsGraphIso
    (fused (graph core0920) (root 10) 0 0) DegreeOneSmallSpectrum1022.graph fusedMap0920=true := by decide +kernel
theorem certified0920 : Certified (graph core0920) (root 10) 0 0 :=
  of_native_maps core0920 DegreeOneSmallSpectrum1023.graph DegreeOneSmallSpectrum1022.graph
    sourceMap0920 fusedMap0920 sourceMap0920_checked fusedMap0920_checked
    DegreeTwoThreeFiniteComparisons.comparison0920
#print axioms sourceMap0920_checked
#print axioms fusedMap0920_checked
#print axioms certified0920
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
