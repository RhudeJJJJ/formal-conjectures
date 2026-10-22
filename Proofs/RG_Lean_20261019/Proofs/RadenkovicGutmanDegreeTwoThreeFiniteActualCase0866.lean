/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0866 : Family 10 := level10.get ⟨1367,by decide⟩
def sourceMap0866 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0866 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0866_checked : acceptsGraphIso
    (source (graph core0866) (root 10) 0 0) DegreeOneSmallSpectrum1805.graph sourceMap0866=true := by decide +kernel
theorem fusedMap0866_checked : acceptsGraphIso
    (fused (graph core0866) (root 10) 0 0) DegreeOneSmallSpectrum1768.graph fusedMap0866=true := by decide +kernel
theorem certified0866 : Certified (graph core0866) (root 10) 0 0 :=
  of_native_maps core0866 DegreeOneSmallSpectrum1805.graph DegreeOneSmallSpectrum1768.graph
    sourceMap0866 fusedMap0866 sourceMap0866_checked fusedMap0866_checked
    DegreeTwoThreeFiniteComparisons.comparison0866
#print axioms sourceMap0866_checked
#print axioms fusedMap0866_checked
#print axioms certified0866
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
