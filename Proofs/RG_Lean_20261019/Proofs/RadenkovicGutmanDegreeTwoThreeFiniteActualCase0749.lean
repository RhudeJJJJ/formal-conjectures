/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0749 : Family 10 := level10.get ⟨1085,by decide⟩
def sourceMap0749 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0749 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0749_checked : acceptsGraphIso
    (source (graph core0749) (root 10) 0 0) DegreeOneSmallSpectrum1082.graph sourceMap0749=true := by decide +kernel
theorem fusedMap0749_checked : acceptsGraphIso
    (fused (graph core0749) (root 10) 0 0) DegreeOneSmallSpectrum1081.graph fusedMap0749=true := by decide +kernel
theorem certified0749 : Certified (graph core0749) (root 10) 0 0 :=
  of_native_maps core0749 DegreeOneSmallSpectrum1082.graph DegreeOneSmallSpectrum1081.graph
    sourceMap0749 fusedMap0749 sourceMap0749_checked fusedMap0749_checked
    DegreeTwoThreeFiniteComparisons.comparison0749
#print axioms sourceMap0749_checked
#print axioms fusedMap0749_checked
#print axioms certified0749
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
