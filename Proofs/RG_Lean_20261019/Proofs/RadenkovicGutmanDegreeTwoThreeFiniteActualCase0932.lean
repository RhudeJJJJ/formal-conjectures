/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0932 : Family 10 := level10.get ⟨1538,by decide⟩
def sourceMap0932 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0932 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0932_checked : acceptsGraphIso
    (source (graph core0932) (root 10) 0 0) DegreeOneSmallSpectrum1553.graph sourceMap0932=true := by decide +kernel
theorem fusedMap0932_checked : acceptsGraphIso
    (fused (graph core0932) (root 10) 0 0) DegreeOneSmallSpectrum1552.graph fusedMap0932=true := by decide +kernel
theorem certified0932 : Certified (graph core0932) (root 10) 0 0 :=
  of_native_maps core0932 DegreeOneSmallSpectrum1553.graph DegreeOneSmallSpectrum1552.graph
    sourceMap0932 fusedMap0932 sourceMap0932_checked fusedMap0932_checked
    DegreeTwoThreeFiniteComparisons.comparison0932
#print axioms sourceMap0932_checked
#print axioms fusedMap0932_checked
#print axioms certified0932
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
