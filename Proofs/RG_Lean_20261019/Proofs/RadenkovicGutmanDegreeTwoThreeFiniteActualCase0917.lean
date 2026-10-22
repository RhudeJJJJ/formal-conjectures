/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0917 : Family 10 := level10.get ⟨1481,by decide⟩
def sourceMap0917 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0917 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0917_checked : acceptsGraphIso
    (source (graph core0917) (root 10) 0 0) DegreeOneSmallSpectrum1373.graph sourceMap0917=true := by decide +kernel
theorem fusedMap0917_checked : acceptsGraphIso
    (fused (graph core0917) (root 10) 0 0) DegreeOneSmallSpectrum1369.graph fusedMap0917=true := by decide +kernel
theorem certified0917 : Certified (graph core0917) (root 10) 0 0 :=
  of_native_maps core0917 DegreeOneSmallSpectrum1373.graph DegreeOneSmallSpectrum1369.graph
    sourceMap0917 fusedMap0917 sourceMap0917_checked fusedMap0917_checked
    DegreeTwoThreeFiniteComparisons.comparison0917
#print axioms sourceMap0917_checked
#print axioms fusedMap0917_checked
#print axioms certified0917
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
