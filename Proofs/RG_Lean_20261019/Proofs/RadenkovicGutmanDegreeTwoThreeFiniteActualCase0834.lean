/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0834 : Family 10 := level10.get ⟨1290,by decide⟩
def sourceMap0834 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0834 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0834_checked : acceptsGraphIso
    (source (graph core0834) (root 10) 0 0) DegreeOneSmallSpectrum1337.graph sourceMap0834=true := by decide +kernel
theorem fusedMap0834_checked : acceptsGraphIso
    (fused (graph core0834) (root 10) 0 0) DegreeOneSmallSpectrum1336.graph fusedMap0834=true := by decide +kernel
theorem certified0834 : Certified (graph core0834) (root 10) 0 0 :=
  of_native_maps core0834 DegreeOneSmallSpectrum1337.graph DegreeOneSmallSpectrum1336.graph
    sourceMap0834 fusedMap0834 sourceMap0834_checked fusedMap0834_checked
    DegreeTwoThreeFiniteComparisons.comparison0834
#print axioms sourceMap0834_checked
#print axioms fusedMap0834_checked
#print axioms certified0834
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
