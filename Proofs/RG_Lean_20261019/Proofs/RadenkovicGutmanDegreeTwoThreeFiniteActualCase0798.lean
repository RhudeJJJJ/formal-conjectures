/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0798 : Family 10 := level10.get ⟨1206,by decide⟩
def sourceMap0798 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0798 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0798_checked : acceptsGraphIso
    (source (graph core0798) (root 10) 0 0) DegreeOneSmallSpectrum1868.graph sourceMap0798=true := by decide +kernel
theorem fusedMap0798_checked : acceptsGraphIso
    (fused (graph core0798) (root 10) 0 0) DegreeOneSmallSpectrum1859.graph fusedMap0798=true := by decide +kernel
theorem certified0798 : Certified (graph core0798) (root 10) 0 0 :=
  of_native_maps core0798 DegreeOneSmallSpectrum1868.graph DegreeOneSmallSpectrum1859.graph
    sourceMap0798 fusedMap0798 sourceMap0798_checked fusedMap0798_checked
    DegreeTwoThreeFiniteComparisons.comparison0798
#print axioms sourceMap0798_checked
#print axioms fusedMap0798_checked
#print axioms certified0798
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
