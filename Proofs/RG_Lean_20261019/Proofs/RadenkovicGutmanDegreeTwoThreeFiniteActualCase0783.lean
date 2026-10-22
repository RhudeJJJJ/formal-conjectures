/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0783 : Family 10 := level10.get ⟨1168,by decide⟩
def sourceMap0783 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0783 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0783_checked : acceptsGraphIso
    (source (graph core0783) (root 10) 0 0) DegreeOneSmallSpectrum1171.graph sourceMap0783=true := by decide +kernel
theorem fusedMap0783_checked : acceptsGraphIso
    (fused (graph core0783) (root 10) 0 0) DegreeOneSmallSpectrum1170.graph fusedMap0783=true := by decide +kernel
theorem certified0783 : Certified (graph core0783) (root 10) 0 0 :=
  of_native_maps core0783 DegreeOneSmallSpectrum1171.graph DegreeOneSmallSpectrum1170.graph
    sourceMap0783 fusedMap0783 sourceMap0783_checked fusedMap0783_checked
    DegreeTwoThreeFiniteComparisons.comparison0783
#print axioms sourceMap0783_checked
#print axioms fusedMap0783_checked
#print axioms certified0783
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
