/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0832 : Family 10 := level10.get ⟨1288,by decide⟩
def sourceMap0832 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0832 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0832_checked : acceptsGraphIso
    (source (graph core0832) (root 10) 0 0) DegreeOneSmallSpectrum1348.graph sourceMap0832=true := by decide +kernel
theorem fusedMap0832_checked : acceptsGraphIso
    (fused (graph core0832) (root 10) 0 0) DegreeOneSmallSpectrum1347.graph fusedMap0832=true := by decide +kernel
theorem certified0832 : Certified (graph core0832) (root 10) 0 0 :=
  of_native_maps core0832 DegreeOneSmallSpectrum1348.graph DegreeOneSmallSpectrum1347.graph
    sourceMap0832 fusedMap0832 sourceMap0832_checked fusedMap0832_checked
    DegreeTwoThreeFiniteComparisons.comparison0832
#print axioms sourceMap0832_checked
#print axioms fusedMap0832_checked
#print axioms certified0832
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
