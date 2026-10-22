/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0456 : Family 10 := level10.get ⟨253,by decide⟩
def sourceMap0456 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0456 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0456_checked : acceptsGraphIso
    (source (graph core0456) (root 10) 0 0) DegreeOneSmallSpectrum1051.graph sourceMap0456=true := by decide +kernel
theorem fusedMap0456_checked : acceptsGraphIso
    (fused (graph core0456) (root 10) 0 0) DegreeOneSmallSpectrum1238.graph fusedMap0456=true := by decide +kernel
theorem certified0456 : Certified (graph core0456) (root 10) 0 0 :=
  of_native_maps core0456 DegreeOneSmallSpectrum1051.graph DegreeOneSmallSpectrum1238.graph
    sourceMap0456 fusedMap0456 sourceMap0456_checked fusedMap0456_checked
    DegreeTwoThreeFiniteComparisons.comparison0456
#print axioms sourceMap0456_checked
#print axioms fusedMap0456_checked
#print axioms certified0456
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
