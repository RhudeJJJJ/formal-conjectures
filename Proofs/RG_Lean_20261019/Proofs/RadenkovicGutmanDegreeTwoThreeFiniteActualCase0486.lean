/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0486 : Family 10 := level10.get ⟨353,by decide⟩
def sourceMap0486 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0486 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0486_checked : acceptsGraphIso
    (source (graph core0486) (root 10) 0 0) DegreeOneSmallSpectrum1384.graph sourceMap0486=true := by decide +kernel
theorem fusedMap0486_checked : acceptsGraphIso
    (fused (graph core0486) (root 10) 0 0) DegreeOneSmallSpectrum1339.graph fusedMap0486=true := by decide +kernel
theorem certified0486 : Certified (graph core0486) (root 10) 0 0 :=
  of_native_maps core0486 DegreeOneSmallSpectrum1384.graph DegreeOneSmallSpectrum1339.graph
    sourceMap0486 fusedMap0486 sourceMap0486_checked fusedMap0486_checked
    DegreeTwoThreeFiniteComparisons.comparison0486
#print axioms sourceMap0486_checked
#print axioms fusedMap0486_checked
#print axioms certified0486
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
