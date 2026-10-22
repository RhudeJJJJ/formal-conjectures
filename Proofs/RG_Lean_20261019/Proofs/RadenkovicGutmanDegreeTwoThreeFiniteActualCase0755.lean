/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0755 : Family 10 := level10.get ⟨1101,by decide⟩
def sourceMap0755 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0755 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0755_checked : acceptsGraphIso
    (source (graph core0755) (root 10) 0 0) DegreeOneSmallSpectrum1719.graph sourceMap0755=true := by decide +kernel
theorem fusedMap0755_checked : acceptsGraphIso
    (fused (graph core0755) (root 10) 0 0) DegreeOneSmallSpectrum1717.graph fusedMap0755=true := by decide +kernel
theorem certified0755 : Certified (graph core0755) (root 10) 0 0 :=
  of_native_maps core0755 DegreeOneSmallSpectrum1719.graph DegreeOneSmallSpectrum1717.graph
    sourceMap0755 fusedMap0755 sourceMap0755_checked fusedMap0755_checked
    DegreeTwoThreeFiniteComparisons.comparison0755
#print axioms sourceMap0755_checked
#print axioms fusedMap0755_checked
#print axioms certified0755
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
