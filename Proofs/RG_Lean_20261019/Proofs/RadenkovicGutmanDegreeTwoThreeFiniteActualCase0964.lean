/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0964 : Family 10 := level10.get ⟨1616,by decide⟩
def sourceMap0964 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0964 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0964_checked : acceptsGraphIso
    (source (graph core0964) (root 10) 0 0) DegreeOneSmallSpectrum2004.graph sourceMap0964=true := by decide +kernel
theorem fusedMap0964_checked : acceptsGraphIso
    (fused (graph core0964) (root 10) 0 0) DegreeOneSmallSpectrum1700.graph fusedMap0964=true := by decide +kernel
theorem certified0964 : Certified (graph core0964) (root 10) 0 0 :=
  of_native_maps core0964 DegreeOneSmallSpectrum2004.graph DegreeOneSmallSpectrum1700.graph
    sourceMap0964 fusedMap0964 sourceMap0964_checked fusedMap0964_checked
    DegreeTwoThreeFiniteComparisons.comparison0964
#print axioms sourceMap0964_checked
#print axioms fusedMap0964_checked
#print axioms certified0964
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
