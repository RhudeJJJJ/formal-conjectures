/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0770 : Family 10 := level10.get ⟨1140,by decide⟩
def sourceMap0770 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0770 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0770_checked : acceptsGraphIso
    (source (graph core0770) (root 10) 0 0) DegreeOneSmallSpectrum1804.graph sourceMap0770=true := by decide +kernel
theorem fusedMap0770_checked : acceptsGraphIso
    (fused (graph core0770) (root 10) 0 0) DegreeOneSmallSpectrum1801.graph fusedMap0770=true := by decide +kernel
theorem certified0770 : Certified (graph core0770) (root 10) 0 0 :=
  of_native_maps core0770 DegreeOneSmallSpectrum1804.graph DegreeOneSmallSpectrum1801.graph
    sourceMap0770 fusedMap0770 sourceMap0770_checked fusedMap0770_checked
    DegreeTwoThreeFiniteComparisons.comparison0770
#print axioms sourceMap0770_checked
#print axioms fusedMap0770_checked
#print axioms certified0770
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
