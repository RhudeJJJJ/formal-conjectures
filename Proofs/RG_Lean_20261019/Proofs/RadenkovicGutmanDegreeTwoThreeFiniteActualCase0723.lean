/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0723 : Family 10 := level10.get ⟨1018,by decide⟩
def sourceMap0723 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0723 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0723_checked : acceptsGraphIso
    (source (graph core0723) (root 10) 0 0) DegreeTwoThreeSpectrum1333.graph sourceMap0723=true := by decide +kernel
theorem fusedMap0723_checked : acceptsGraphIso
    (fused (graph core0723) (root 10) 0 0) DegreeOneSmallSpectrum1582.graph fusedMap0723=true := by decide +kernel
theorem certified0723 : Certified (graph core0723) (root 10) 0 0 :=
  of_native_maps core0723 DegreeTwoThreeSpectrum1333.graph DegreeOneSmallSpectrum1582.graph
    sourceMap0723 fusedMap0723 sourceMap0723_checked fusedMap0723_checked
    DegreeTwoThreeFiniteComparisons.comparison0723
#print axioms sourceMap0723_checked
#print axioms fusedMap0723_checked
#print axioms certified0723
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
