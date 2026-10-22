/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0723 : Family 10 := level10.get ⟨342,by decide⟩
def sourceMap0723 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0723 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0723_checked : acceptsGraphIso
    (source (graph core0723) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1811.graph sourceMap0723=true := by decide +kernel
theorem fusedMap0723_checked : acceptsGraphIso
    (fused (graph core0723) (root 10) 2 2) DegreeTwoThreeSpectrum5601.graph fusedMap0723=true := by decide +kernel
theorem certified0723 : Certified (graph core0723) (root 10) 2 2 :=
  of_native_maps core0723 DegreeOneMiddleResidualSpectrum1811.graph DegreeTwoThreeSpectrum5601.graph
    sourceMap0723 fusedMap0723 sourceMap0723_checked fusedMap0723_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0723
#print axioms sourceMap0723_checked
#print axioms fusedMap0723_checked
#print axioms certified0723
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
