/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0858 : Family 10 := level10.get ⟨590,by decide⟩
def sourceMap0858 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0858 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0858_checked : acceptsGraphIso
    (source (graph core0858) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2083.graph sourceMap0858=true := by decide +kernel
theorem fusedMap0858_checked : acceptsGraphIso
    (fused (graph core0858) (root 10) 2 2) DegreeTwoThreeSpectrum5264.graph fusedMap0858=true := by decide +kernel
theorem certified0858 : Certified (graph core0858) (root 10) 2 2 :=
  of_native_maps core0858 DegreeOneMiddleResidualSpectrum2083.graph DegreeTwoThreeSpectrum5264.graph
    sourceMap0858 fusedMap0858 sourceMap0858_checked fusedMap0858_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0858
#print axioms sourceMap0858_checked
#print axioms fusedMap0858_checked
#print axioms certified0858
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
