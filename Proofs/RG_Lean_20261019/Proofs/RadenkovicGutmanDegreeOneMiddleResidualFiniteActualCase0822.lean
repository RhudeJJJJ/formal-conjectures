/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0822 : Family 10 := level10.get ⟨526,by decide⟩
def sourceMap0822 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0822 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0822_checked : acceptsGraphIso
    (source (graph core0822) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2013.graph sourceMap0822=true := by decide +kernel
theorem fusedMap0822_checked : acceptsGraphIso
    (fused (graph core0822) (root 10) 2 2) DegreeTwoThreeSpectrum5170.graph fusedMap0822=true := by decide +kernel
theorem certified0822 : Certified (graph core0822) (root 10) 2 2 :=
  of_native_maps core0822 DegreeOneMiddleResidualSpectrum2013.graph DegreeTwoThreeSpectrum5170.graph
    sourceMap0822 fusedMap0822 sourceMap0822_checked fusedMap0822_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0822
#print axioms sourceMap0822_checked
#print axioms fusedMap0822_checked
#print axioms certified0822
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
