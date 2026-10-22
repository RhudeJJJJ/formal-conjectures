/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1057 : Family 10 := level10.get ⟨1053,by decide⟩
def sourceMap1057 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1057 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1057_checked : acceptsGraphIso
    (source (graph core1057) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2008.graph sourceMap1057=true := by decide +kernel
theorem fusedMap1057_checked : acceptsGraphIso
    (fused (graph core1057) (root 10) 2 2) DegreeTwoThreeSpectrum6093.graph fusedMap1057=true := by decide +kernel
theorem certified1057 : Certified (graph core1057) (root 10) 2 2 :=
  of_native_maps core1057 DegreeOneMiddleResidualSpectrum2008.graph DegreeTwoThreeSpectrum6093.graph
    sourceMap1057 fusedMap1057 sourceMap1057_checked fusedMap1057_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1057
#print axioms sourceMap1057_checked
#print axioms fusedMap1057_checked
#print axioms certified1057
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
