/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1151 : Family 10 := level10.get ⟨1352,by decide⟩
def sourceMap1151 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1151 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1151_checked : acceptsGraphIso
    (source (graph core1151) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2226.graph sourceMap1151=true := by decide +kernel
theorem fusedMap1151_checked : acceptsGraphIso
    (fused (graph core1151) (root 10) 2 2) DegreeTwoThreeSpectrum6687.graph fusedMap1151=true := by decide +kernel
theorem certified1151 : Certified (graph core1151) (root 10) 2 2 :=
  of_native_maps core1151 DegreeOneMiddleResidualSpectrum2226.graph DegreeTwoThreeSpectrum6687.graph
    sourceMap1151 fusedMap1151 sourceMap1151_checked fusedMap1151_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1151
#print axioms sourceMap1151_checked
#print axioms fusedMap1151_checked
#print axioms certified1151
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
