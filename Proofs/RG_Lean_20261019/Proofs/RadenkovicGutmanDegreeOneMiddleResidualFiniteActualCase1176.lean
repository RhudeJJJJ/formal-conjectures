/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1176 : Family 10 := level10.get ⟨1527,by decide⟩
def sourceMap1176 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1176 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1176_checked : acceptsGraphIso
    (source (graph core1176) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2332.graph sourceMap1176=true := by decide +kernel
theorem fusedMap1176_checked : acceptsGraphIso
    (fused (graph core1176) (root 10) 2 2) DegreeTwoThreeSpectrum5963.graph fusedMap1176=true := by decide +kernel
theorem certified1176 : Certified (graph core1176) (root 10) 2 2 :=
  of_native_maps core1176 DegreeOneMiddleResidualSpectrum2332.graph DegreeTwoThreeSpectrum5963.graph
    sourceMap1176 fusedMap1176 sourceMap1176_checked fusedMap1176_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1176
#print axioms sourceMap1176_checked
#print axioms fusedMap1176_checked
#print axioms certified1176
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
