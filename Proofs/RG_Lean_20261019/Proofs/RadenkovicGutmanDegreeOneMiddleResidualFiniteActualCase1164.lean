/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1164 : Family 10 := level10.get ⟨1420,by decide⟩
def sourceMap1164 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1164 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1164_checked : acceptsGraphIso
    (source (graph core1164) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2270.graph sourceMap1164=true := by decide +kernel
theorem fusedMap1164_checked : acceptsGraphIso
    (fused (graph core1164) (root 10) 2 2) DegreeTwoThreeSpectrum6873.graph fusedMap1164=true := by decide +kernel
theorem certified1164 : Certified (graph core1164) (root 10) 2 2 :=
  of_native_maps core1164 DegreeOneMiddleResidualSpectrum2270.graph DegreeTwoThreeSpectrum6873.graph
    sourceMap1164 fusedMap1164 sourceMap1164_checked fusedMap1164_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1164
#print axioms sourceMap1164_checked
#print axioms fusedMap1164_checked
#print axioms certified1164
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
