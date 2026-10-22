/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1178 : Family 10 := level10.get ⟨1532,by decide⟩
def sourceMap1178 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1178 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1178_checked : acceptsGraphIso
    (source (graph core1178) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2334.graph sourceMap1178=true := by decide +kernel
theorem fusedMap1178_checked : acceptsGraphIso
    (fused (graph core1178) (root 10) 2 2) DegreeTwoThreeSpectrum5972.graph fusedMap1178=true := by decide +kernel
theorem certified1178 : Certified (graph core1178) (root 10) 2 2 :=
  of_native_maps core1178 DegreeOneMiddleResidualSpectrum2334.graph DegreeTwoThreeSpectrum5972.graph
    sourceMap1178 fusedMap1178 sourceMap1178_checked fusedMap1178_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1178
#print axioms sourceMap1178_checked
#print axioms fusedMap1178_checked
#print axioms certified1178
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
