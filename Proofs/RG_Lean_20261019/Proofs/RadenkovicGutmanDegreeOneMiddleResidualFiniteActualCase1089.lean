/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1089 : Family 10 := level10.get ⟨1135,by decide⟩
def sourceMap1089 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1089 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1089_checked : acceptsGraphIso
    (source (graph core1089) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2072.graph sourceMap1089=true := by decide +kernel
theorem fusedMap1089_checked : acceptsGraphIso
    (fused (graph core1089) (root 10) 2 2) DegreeTwoThreeSpectrum6260.graph fusedMap1089=true := by decide +kernel
theorem certified1089 : Certified (graph core1089) (root 10) 2 2 :=
  of_native_maps core1089 DegreeOneMiddleResidualSpectrum2072.graph DegreeTwoThreeSpectrum6260.graph
    sourceMap1089 fusedMap1089 sourceMap1089_checked fusedMap1089_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1089
#print axioms sourceMap1089_checked
#print axioms fusedMap1089_checked
#print axioms certified1089
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
