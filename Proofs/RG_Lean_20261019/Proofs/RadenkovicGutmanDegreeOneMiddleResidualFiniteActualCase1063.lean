/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1063 : Family 10 := level10.get ⟨1067,by decide⟩
def sourceMap1063 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1063 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1063_checked : acceptsGraphIso
    (source (graph core1063) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2019.graph sourceMap1063=true := by decide +kernel
theorem fusedMap1063_checked : acceptsGraphIso
    (fused (graph core1063) (root 10) 2 2) DegreeTwoThreeSpectrum6123.graph fusedMap1063=true := by decide +kernel
theorem certified1063 : Certified (graph core1063) (root 10) 2 2 :=
  of_native_maps core1063 DegreeOneMiddleResidualSpectrum2019.graph DegreeTwoThreeSpectrum6123.graph
    sourceMap1063 fusedMap1063 sourceMap1063_checked fusedMap1063_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1063
#print axioms sourceMap1063_checked
#print axioms fusedMap1063_checked
#print axioms certified1063
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
