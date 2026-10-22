/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1075 : Family 10 := level10.get ⟨1104,by decide⟩
def sourceMap1075 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1075 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1075_checked : acceptsGraphIso
    (source (graph core1075) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2046.graph sourceMap1075=true := by decide +kernel
theorem fusedMap1075_checked : acceptsGraphIso
    (fused (graph core1075) (root 10) 2 2) DegreeTwoThreeSpectrum6193.graph fusedMap1075=true := by decide +kernel
theorem certified1075 : Certified (graph core1075) (root 10) 2 2 :=
  of_native_maps core1075 DegreeOneMiddleResidualSpectrum2046.graph DegreeTwoThreeSpectrum6193.graph
    sourceMap1075 fusedMap1075 sourceMap1075_checked fusedMap1075_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1075
#print axioms sourceMap1075_checked
#print axioms fusedMap1075_checked
#print axioms certified1075
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
