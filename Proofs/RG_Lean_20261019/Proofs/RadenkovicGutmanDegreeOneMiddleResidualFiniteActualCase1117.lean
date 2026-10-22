/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1117 : Family 10 := level10.get ⟨1245,by decide⟩
def sourceMap1117 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1117 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1117_checked : acceptsGraphIso
    (source (graph core1117) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2147.graph sourceMap1117=true := by decide +kernel
theorem fusedMap1117_checked : acceptsGraphIso
    (fused (graph core1117) (root 10) 2 2) DegreeTwoThreeSpectrum6479.graph fusedMap1117=true := by decide +kernel
theorem certified1117 : Certified (graph core1117) (root 10) 2 2 :=
  of_native_maps core1117 DegreeOneMiddleResidualSpectrum2147.graph DegreeTwoThreeSpectrum6479.graph
    sourceMap1117 fusedMap1117 sourceMap1117_checked fusedMap1117_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1117
#print axioms sourceMap1117_checked
#print axioms fusedMap1117_checked
#print axioms certified1117
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
