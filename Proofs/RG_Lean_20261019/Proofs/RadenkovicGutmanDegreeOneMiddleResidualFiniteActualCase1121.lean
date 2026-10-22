/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1121 : Family 10 := level10.get ⟨1253,by decide⟩
def sourceMap1121 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1121 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1121_checked : acceptsGraphIso
    (source (graph core1121) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2154.graph sourceMap1121=true := by decide +kernel
theorem fusedMap1121_checked : acceptsGraphIso
    (fused (graph core1121) (root 10) 2 2) DegreeTwoThreeSpectrum6496.graph fusedMap1121=true := by decide +kernel
theorem certified1121 : Certified (graph core1121) (root 10) 2 2 :=
  of_native_maps core1121 DegreeOneMiddleResidualSpectrum2154.graph DegreeTwoThreeSpectrum6496.graph
    sourceMap1121 fusedMap1121 sourceMap1121_checked fusedMap1121_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1121
#print axioms sourceMap1121_checked
#print axioms fusedMap1121_checked
#print axioms certified1121
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
