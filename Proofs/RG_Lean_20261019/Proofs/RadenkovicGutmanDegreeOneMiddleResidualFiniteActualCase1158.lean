/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1158 : Family 10 := level10.get ⟨1405,by decide⟩
def sourceMap1158 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1158 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1158_checked : acceptsGraphIso
    (source (graph core1158) (root 10) 2 2) DegreeTwoThreeSpectrum7475.graph sourceMap1158=true := by decide +kernel
theorem fusedMap1158_checked : acceptsGraphIso
    (fused (graph core1158) (root 10) 2 2) DegreeTwoThreeSpectrum6798.graph fusedMap1158=true := by decide +kernel
theorem certified1158 : Certified (graph core1158) (root 10) 2 2 :=
  of_native_maps core1158 DegreeTwoThreeSpectrum7475.graph DegreeTwoThreeSpectrum6798.graph
    sourceMap1158 fusedMap1158 sourceMap1158_checked fusedMap1158_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1158
#print axioms sourceMap1158_checked
#print axioms fusedMap1158_checked
#print axioms certified1158
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
