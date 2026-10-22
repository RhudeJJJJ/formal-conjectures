/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1052 : Family 10 := level10.get ⟨1041,by decide⟩
def sourceMap1052 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1052 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1052_checked : acceptsGraphIso
    (source (graph core1052) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1998.graph sourceMap1052=true := by decide +kernel
theorem fusedMap1052_checked : acceptsGraphIso
    (fused (graph core1052) (root 10) 2 2) DegreeTwoThreeSpectrum6066.graph fusedMap1052=true := by decide +kernel
theorem certified1052 : Certified (graph core1052) (root 10) 2 2 :=
  of_native_maps core1052 DegreeOneMiddleResidualSpectrum1998.graph DegreeTwoThreeSpectrum6066.graph
    sourceMap1052 fusedMap1052 sourceMap1052_checked fusedMap1052_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1052
#print axioms sourceMap1052_checked
#print axioms fusedMap1052_checked
#print axioms certified1052
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
