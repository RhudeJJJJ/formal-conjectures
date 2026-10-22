/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1047 : Family 10 := level10.get ⟨1034,by decide⟩
def sourceMap1047 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1047 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1047_checked : acceptsGraphIso
    (source (graph core1047) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1991.graph sourceMap1047=true := by decide +kernel
theorem fusedMap1047_checked : acceptsGraphIso
    (fused (graph core1047) (root 10) 2 2) DegreeTwoThreeSpectrum6052.graph fusedMap1047=true := by decide +kernel
theorem certified1047 : Certified (graph core1047) (root 10) 2 2 :=
  of_native_maps core1047 DegreeOneMiddleResidualSpectrum1991.graph DegreeTwoThreeSpectrum6052.graph
    sourceMap1047 fusedMap1047 sourceMap1047_checked fusedMap1047_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1047
#print axioms sourceMap1047_checked
#print axioms fusedMap1047_checked
#print axioms certified1047
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
