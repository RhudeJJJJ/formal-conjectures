/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1124 : Family 10 := level10.get ⟨1259,by decide⟩
def sourceMap1124 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1124 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1124_checked : acceptsGraphIso
    (source (graph core1124) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2159.graph sourceMap1124=true := by decide +kernel
theorem fusedMap1124_checked : acceptsGraphIso
    (fused (graph core1124) (root 10) 2 2) DegreeTwoThreeSpectrum6509.graph fusedMap1124=true := by decide +kernel
theorem certified1124 : Certified (graph core1124) (root 10) 2 2 :=
  of_native_maps core1124 DegreeOneMiddleResidualSpectrum2159.graph DegreeTwoThreeSpectrum6509.graph
    sourceMap1124 fusedMap1124 sourceMap1124_checked fusedMap1124_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1124
#print axioms sourceMap1124_checked
#print axioms fusedMap1124_checked
#print axioms certified1124
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
