/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1072 : Family 10 := level10.get ⟨1098,by decide⟩
def sourceMap1072 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1072 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1072_checked : acceptsGraphIso
    (source (graph core1072) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2041.graph sourceMap1072=true := by decide +kernel
theorem fusedMap1072_checked : acceptsGraphIso
    (fused (graph core1072) (root 10) 2 2) DegreeTwoThreeSpectrum6182.graph fusedMap1072=true := by decide +kernel
theorem certified1072 : Certified (graph core1072) (root 10) 2 2 :=
  of_native_maps core1072 DegreeOneMiddleResidualSpectrum2041.graph DegreeTwoThreeSpectrum6182.graph
    sourceMap1072 fusedMap1072 sourceMap1072_checked fusedMap1072_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1072
#print axioms sourceMap1072_checked
#print axioms fusedMap1072_checked
#print axioms certified1072
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
