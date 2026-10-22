/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1090 : Family 10 := level10.get ⟨1136,by decide⟩
def sourceMap1090 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1090 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1090_checked : acceptsGraphIso
    (source (graph core1090) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2073.graph sourceMap1090=true := by decide +kernel
theorem fusedMap1090_checked : acceptsGraphIso
    (fused (graph core1090) (root 10) 2 2) DegreeTwoThreeSpectrum6261.graph fusedMap1090=true := by decide +kernel
theorem certified1090 : Certified (graph core1090) (root 10) 2 2 :=
  of_native_maps core1090 DegreeOneMiddleResidualSpectrum2073.graph DegreeTwoThreeSpectrum6261.graph
    sourceMap1090 fusedMap1090 sourceMap1090_checked fusedMap1090_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1090
#print axioms sourceMap1090_checked
#print axioms fusedMap1090_checked
#print axioms certified1090
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
